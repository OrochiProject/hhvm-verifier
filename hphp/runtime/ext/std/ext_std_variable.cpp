/*
   +----------------------------------------------------------------------+
   | HipHop for PHP                                                       |
   +----------------------------------------------------------------------+
   | Copyright (c) 2010-2014 Facebook, Inc. (http://www.facebook.com)     |
   | Copyright (c) 1997-2010 The PHP Group                                |
   +----------------------------------------------------------------------+
   | This source file is subject to version 3.01 of the PHP license,      |
   | that is bundled with this package in the file LICENSE, and is        |
   | available through the world-wide-web at the following url:           |
   | http://www.php.net/license/3_01.txt                                  |
   | If you did not receive a copy of the PHP license and are unable to   |
   | obtain it through the world-wide-web, please send a note to          |
   | license@php.net so we can mail you a copy immediately.               |
   +----------------------------------------------------------------------+
*/
#include "hphp/runtime/ext/std/ext_std_variable.h"

#include <folly/Likely.h>

#include "hphp/util/logger.h"
#include "hphp/runtime/base/variable-serializer.h"
#include "hphp/runtime/base/variable-unserializer.h"
#include "hphp/runtime/base/builtin-functions.h"
#include "hphp/runtime/base/zend-functions.h"
#include "hphp/runtime/vm/jit/translator-inline.h"
#include "hphp/runtime/server/http-protocol.h"

#include "hphp/runtime/base/multi-val.h"
#include "hphp/runtime/ext/std/sql-parser.h"
#include "hphp/runtime/vm/yastopwatch.h"

#include "fstream"
#include "vector"

namespace HPHP {
///////////////////////////////////////////////////////////////////////////////


const StaticString
  s_unknown_type("unknown type"),
  s_boolean("boolean"),
  s_bool("bool"),
  s_integer("integer"),
  s_int("int"),
  s_float("float"),
  s_double("double"),
  s_string("string"),
  s_object("object"),
  s_array("array"),
  s_null("null");

String HHVM_FUNCTION(gettype, const Variant& v) {
  if (v.getType() == KindOfResource && v.getResourceData()->isInvalid()) {
    return s_unknown_type;
  }
  return getDataTypeString(v.getType());
}

String HHVM_FUNCTION(get_resource_type, const Resource& handle) {
  return handle->o_getResourceName();
}

bool HHVM_FUNCTION(boolval, const Variant& v) {
  return v.toBoolean();
}

int64_t HHVM_FUNCTION(intval, const Variant& v, int64_t base /* = 10 */) {
  return v.toInt64(base);
}

double HHVM_FUNCTION(floatval, const Variant& v) {
  return v.toDouble();
}

String HHVM_FUNCTION(strval, const Variant& v) {
  return v.toString();
}

bool HHVM_FUNCTION(settype, VRefParam var, const String& type) {
  if      (type == s_boolean) var = var.toBoolean();
  else if (type == s_bool   ) var = var.toBoolean();
  else if (type == s_integer) var = var.toInt64();
  else if (type == s_int    ) var = var.toInt64();
  else if (type == s_float  ) var = var.toDouble();
  else if (type == s_double ) var = var.toDouble();
  else if (type == s_string ) var = var.toString();
  else if (type == s_array  ) var = var.toArray();
  else if (type == s_object ) var = var.toObject();
  else if (type == s_null   ) var = uninit_null();
  else return false;
  return true;
}

bool HHVM_FUNCTION(is_null, const Variant& v) {
  return is_null(v);
}

bool HHVM_FUNCTION(is_bool, const Variant& v) {
  return is_bool(v);
}

bool HHVM_FUNCTION(is_int, const Variant& v) {
  return is_int(v);
}

bool HHVM_FUNCTION(is_float, const Variant& v) {
  return is_double(v);
}

bool HHVM_FUNCTION(is_numeric, const Variant& v) {
  return v.isNumeric(true);
}

bool HHVM_FUNCTION(is_string, const Variant& v) {
  return is_string(v);
}

bool HHVM_FUNCTION(is_scalar, const Variant& v) {
  return v.isScalar();
}

bool HHVM_FUNCTION(is_array, const Variant& v) {
  return is_array(v);
}

bool HHVM_FUNCTION(is_object, const Variant& v) {
  return is_object(v);
}

bool HHVM_FUNCTION(is_resource, const Variant& v) {
  return (v.getType() == KindOfResource && !v.getResourceData()->isInvalid());
}

///////////////////////////////////////////////////////////////////////////////
// cheng-hack: Multi-value APIs

extern bool should_count;
void HHVM_FUNCTION(set_should_count, bool count) {
  should_count = count;
}

static Variant
makeMultiVal(int size=0) {
  Variant v;
  v.m_type = KindOfMulti;
  v.m_data.pmulti = new MultiVal(size); 
  return v;
}

extern thread_local bool loop_capture_mode;
extern thread_local std::vector<TypedValue> finish_loop_var;
extern thread_local std::vector<TypedValue> finish_capture_var;
extern thread_local std::vector<int> loop_alive;
extern thread_local TypedValue origin_loop_var_ref;
extern thread_local TypedValue origin_capture_var_ref;

void HHVM_FUNCTION(loop_var_capture, VRefParam loop_var_ref, VRefParam capture_var_ref, int64_t size) {
  loop_capture_mode = true;

  // initialize the ds
  TypedValue uninit_tv;
  uninit_tv.m_type = KindOfUninit;

  loop_alive.resize(size);
  finish_loop_var.resize(size);
  finish_capture_var.resize(size);

  for(int i=0; i<size; i++) {
    loop_alive[i] = 1;
    finish_loop_var[i] = uninit_tv;
    finish_capture_var[i] = uninit_tv;
  }

  // copy the ref 
  refDup(loop_var_ref.wrapped(), origin_loop_var_ref);

  // FIXME: obj may have side-effect after the capture end
  // we do not earse the element from capture_var after its end
  cheng_assert(capture_var_ref.wrapped().m_type != KindOfObject);
  // point to the same MultiVal object
  refDup(capture_var_ref.wrapped(), origin_capture_var_ref);
}

void HHVM_FUNCTION(loop_var_end, VRefParam loop_var_ref, VRefParam capture_var_ref) {
  cheng_assert(loop_var_ref.isReferenced());
  cheng_assert(capture_var_ref.isReferenced());

  // check if in capture mode
  if (loop_capture_mode) {
    // check: loop_alive should be all zero
    for (auto it : loop_alive) {
      cheng_assert(it == 0);
    }
    // check: finished loop and capture should be full 
    for (int i=0; i<finish_loop_var.size(); i++) {
      cheng_assert(finish_loop_var[i].m_type != KindOfUninit);
      cheng_assert(finish_capture_var[i].m_type != KindOfUninit);
    }

    int size = finish_loop_var.size();

    auto ret_loop_var = makeMultiVal();
    auto ret_capture_var = makeMultiVal();
    // recover the correct result from finish_loop_var/finish_capture_var
    for (int i=0; i<size; i++) {
      ret_loop_var.m_data.pmulti->addValue(finish_loop_var[i]);
      ret_capture_var.m_data.pmulti->addValue(finish_capture_var[i]);
    }
    
    // put the result back to program
    ret_loop_var.m_data.pmulti->valid();
    ret_capture_var.m_data.pmulti->valid();
    
    // shrink and assign the output
    auto single = ret_loop_var.m_data.pmulti->shrinkToSingle();
    if (single == nullptr) {
      loop_var_ref = tvAsVariant(&ret_loop_var);
    } else {
      loop_var_ref = tvAsVariant(single);
    }

    single = ret_capture_var.m_data.pmulti->shrinkToSingle();
    if (single == nullptr) {
      capture_var_ref = tvAsVariant(&ret_capture_var);
    } else {
      capture_var_ref = tvAsVariant(single);
    }

    loop_capture_mode = false;
  }
}

// cheng-hack:
extern thread_local bool is_resource_req; 
bool HHVM_FUNCTION(is_res_req) {
  return is_resource_req;
}

void HHVM_FUNCTION(set_res_req, bool is_res) {
  is_resource_req = is_res;
}

// cheng-hack: set the batch_size
extern thread_local int batch_size; 
int HHVM_FUNCTION(get_batch_size) {
  return batch_size;
}

void HHVM_FUNCTION(set_batch_size, int size) {
  batch_size = size;
}

// cheng-hack: the instruction related profiling 

extern thread_local int ins_counter;
extern thread_local int64_t multi_ins_counter;
int HHVM_FUNCTION(get_ins_counter) {
  return ins_counter;
}

int HHVM_FUNCTION(get_multi_ins_counter) {
  return multi_ins_counter;
}

extern thread_local int oparr_ins_counter;
extern thread_local int oparith_ins_counter;
extern thread_local int opcf_ins_counter;
extern thread_local int opget_ins_counter;
extern thread_local int opset_ins_counter;
extern thread_local int opisset_ins_counter;
extern thread_local int opcall_ins_counter;
extern thread_local int opmember_ins_counter;
extern thread_local int opiter_ins_counter;
extern thread_local int opmisc_ins_counter;
// defined later
static inline ArrayData* SetNewElemArray(ArrayData* a, TypedValue* value);

Variant HHVM_FUNCTION(get_classified_ins_counter) {
  // return an array
  ArrayData* array = staticEmptyArray();
  array = SetNewElemArray(array, Variant(oparr_ins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(oparith_ins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opcf_ins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opget_ins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opset_ins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opisset_ins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opcall_ins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opmember_ins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opiter_ins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opmisc_ins_counter).asTypedValue());
  return array;
}

extern thread_local int oparr_mins_counter;
extern thread_local int oparith_mins_counter;
extern thread_local int opcf_mins_counter;
extern thread_local int opget_mins_counter;
extern thread_local int opset_mins_counter;
extern thread_local int opisset_mins_counter;
extern thread_local int opcall_mins_counter;
extern thread_local int opmember_mins_counter;
extern thread_local int opiter_mins_counter;
extern thread_local int opmisc_mins_counter;

Variant HHVM_FUNCTION(get_classified_mins_counter) {
  // return an array
  ArrayData* array = staticEmptyArray();
  array = SetNewElemArray(array, Variant(oparr_mins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(oparith_mins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opcf_mins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opget_mins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opset_mins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opisset_mins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opcall_mins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opmember_mins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opiter_mins_counter).asTypedValue());
  array = SetNewElemArray(array, Variant(opmisc_mins_counter).asTypedValue());
  return array;
}

extern bool cheng_verification;
extern thread_local std::stringstream veri_buf;
void HHVM_FUNCTION(replay_dump_output, const Variant& v) {
  if (is_resource_req) return;
  if (cheng_verification) {


    // If there are other contents within ob buffer, append to the
    // veri_buf output
    if (g_context->obGetContentLength() != 0) {
      auto content = g_context->obCopyContents();
      veri_buf << content.toCppString();
    }

    std::ofstream of;
    of.open(v.toCStrRef().toCppString());
    of << veri_buf.str();
    of.close();
  }
}

void HHVM_FUNCTION(veri_dump_output, const Variant& path, const Variant& req_no) {
  always_assert(req_no.m_type == KindOfMulti);
  if (is_resource_req) return;
  if (cheng_verification) {

    if (veri_buf.str() == "") {
      // FIXME:
      if (g_context->m_isMultiObs) {
        g_context->multiObFlushAll();
      }
      auto content = g_context->obCopyContents();
      veri_buf << content.toCppString();
    }

    std::ofstream of;
    of.open(path.toCStrRef().toCppString());
    // first write the batched request id 
    of << "[";
    for (auto it : *req_no.m_data.pmulti) {
      of << it->m_data.num << ",";
    }
    of << "]\n";
    of << veri_buf.str();
    of.close();
  }
}

bool HHVM_FUNCTION(is_verify) {
  return cheng_verification;
}

// cheng-hack: session thing
extern std::string _sess_get_last_write(int64_t rid, int64_t opnum, std::string sess_id);
extern std::string _sess_get_id(int64_t rid, int64_t opnum, bool check);

Variant HHVM_FUNCTION(sess_get_last_write, const int64_t rid, const int64_t opnum, const Variant& sess_id) {
  std::string sid = std::string(sess_id.toString().data());
  return _sess_get_last_write(rid, opnum, sid); 
}

Variant HHVM_FUNCTION(sess_get_id, const int64_t rid, const int64_t opnum, bool check) {
  return _sess_get_id(rid, opnum, check); 
}

Variant HHVM_FUNCTION(add_multi, Variant var, Variant value, int64_t req_num) {
  if (var.m_type == KindOfMulti) {
    MultiVal* mv = var.getMultiVal();
    mv->addValue(value);
  } else if (var.m_type == KindOfNull || var.m_type == KindOfUninit) {
    var = makeMultiVal();
    var.getMultiVal()->addValue(value);
  } else {
    std::cout << "ERROR: Cannot add a value to a non-multi-value variable!\n";
    always_assert(false);
  }
  return var;
}


// for break-even eval
extern void set_batch_upperbound(int64_t bound);
extern int64_t get_batch_upperbound();

void HHVM_FUNCTION(set_batch_upper_bound, int64_t size) {
  set_batch_upperbound(size);
}

// The inputs is an array of values with same type
Variant HHVM_FUNCTION(gen_multi, const Array& arr) {
  auto multi_ret = makeMultiVal();

  bool first = true;
  DataType type;
  int64_t batch_size = 0;
  for (ArrayIter iter(arr); iter; ++iter) {
    if (first) {
      type = iter.nvSecond()->m_type;
      first = false;
    }
    cheng_assert( (type == iter.nvSecond()->m_type) ||
                  (type == KindOfInt64 && iter.nvSecond()->m_type == KindOfDouble) ||
                  (type == KindOfDouble && iter.nvSecond()->m_type == KindOfInt64) );

    multi_ret.m_data.pmulti->addValue(*iter.nvSecond());

    // NOTE: we do batch_upperbound check here
    // This should only be used for break-even eval
    if (++batch_size >= get_batch_upperbound()) break;
  }

  return multi_ret;
}

bool HHVM_FUNCTION(is_multi, const Variant& value) {
  if (value.m_type == KindOfMulti) {
    return true;
  } else {
    return (MultiVal::containMultiVal((TypedValue*)value.asTypedValue()) != 0);
  }
}

/**
 * cheng: Borrow from member-operations.h
 * SetNewElem when base is an Array
 */
static inline ArrayData* SetNewElemArray(ArrayData* a, TypedValue* value) {
  //ArrayData* a = base->m_data.parr;
  bool copy = (a->hasMultipleRefs())
    || (value->m_type == KindOfArray && value->m_data.parr == a);
  ArrayData* a2 = a->append(cellAsCVarRef(*value), copy);
  if (a2 != a) {
    a2->incRefCount();
    a->decRefAndRelease();
  }
  return a2;
}

Variant HHVM_FUNCTION(split_multi, const Variant& value) {
  always_assert(value.m_type == KindOfMulti);

  ArrayData* array = staticEmptyArray();
  int req_num = value.m_data.pmulti->valSize();
  for (int i = 0; i < req_num; i++) {
    auto it = value.m_data.pmulti->getByVal(i);
    array = SetNewElemArray(array, it);
  }
  return array;
}

Variant HHVM_FUNCTION(getIthVal, const Variant& value, int64_t i) {
  cheng_assert(value.m_type == KindOfMulti || MultiVal::containMultiVal((TypedValue*)value.asTypedValue())!=0);
  auto tv = MultiVal::selectIthVal(value, i);
  return tvAsVariant(&tv);
}

Variant HHVM_FUNCTION(merge_multi, const Variant& value) {
  if (value.m_type == KindOfMulti) {
    TypedValue *shrink = value.m_data.pmulti->shrinkToSingle();
    if (shrink == nullptr) {
      return value;
    }
    return tvAsVariant(shrink);
  } else {
    // FIXME: can be MIC
    return value; 
  }
}

//==============================



extern struct __stopwatch__ __SW(db_trans_time);
extern enum __stopwatch__source__ __SOURCE(db_trans_time); 
extern enum __stopwatch__type__ __TYPE(db_trans_time);

// cheng-hack:
#define MAX_IN_TXN 10000
// defined in bytecode.cpp
extern int search_opmap(int rid, int opnum, int type);

Variant HHVM_FUNCTION(rewrite_select_sql, const Variant& sql, int64_t rid, int64_t opnum, int64_t query_num) {
  always_assert(sql.m_type == KindOfStaticString || sql.m_type == KindOfString);
  
  std::string str_sql = std::string(sql.toString().data());
  int64_t seqnum = search_opmap(rid, opnum, SQL_READ); 
  int64_t timestamp = seqnum * MAX_IN_TXN + query_num; 
  START_SW(db_trans_time);
  std::string ret = rewriteOptSelect(str_sql, timestamp);
  STOP_SW(db_trans_time);
  return Variant(ret);
}

Variant HHVM_FUNCTION(MC_to_MIC, const Variant& multi) {
  always_assert(multi.m_type == KindOfMulti);
  
  TypedValue ret;
  if (multi.m_data.pmulti->getType() == KindOfArray) {
    ret = MultiVal::invertTransferArray(multi); 
  } else if (multi.m_data.pmulti->getType() == KindOfObject) {
    ret = MultiVal::invertTransferObj(multi);
  } else {
    always_assert(false);
  }
  return tvAsVariant(&ret);
}

bool HHVM_FUNCTION(check_write_sql, const Variant& sql, int64_t rid, int64_t opnum) {
  search_opmap(rid, opnum, SQL_WRITE);
  return true;
}

int HHVM_FUNCTION(get_seqnum_from_opmap, int64_t rid, int64_t opnum) {
  // ignore the type check, we just want to know the seqnum
  return search_opmap(rid, opnum, TYPE_NONE);
}


extern thread_local bool single_mode_on; 
bool HHVM_FUNCTION(is_single_mode_on) {
  return single_mode_on;
}

Variant HHVM_FUNCTION(MIC_to_MC, const Variant& container) {
  always_assert(container.m_type == KindOfArray || container.m_type == KindOfObject);
  always_assert(MultiVal::containMultiVal((TypedValue*)container.asTypedValue()) != 0);

  TypedValue ret;
  if (container.m_type == KindOfArray) {
    ret = MultiVal::transferArray(container);
  } else {
    ret = MultiVal::transferObj(container);
  }
  return tvAsVariant(&ret);
}

extern bool check_maxop(int rid,  int last_op_num);
bool HHVM_FUNCTION(check_maxop, int64_t rid, int64_t last_op_num) {
  return check_maxop(rid, last_op_num);
}

///////////////////////////////////////////////////////////////////////////////
// input/output
// cheng-hack:
Variant HHVM_FUNCTION(print_p, const Variant& expression) {
  return MultiVal::dumpElem((TypedValue*)expression.asTypedValue());
  //auto pretty = expression.pretty();
  //auto isMulti = MultiVal::containMultiVal((TypedValue*)expression.asTypedValue());
  //std::stringstream ss;
  //ss << "[" << isMulti << "] " << pretty;
  //if (expression.m_type == KindOfMulti) {
  //  ss << " type: " << expression.m_data.pmulti->getType();
  //}
  //return ss.str();
}

Variant HHVM_FUNCTION(print_r, const Variant& expression,
                               bool ret /* = false */) {
  Variant res;
  try {
    VariableSerializer vs(VariableSerializer::Type::PrintR);
    if (ret) {
      res = vs.serialize(expression, ret);
    } else {
      vs.serialize(expression, ret);
      res = true;
    }
  } catch (StringBufferLimitException &e) {
    raise_notice("print_r() exceeded max bytes limit");
    res = e.m_result;
  }
  return res;
}

Variant HHVM_FUNCTION(var_export, const Variant& expression,
                                  bool ret /* = false */) {
  Variant res;
  try {
    VariableSerializer vs(VariableSerializer::Type::VarExport);
    if (ret) {
      res = vs.serialize(expression, ret);
    } else {
      vs.serialize(expression, ret);
      res = true;
    }
  } catch (StringBufferLimitException &e) {
    raise_notice("var_export() exceeded max bytes limit");
  }
  return res;
}

static ALWAYS_INLINE void do_var_dump(VariableSerializer vs,
                                      const Variant& expression) {
  // manipulate maxCount to match PHP behavior
  if (!expression.isObject()) {
    vs.incMaxCount();
  }
  vs.serialize(expression, false);
}

void HHVM_FUNCTION(var_dump, const Variant& expression,
                             const Array& _argv /*=null_array */) {
  VariableSerializer vs(VariableSerializer::Type::VarDump, 0, 2);
  do_var_dump(vs, expression);

  auto sz = _argv.size();
  for (int i = 0; i < sz; i++) {
    do_var_dump(vs, _argv[i]);
  }
}

void HHVM_FUNCTION(debug_zval_dump, const Variant& variable) {
  VariableSerializer vs(VariableSerializer::Type::DebugDump);
  vs.serialize(variable, false);
}

String HHVM_FUNCTION(serialize, const Variant& value) {
  switch (value.getType()) {
    case KindOfUninit:
    case KindOfNull:
      return "N;";
    case KindOfBoolean:
      return value.getBoolean() ? "b:1;" : "b:0;";
    case KindOfInt64: {
      StringBuffer sb;
      sb.append("i:");
      sb.append(value.getInt64());
      sb.append(';');
      return sb.detach();
    }
    case KindOfStaticString:
    case KindOfString: {
      StringData *str = value.getStringData();
      StringBuffer sb;
      sb.append("s:");
      sb.append(str->size());
      sb.append(":\"");
      sb.append(str->data(), str->size());
      sb.append("\";");
      return sb.detach();
    }
    case KindOfResource:
      return "i:0;";
    case KindOfArray: {
      ArrayData *arr = value.getArrayData();
      if (arr->empty()) return "a:0:{}";
      // fall-through
    }
    case KindOfDouble:
    case KindOfObject: {
      VariableSerializer vs(VariableSerializer::Type::Serialize);
      return vs.serialize(value, true);
    }
    case KindOfRef:
    case KindOfMulti:
    case KindOfClass:
      break;
  }
  not_reached();
}

Variant HHVM_FUNCTION(unserialize, const String& str,
                                   const Array& class_whitelist /* =[] */) {
  return unserialize_from_string(str, class_whitelist);
}

///////////////////////////////////////////////////////////////////////////////
// variable table

ALWAYS_INLINE
static Array get_defined_vars() {
  VarEnv* v = g_context->getVarEnv();
  return v ? v->getDefinedVariables() : empty_array();
}

Array HHVM_FUNCTION(get_defined_vars) {
  raise_disallowed_dynamic_call("extract should not be called dynamically");
  return get_defined_vars();
}

// accessible as __SystemLib\\get_defined_vars
Array HHVM_FUNCTION(SystemLib_get_defined_vars) {
  return get_defined_vars();
}

const StaticString
  s_GLOBALS("GLOBALS"),
  s_this("this");

static const Func* arGetContextFunc(const ActRec* ar) {
  if (ar == nullptr) {
    return nullptr;
  }
  if (ar->m_func->isPseudoMain() || ar->m_func->isBuiltin()) {
    // Pseudomains inherit the context of their caller
    auto const context = g_context.getNoCheck();
    ar = context->getPrevVMStateUNSAFE(ar);
    while (ar != nullptr &&
             (ar->m_func->isPseudoMain() || ar->m_func->isBuiltin())) {
      ar = context->getPrevVMStateUNSAFE(ar);
    }
    if (ar == nullptr) {
      return nullptr;
    }
  }
  return ar->m_func;
}

static bool modify_extract_name(VarEnv* v,
                                String& name,
                                int64_t extract_type,
                                const String& prefix) {
  switch (extract_type) {
  case EXTR_SKIP:
    if (v->lookup(name.get()) != nullptr) {
      return false;
    }
    break;
  case EXTR_IF_EXISTS:
    if (v->lookup(name.get()) == nullptr) {
      return false;
    } else {
      goto namechecks;
    }
    break;
  case EXTR_PREFIX_SAME:
    if (v->lookup(name.get()) != nullptr) {
      name = prefix + "_" + name;
    } else {
      goto namechecks;
    }
    break;
  case EXTR_PREFIX_ALL:
    name = prefix + "_" + name;
    break;
  case EXTR_PREFIX_INVALID:
    if (!is_valid_var_name(name.get()->data(), name.size())) {
      name = prefix + "_" + name;
    } else {
      goto namechecks;
    }
    break;
  case EXTR_PREFIX_IF_EXISTS:
    if (v->lookup(name.get()) == nullptr) {
      return false;
    }
    name = prefix + "_" + name;
    break;
  case EXTR_OVERWRITE:
    namechecks:
    if (name == s_GLOBALS) {
      return false;
    }
    if (name == s_this) {
      // Only disallow $this when inside a non-static method, or a static method
      // that has defined $this (matches Zend)
      CallerFrame cf;
      const Func* func = arGetContextFunc(cf());

      if (func && func->isMethod() && v->lookup(s_this.get()) != nullptr) {
        return false;
      }
    }
  default:
    break;
  }

  // skip invalid variable names, as in PHP
  return is_valid_var_name(name.get()->data(), name.size());
}

ALWAYS_INLINE static
int64_t extract_impl(VRefParam vref_array,
                     int extract_type /* = EXTR_OVERWRITE */,
                     const String& prefix /* = "" */) {
  bool reference = extract_type & EXTR_REFS;
  extract_type &= ~EXTR_REFS;

  // cheng-hack:
  if (tvToCell(vref_array.wrapped().asTypedValue())->m_type == KindOfMulti) {
    auto arr = tvToCell(vref_array.wrapped().asTypedValue());
    cheng_assert(arr->m_data.pmulti->getType() == KindOfArray);
    // TODO: only support SKIP/OVERWRITE
    cheng_assert(!reference);

    VMRegAnchor _;
    auto const varEnv = g_context->getVarEnv();
    if (!varEnv) return 0;

    auto new_arr = MultiVal::invertTransferArray(*arr);
    auto var_array = new_arr.m_data.parr;
    int count = 0;
    for (ArrayIter iter(var_array); iter; ++iter) {
      String name = iter.first();
      if (!modify_extract_name(varEnv, name, extract_type, prefix)) continue;
      g_context->setVar(name.get(), iter.secondRef().asTypedValue());
      ++count;
    }
    return count;
  }

  if (!vref_array.wrapped().isArray()) {
    raise_warning("extract() expects parameter 1 to be array");
    return 0;
  }

  VMRegAnchor _;
  auto const varEnv = g_context->getVarEnv();
  if (!varEnv) return 0;

  if (UNLIKELY(reference)) {
    auto& arr = vref_array.wrapped().toArrRef();
    int count = 0;
    for (ArrayIter iter(arr); iter; ++iter) {
      String name = iter.first();
      if (!modify_extract_name(varEnv, name, extract_type, prefix)) continue;
      g_context->bindVar(name.get(), arr.lvalAt(name).asTypedValue());
      ++count;
    }
    return count;
  }

  auto const var_array = vref_array.wrapped().toArray();
  int count = 0;
  for (ArrayIter iter(var_array); iter; ++iter) {
    String name = iter.first();
    if (!modify_extract_name(varEnv, name, extract_type, prefix)) continue;
    g_context->setVar(name.get(), iter.secondRef().asTypedValue());
    ++count;
  }
  return count;
}

int64_t HHVM_FUNCTION(extract, VRefParam vref_array,
                      int64_t extract_type /* = EXTR_OVERWRITE */,
                      const String& prefix /* = "" */) {
  raise_disallowed_dynamic_call("extract should not be called dynamically");
  return extract_impl(vref_array, extract_type, prefix);
}

int64_t HHVM_FUNCTION(SystemLib_extract,
                      VRefParam vref_array,
                      int64_t extract_type = EXTR_OVERWRITE,
                      const String& prefix = "") {
  return extract_impl(vref_array, extract_type, prefix);
}

static void parse_str_impl(const String& str, VRefParam arr) {
  Array result = Array::Create();
  HttpProtocol::DecodeParameters(result, str.data(), str.size());
  if (!arr.isReferenced()) {
    HHVM_FN(SystemLib_extract)(result);
    return;
  }
  arr = result;
}

void HHVM_FUNCTION(parse_str,
                   const String& str,
                   VRefParam arr /* = null */) {
  raise_disallowed_dynamic_call("parse_str should not be called dynamically");
  parse_str_impl(str, arr);
}

void HHVM_FUNCTION(SystemLib_parse_str,
                   const String& str,
                   VRefParam arr /* = null */) {
  parse_str_impl(str, arr);
}

/////////////////////////////////////////////////////////////////////////////

#define EXTR_CONST(v) Native::registerConstant<KindOfInt64> \
                                   (makeStaticString("EXTR_" #v), EXTR_##v);

void StandardExtension::initVariable() {
  EXTR_CONST(IF_EXISTS);
  EXTR_CONST(OVERWRITE);
  EXTR_CONST(PREFIX_ALL);
  EXTR_CONST(PREFIX_IF_EXISTS);
  EXTR_CONST(PREFIX_INVALID);
  EXTR_CONST(PREFIX_SAME);
  EXTR_CONST(REFS);
  EXTR_CONST(SKIP);

  HHVM_FE(is_null);
  HHVM_FE(is_bool);
  HHVM_FE(is_int);
  HHVM_FALIAS(is_integer, is_int);
  HHVM_FALIAS(is_long, is_int);
  HHVM_FE(is_float);
  HHVM_FALIAS(is_double, is_float);
  HHVM_FALIAS(is_real, is_float);
  HHVM_FE(is_numeric);
  HHVM_FE(is_string);
  HHVM_FE(is_scalar);
  HHVM_FE(is_array);
  HHVM_FE(is_object);
  HHVM_FE(is_resource);
  HHVM_FE(add_multi);    // cheng-hack
  HHVM_FE(gen_multi);    // cheng-hack
  HHVM_FE(set_batch_upper_bound);    // cheng-hack
  HHVM_FE(is_multi);     // cheng-hack
  HHVM_FE(split_multi);  // cheng-hack
  HHVM_FE(getIthVal);  // cheng-hack
  HHVM_FE(merge_multi);  // cheng-hack
  HHVM_FE(rewrite_select_sql);  // cheng-hack
  HHVM_FE(check_write_sql);  // cheng-hack
  HHVM_FE(get_seqnum_from_opmap);  // cheng-hack
  HHVM_FE(is_verify);  // cheng-hack
  HHVM_FE(is_single_mode_on);  // cheng-hack
  HHVM_FE(is_res_req);  // cheng-hack
  HHVM_FE(set_res_req);  // cheng-hack
  HHVM_FE(get_batch_size);  // cheng-hack
  HHVM_FE(set_batch_size);  // cheng-hack
  HHVM_FE(get_ins_counter);  // cheng-hack
  HHVM_FE(get_multi_ins_counter);  // cheng-hack
  HHVM_FE(get_classified_ins_counter);  // cheng-hack
  HHVM_FE(get_classified_mins_counter);  // cheng-hack
  HHVM_FE(set_should_count);  // cheng-hack
  HHVM_FE(replay_dump_output);  // cheng-hack
  HHVM_FE(veri_dump_output);  // cheng-hack
  HHVM_FE(loop_var_capture);  // cheng-hack
  HHVM_FE(loop_var_end);  // cheng-hack
  HHVM_FE(MIC_to_MC);  // cheng-hack
  HHVM_FE(MC_to_MIC);  // cheng-hack
  HHVM_FE(check_maxop);  // cheng-hack
  HHVM_FE(sess_get_last_write);  // cheng-hack
  HHVM_FE(sess_get_id);  // cheng-hack
  HHVM_FE(boolval);
  HHVM_FE(intval);
  HHVM_FE(floatval);
  HHVM_FALIAS(doubleval, floatval);
  HHVM_FE(strval);
  HHVM_FE(gettype);
  HHVM_FE(get_resource_type);
  HHVM_FE(settype);
  HHVM_FE(print_r);
  HHVM_FE(print_p); // cheng-hack
  HHVM_FE(var_export);
  HHVM_FE(debug_zval_dump);
  HHVM_FE(var_dump);
  HHVM_FE(serialize);
  HHVM_FE(unserialize);
  HHVM_FE(get_defined_vars);
  HHVM_FALIAS(__SystemLib\\get_defined_vars, SystemLib_get_defined_vars);
  HHVM_FE(extract);
  HHVM_FE(parse_str);
  HHVM_FALIAS(__SystemLib\\extract, SystemLib_extract);
  HHVM_FALIAS(__SystemLib\\parse_str, SystemLib_parse_str);

  loadSystemlib("std_variable");
}

///////////////////////////////////////////////////////////////////////////////
} // namespace HPHP
