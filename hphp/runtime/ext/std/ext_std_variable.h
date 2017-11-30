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

#ifndef incl_HPHP_VARIABLE_H_
#define incl_HPHP_VARIABLE_H_

#include "hphp/runtime/ext/std/ext_std.h"

namespace HPHP {
///////////////////////////////////////////////////////////////////////////////
// type testing

bool HHVM_FUNCTION(is_bool, const Variant& v);
bool HHVM_FUNCTION(is_int, const Variant& v);
bool HHVM_FUNCTION(is_float, const Variant& v);
bool HHVM_FUNCTION(is_numeric, const Variant& v);
bool HHVM_FUNCTION(is_string, const Variant& v);
bool HHVM_FUNCTION(is_scalar, const Variant& v);
bool HHVM_FUNCTION(is_array, const Variant& v);
bool HHVM_FUNCTION(is_object, const Variant& v);
bool HHVM_FUNCTION(is_resource, const Variant& v);
// cheng-hack:
enum OPMAP_OP_TYPE {
  TYPE_NONE,
  META_START, META_END,
  REGISTER_READ, REGISTER_WRITE,
  KV_GET, KV_SET, KV_DEL,
  SQL_READ, SQL_WRITE, SQL_TXN
};
Variant HHVM_FUNCTION(add_multi, Variant var, Variant value, int64_t req_num);
Variant HHVM_FUNCTION(gen_multi, const Array& var);
void HHVM_FUNCTION(set_batch_upper_bound, int64_t size);
bool HHVM_FUNCTION(is_multi, const Variant& value);
Variant HHVM_FUNCTION(split_multi, const Variant& value);
Variant HHVM_FUNCTION(merge_multi, const Variant& value);
Variant HHVM_FUNCTION(rewrite_select_sql, const Variant& sql, int64_t rid, int64_t opnum, int64_t query_num);
bool HHVM_FUNCTION(check_write_sql, const Variant& sql, int64_t rid, int64_t opnum);
Variant HHVM_FUNCTION(MIC_to_MC, const Variant& value);
Variant HHVM_FUNCTION(MC_to_MIC, const Variant& value);
bool HHVM_FUNCTION(is_verify);
bool HHVM_FUNCTION(is_single_mode_on);
bool HHVM_FUNCTION(is_res_req);
void HHVM_FUNCTION(set_res_req, bool is_set);
int HHVM_FUNCTION(get_ins_counter);
int HHVM_FUNCTION(get_multi_ins_counter);
Variant HHVM_FUNCTION(get_classified_ins_counter);
Variant HHVM_FUNCTION(get_classified_mins_counter);
Variant HHVM_FUNCTION(sess_get_last_write, const int64_t rid, const int64_t opnum, const Variant& sess_id);
Variant HHVM_FUNCTION(sess_get_id, const int64_t rid, const int64_t opnum, bool check);
void HHVM_FUNCTION(set_should_count, bool count);
void HHVM_FUNCTION(replay_dump_output, const Variant& value);
void HHVM_FUNCTION(veri_dump_output, const Variant& path, const Variant& req_no);
void HHVM_FUNCTION(loop_var_capture, VRefParam loop_var_ref, VRefParam capture_var_ref, int64_t size);
void HHVM_FUNCTION(loop_var_end, VRefParam loop_var_ref, VRefParam capture_var_ref);

String HHVM_FUNCTION(gettype, const Variant& v);
String HHVM_FUNCTION(get_resource_type, const Resource& handle);

///////////////////////////////////////////////////////////////////////////////
// type conversion

bool HHVM_FUNCTION(settype, VRefParam var, const String& type);

///////////////////////////////////////////////////////////////////////////////
// input/output

Variant HHVM_FUNCTION(print_r, const Variant& expression, bool ret = false);
Variant HHVM_FUNCTION(print_p, const Variant& expression);
Variant HHVM_FUNCTION(var_export, const Variant& expression, bool ret = false);
void HHVM_FUNCTION(var_dump,
                   const Variant& v, const Array& _argv = null_array);
void HHVM_FUNCTION(debug_zval_dump, const Variant& variable);
String HHVM_FUNCTION(serialize, const Variant& value);
Variant HHVM_FUNCTION(unserialize, const String& str,
                      const Array& class_whitelist = empty_array_ref);

///////////////////////////////////////////////////////////////////////////////
// variable table

int64_t constexpr EXTR_OVERWRITE        = 0;
int64_t constexpr EXTR_SKIP             = 1;
int64_t constexpr EXTR_PREFIX_SAME      = 2;
int64_t constexpr EXTR_PREFIX_ALL       = 3;
int64_t constexpr EXTR_PREFIX_INVALID   = 4;
int64_t constexpr EXTR_PREFIX_IF_EXISTS = 5;
int64_t constexpr EXTR_IF_EXISTS        = 6;
int64_t constexpr EXTR_REFS             = 0x100;

///////////////////////////////////////////////////////////////////////////////
}

#endif // incl_HPHP_VARIABLE_H_
