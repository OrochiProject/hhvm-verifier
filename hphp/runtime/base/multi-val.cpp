#include "hphp/runtime/base/multi-val.h"
#include "hphp/runtime/vm/native.h"
#include "hphp/runtime/ext/std/ext_std_variable.h"
#include "hphp/runtime/base/array-iterator.h"
#include "hphp/runtime/vm/member-operations.h"
#include "hphp/runtime/base/tv-helpers.h"

#include "fstream"
#include "set"

namespace HPHP {

//#define MUL_DETAIL_DEBUG
extern std::ofstream debug_log;

static inline void
castToStringInPlace(TypedValue* v) {
  cheng_assert(v->m_type == KindOfStaticString);
  auto str_ptr = v->m_data.pstr;
  v->m_type = KindOfString;
  v->m_data.pstr = StringData::Make(str_ptr, CopyString);
  tvRefcountedIncRef(v); 
}

static inline void
checkAdjustType(MultiVal* mv, TypedValue* adding_val) {
  auto m_multi_type = mv->getType();

  // some casting:
  //  int => Double
  if (m_multi_type == KindOfDouble && adding_val->m_type == KindOfInt64) {
    tvCastToDoubleInPlace(adding_val);
  }
  else if (m_multi_type == KindOfString && adding_val->m_type == KindOfStaticString) {
    castToStringInPlace(adding_val);
  }

  // promote the multi-val from Int to Double
  if (m_multi_type == KindOfInt64 && adding_val->m_type == KindOfDouble) {
    // change the previous Int into Double
    for (int i = 0; i < mv->valSize(); i++) {
      tvCastToDoubleInPlace(mv->getByVal(i));
    }
    mv->setType(KindOfDouble);
    m_multi_type = KindOfDouble;
  }
  // promote the multi-val from StaticString to String
  else if (m_multi_type == KindOfStaticString && adding_val->m_type == KindOfString) {
    // change the previous StaticString to String
    for (int i = 0; i < mv->valSize(); i++) {
      castToStringInPlace(mv->getByVal(i));
    }
    mv->setType(KindOfString);
    m_multi_type = KindOfString;
  }

  // if m_multi_type is KindOfUninit, we accept NULL/Uninit and whatever
  // if m_multi_type is decided, we accept NULL/Uninit and THAT TYPE
#ifdef CHENG_CHECK
  if ( m_multi_type != KindOfUninit
       && (adding_val->m_type != KindOfUninit && adding_val->m_type != KindOfNull) 
       && m_multi_type != adding_val->m_type) {
    TypedValue tmp;
    tmp.m_type = KindOfMulti;
    tmp.m_data.pmulti = mv;
    std::cout << "\n   === AddValue Warning ===\nOriginal MultiVal:\n";
    std::cout << "    === Elements:\n";
    for (auto it : *mv) {
      std::cout << it->pretty() << "\n";
    }
    HHVM_FN(print_r)(tvAsVariant(&tmp));
    std::cout << "\nAdding element:\n    " << adding_val->pretty() << "\n";
    always_assert(false);
  }

  // Allow NULL with other data
  always_assert(m_multi_type == KindOfUninit ||  m_multi_type == KindOfNull ||
               m_multi_type == adding_val->m_type || adding_val->m_type == KindOfNull || adding_val->m_type == KindOfUninit);

#endif
  if ((m_multi_type == KindOfUninit || m_multi_type == KindOfNull) 
      && (adding_val->m_type != KindOfUninit && adding_val->m_type != KindOfNull) ) {
    mv->setType(adding_val->m_type);
  }
}

void 
MultiVal::addValueNoInc(const struct TypedValue& ov) {
  TypedValue v = ov;
  checkAdjustType(this, &v);
  values->push_back(v);
}

void
MultiVal::addValue(const struct TypedValue& v) {
  addValueNoInc(v);
  tvRefcountedIncRef(&v);
}

void
MultiVal::setValById(int index, const TypedValue& tv, bool setType=false) {
  cheng_assert(index < values->size()); 

  TypedValue v = tv;
  checkAdjustType(this, &v);
  (*values)[index] = v;
  tvRefcountedIncRef(&v);
}

TypedValue
MultiVal::popValById(int index) {
  cheng_assert(index < values->size());
  TypedValue ret = *getByVal(index);
  values->erase(values->begin() + index);
  return ret;
}

bool
MultiVal::valid() {
#ifdef CHENG_CHECK
  // check the same type
  //for (int i = 0; i < valSize(); i++) {
  //  always_assert(m_multi_type == getByVal(i)->m_type);
  //}
#endif
  return true;
}


TypedValue* 
MultiValIter::operator * () {
  return m_multi->getByVal(m_pos);
}

struct TypedValue 
MultiVal::makeMultiVal() {
  TypedValue v;
  v.m_type = KindOfMulti;
  v.m_data.pmulti = new (MM().smartMallocSizeLogged(sizeof(MultiVal)))
    MultiVal(); 
  return v;
}

struct TypedValue
MultiVal::copy() {
  TypedValue new_tv = makeMultiVal();
  for (auto it : *values) {
    new_tv.m_data.pmulti->addValue(it);
  }
  return new_tv;
}

void
MultiVal::release() {
  this->~MultiVal();
  MM().smartFreeSizeLogged(this, sizeof(MultiVal));
}

//======================================
//=========== Helper function ==========
//======================================


// why do we need clone multivalue itself?
struct TypedValue
MultiVal::cloneMultiVal(TypedValue *tv) {
#ifdef CHENG_CHECK
  always_assert(tv->m_type == KindOfMulti);
#endif
  auto multi = tv->m_data.pmulti;
  TypedValue ret = makeMultiVal();
  auto ret_multi = ret.m_data.pmulti; 
  // CHECK: is this correct?
  ret_multi->setRefCount(multi->getCount());
  for (auto it : *multi) {
    TypedValue new_val;
    new_val.m_type = it->m_type;
    TypedValue *inner;
    switch (it->m_type) {
      case KindOfRef:
        // Make a new copy of the inner value, and reference it
        // FIXME: shared references?
        inner = it->m_data.pref->tv();
        tvCopy(*inner, new_val);
        tvBox(&new_val);
        ret_multi->addValue(new_val);
        break;
      case KindOfArray:
        // Copy the array
        new_val.m_data.parr = it->m_data.parr->copy();
        ret_multi->addValue(new_val);
        break;
      case KindOfString:
        // Strings are immutable, so copying and incrementing a reference should be okay?
        ret_multi->addValue(*it);
        tvRefcountedIncRef(it);
        break;
      case KindOfObject:
        new_val.m_data.pobj = it->m_data.pobj->clone();
        ret_multi->addValueNoInc(new_val);
        break;
      default: 
        ret_multi->addValue(*it);
        tvRefcountedIncRef(it);
        break;
    }
  }

  return ret;
}

struct TypedValue
MultiVal::splitArray(TypedValue& tv, int size) {
#ifdef CHENG_CHECK
  always_assert(tv.m_type == KindOfArray);
#endif

  // check whether we can do it fast
  int multi_size = containMultiVal(&tv);
  bool no_multi_val = (0 == multi_size);
  TypedValue ret = makeMultiVal();
  auto ret_multi = ret.m_data.pmulti;

  if (no_multi_val) {
    ArrayData *arr = tv.m_data.parr;
    for (int i = 0; i < size; i++) {
      TypedValue new_arr;
      // For split ref-array, we need all the field including gap field to be the same
      // After that, we copy the ArrayData
      memcpy(&new_arr, &tv, sizeof(TypedValue));
      new_arr.m_data.parr = arr->copy();
      ret_multi->addValue(new_arr); // FIXME: the count seems not right
    }
  } else {
    cheng_assert(size == multi_size);

    // In order to fix multi-multi-value problem, we need to
    // only get ith elements from current array
    for (int i = 0; i < size; i++) {
      auto ith_tv = selectIthVal(tv, i, true);
      ret_multi->addValue(ith_tv);
    }
  }

  // FIXME: check refcounts and decref if necessary, fix invariants
#ifdef CHENG_CHECK  
  always_assert(size == ret_multi->valSize());
#endif

  return ret;
}

struct TypedValue
MultiVal::splitObject(TypedValue& tv, int size) {
#ifdef CHENG_CHECK
  always_assert(tv.m_type == KindOfObject);
#endif
  auto obj = tv.m_data.pobj;
  TypedValue ret = makeMultiVal();
  auto ret_multi = ret.m_data.pmulti;
  for (int i = 0; i < size; i++) {
    TypedValue new_obj;
    // For split ref-obj, we need all the field including gap field to be the same
    // After that, we copy the ObjectData
    memcpy(&new_obj, &tv, sizeof(TypedValue));
    new_obj.m_data.pobj = obj->clone(); 
    ret_multi->addValue(new_obj);
  }
  // FIXME: check refcounts and decref if necessary, fix invariants

#ifdef CHENG_CHECK  
  always_assert(size == ret_multi->valSize());
#endif

  return ret;
}

static inline TypedValue
buildUninitMultiVal(int size) {
  // build uninitial multi-val
  TypedValue uninit_mv = MultiVal::makeMultiVal();
  TypedValue uninit;
  uninit.m_type = KindOfUninit;
  for (int i=0; i<size; i++) {
    uninit_mv.m_data.pmulti->addValue(uninit);
  }
  return uninit_mv;
}

TypedValue
MultiVal::invertTransferArray(TypedValue marr) {
#ifdef CHENG_CHECK
  always_assert(marr.m_type == KindOfMulti && marr.m_data.pmulti->getType() == KindOfArray);
#endif

  // get the multi_size
  int multi_size = marr.m_data.pmulti->valSize();

  // create the return array
  auto parr = staticEmptyArray(); // FIXME 
  for (int i=0; i<multi_size; i++) {
    // fetch each of the array
    auto it = marr.m_data.pmulti->getByVal(i);
    ArrayIter ait(it->m_data.parr);

    while(!ait.end()) {
      auto key = ait.first();      // Variant
      auto value = ait.nvSecond(); // TypedValue*
      // if this key exists, get the multi-value
      //         and put into the i-th location
      // if this key doesn't exist, add one uninit-multivalue,
      //         and put the value to i-th location
      if (parr->exists(key)) {
        auto val = parr->get(key);
        val.m_data.pmulti->setValById(i, *value);
      } else {
        auto tmp = buildUninitMultiVal(multi_size);
        tmp.m_data.pmulti->setValById(i, *value);
        parr = parr->set(key, tvAsVariant(&tmp), false);
      }
      ait.next();
    }
  }


  ArrayIter ait(parr);
  while(!ait.end()) {
    auto key = ait.first();
    auto value = ait.second();

    // Shrink the same multi-val
    // NOTE: this can be costy
    auto single = value.m_data.pmulti->shrinkToSingle();
    if (single != nullptr) {
      parr =parr->set(key, tvAsVariant(single), false);
    }
    // NOTE(1): we cannot do continue merging in the no-mv-in-container world 
    // since this function is only used by FCallArray, which need one layer merge
#ifdef MV_IN_CONTAINER_WORLD
    // Merge the additional multi-arr/obj
    else if (value.m_data.pmulti->getType() == KindOfArray) {
      auto ret = invertTransferArray(value);
      parr = parr->set(key, tvAsVariant(&ret), false);
    } else if (value.m_data.pmulti->getType() == KindOfObject) {
      auto ret = invertTransferObj(value);
      parr = parr->set(key, tvAsVariant(&ret), false);
    }
#endif

    ait.next();
  }

  TypedValue ret;
  ret.m_type = KindOfArray;
  ret.m_data.parr = parr; 
  tvRefcountedIncRef(&ret); 
  return ret;
}

struct TypedValue
MultiVal::transferArray(TypedValue tv) {
#ifdef CHENG_CHECK
  always_assert(tv.m_type == KindOfArray);
#endif

  // MIC_to_MC the inner element first
  ArrayIter ait(tv.m_data.parr);
  while(!ait.end()) {
    auto value = ait.second();
    if (value.m_type == KindOfArray) {
      if (0 != containMultiVal(value.asTypedValue())) {
        auto mc = transferArray(value); 
        tv.m_data.parr = tv.m_data.parr->set(ait.first(), tvAsVariant(&mc), true);
      }
    } else if (value.m_type == KindOfObject) {
      if (0 != containMultiVal(value.asTypedValue())) {
        auto mc = transferObj(value);
        tv.m_data.parr = tv.m_data.parr->set(ait.first(), tvAsVariant(&mc), true);
      }
    }
    ait.next();
  }

  // get the multivalue size
  int multi_size = containMultiVal(&tv);

#ifdef CHENG_CHECK
  always_assert(multi_size != 0);
#endif

  // do split first
  TypedValue new_tv = splitArray(tv, multi_size);
  // replace all the multi_value with corresponding single value
  for (int i = 0; i < multi_size; i++) {
    TypedValue *tmp_arr = new_tv.m_data.pmulti->getByVal(i);
#ifdef CHENG_CHECK
    always_assert(tmp_arr->m_type == KindOfArray);
#endif
    ArrayIter tmp_ait(tmp_arr->m_data.parr);
    while(!tmp_ait.end()) {
      auto key = tmp_ait.first();
      auto value = tmp_ait.second();
      if (value.m_type == KindOfMulti) {
        // this is the i'th array, which needs i'th element
        TypedValue *single_val = value.m_data.pmulti->getByVal(i);
        // NOTE: this should never cause escalation
        tmp_arr->m_data.parr = tmp_arr->m_data.parr->set(key, tvAsVariant(single_val), false);
      }
      tmp_ait.next();
    }
  }

  return new_tv;
}

// If tv does not conatin multival, it will return tv itself
struct TypedValue
MultiVal::selectIthVal(TypedValue tv, int i, bool skip_obj /*=false*/) {
  int multi_num = containMultiVal(&tv); 
  // either not multi-v; or i within multi-v size 
  always_assert(multi_num == 0 || i < multi_num);

  // if this is not multi-value, return directly
  // FIXME: is this correct?
  if (multi_num == 0) return tv;

  if (tv.m_type == KindOfArray) {
    auto new_arr = staticEmptyArray(); // FIXME 
    // create a new array, but all elements will be ith
    ArrayIter ait(tv.m_data.parr);
    while(!ait.end()) {
      auto key = ait.first();
      auto value = ait.second();
      auto ith_val = selectIthVal(value, i, skip_obj);
      // add to array
      new_arr = new_arr->set(key, tvAsVariant(&ith_val), false);
      ait.next();
    }

    TypedValue ret;
    ret.m_type = KindOfArray;
    ret.m_data.parr = new_arr; 
    tvRefcountedIncRef(&ret); 

    return ret;
  } else if (tv.m_type == KindOfObject) {
    if (skip_obj) return tv;

    // create a new obj, but all elements will be ith
    auto obj = tv.m_data.pobj->clone();

    // FIXME: ugly copy/paste from iterObjElemsAndReplace
    // should be uniformed

    // loop through all properties of obj
    auto cls = obj->getVMClass();
    do {
      auto c_name = cls->nameStr();
      Array arr = obj->o_toIterArray(c_name);

      ArrayIter it(arr);
      while(!it.end()) {
        auto key = it.first();
        auto val = it.secondRef().asTypedValue();

        auto ith_val = selectIthVal(*val, i, skip_obj);

        if (ith_val.m_type != KindOfUninit) {
          obj->setProp(cls, key.getStringData(), &ith_val);
        }
        it.next();
      }
      cls = cls->parent();
    } while(cls);

    TypedValue ret;
    ret.m_type = KindOfObject;
    ret.m_data.pobj = obj; 
    tvRefcountedIncRef(&ret); 
    return ret;

  } else if (tv.m_type == KindOfMulti) {
    auto ith_tv = *tv.m_data.pmulti->getByVal(i); 
    return selectIthVal(ith_tv, i, skip_obj);
  }
  // else
  return tv;
}

// NOTE: the public elements may be iterated more than once!
static void
iterObjElemsAndReplace(std::function <TypedValue (TypedValue*)> f, TypedValue *obj) {
  auto cls = obj->m_data.pobj->getVMClass();
  do {
    auto c_name = cls->nameStr();
    Array arr = obj->m_data.pobj->o_toIterArray(c_name);

    ArrayIter it(arr);
    while(!it.end()) {
      auto key = it.first();
      auto val = it.secondRef().asTypedValue();
      auto new_v = f((TypedValue*)val);
      if (new_v.m_type != KindOfUninit) {
        obj->m_data.pobj->setProp(cls, key.getStringData(), &new_v);
      }
      it.next();
    }
    cls = cls->parent();
  } while(cls);
}


// MC to MIC
struct TypedValue
MultiVal::invertTransferObj(TypedValue obj) {
#ifdef CHENG_CHECK
  always_assert(obj.m_type == KindOfMulti && obj.m_data.pmulti->getType() == KindOfObject);
#endif

  // (1) Create empty object, and assign each key/value to it
  // (2) check the container whehter they are multi, and do the same thing
  
  int multi_size = containMultiVal(&obj);

  auto obj_cls = obj.m_data.pmulti->getByVal(0)->m_data.pobj->getVMClass();
  auto ret_obj = newInstance(obj_cls);

  for (int i=0; i<multi_size; i++) {
    auto tmp_obj = obj.m_data.pmulti->getByVal(i)->m_data.pobj;

    auto cls = tmp_obj->getVMClass();
    do {
      auto c_name = cls->nameStr();
      Array arr = tmp_obj->o_toIterArray(c_name);

      ArrayIter it(arr);
      while(!it.end()) {
        auto key = it.first();
        auto val = it.secondRef().asTypedValue();

        auto look_up = ret_obj->getProp(cls, key.getStringData());
        auto prop = look_up.prop;
        if (prop && prop->m_type != KindOfNull && prop->m_type != KindOfUninit) {
          // if the prop exists
          cheng_assert(prop->m_type == KindOfMulti);
          prop->m_data.pmulti->setValById(i, *val);
        } else {
          // if prop does not exist
          auto tmp = buildUninitMultiVal(multi_size);
          tmp.m_data.pmulti->setValById(i, *val);
          ret_obj->setProp(cls, key.getStringData(), &tmp);
        }
        it.next();
      }
      cls = cls->parent();
    } while(cls);
  }

  // (2) shrink and recursively call invert
  auto cls = ret_obj->getVMClass();
  do {

    auto c_name = cls->nameStr();
    Array arr = ret_obj->o_toIterArray(c_name);

    ArrayIter it(arr);
    while(!it.end()) {
      auto key = it.first();
      auto val = it.secondRef().asTypedValue();

      auto single = val->m_data.pmulti->shrinkToSingle();
      if (single != nullptr) {
        ret_obj->setProp(cls, key.getStringData(), single);
      }
      // See NOTE(1)
#ifdef MV_IN_CONTAINER_WORLD
      // Merge the additional multi-arr/obj
      else if (val->m_data.pmulti->getType() == KindOfArray) {
        auto ret = invertTransferArray(*val);
        ret_obj->setProp(cls, key.getStringData(), &ret);
      } else if (val->m_data.pmulti->getType() == KindOfObject) {
        auto ret = invertTransferObj(*val);
        ret_obj->setProp(cls, key.getStringData(), &ret);
      }
#endif
      it.next();
    }
    cls = cls->parent();
  } while(cls);


  TypedValue result;
  result.m_type = KindOfObject;
  result.m_data.pobj = ret_obj;
  return result;
}

// MIC to MC
// (1) search contained elements, if multi, split
// (2) split the object itself, and assign each element to the correct location
struct TypedValue
MultiVal::transferObj(TypedValue tv) {
#ifdef CHENG_CHECK
  always_assert(tv.m_type == KindOfObject);
#endif

  auto f = [] (TypedValue* value) {
    TypedValue ret;
    ret.m_type = KindOfUninit;

    if (value->m_type == KindOfArray) {
      if (containMultiVal(value)) {
        ret = transferArray(*value);
      }
    } else if (value->m_type == KindOfObject) {
      if (containMultiVal(value)) {
        ret = transferObj(*value);
      }
    }

    return ret;
  };
  iterObjElemsAndReplace(f, &tv);
    
  // get the multivalue size
  int multi_size = containMultiVal(&tv);

#ifdef CHENG_CHECK
  cheng_assert(multi_size != 0);
#endif

  // do split first
  TypedValue new_tv = splitObject(tv, multi_size);
  // replace all the multi_value with corresponding single value
  for (int i = 0; i < multi_size; i++) {
    TypedValue *tmp_obj = new_tv.m_data.pmulti->getByVal(i);
#ifdef CHENG_CHECK
    always_assert(tmp_obj->m_type == KindOfObject);
#endif

    auto f2 = [i] (TypedValue *value) {
      TypedValue ret;
      ret.m_type = KindOfUninit;
      if (value->m_type == KindOfMulti) {
        ret = *value->m_data.pmulti->getByVal(i);
      }
      return ret;
    };

    iterObjElemsAndReplace(f2 ,tmp_obj);
  }

  return new_tv;
}


// cycle-breaker: in PHP only obj can have cycle, remember all the obj in a set.
// if meet it again, just return
#define TRACK_MAX_DEPTH 10
// the return value is the size of the multi-value
// 0 indicates there is no multi-value
// FIXME: not touch depth for now
thread_local std::set<ObjectData*> met_obj;
int MultiVal::containMultiVal(TypedValue* v, int depth) {
  if (depth == 0) { met_obj.clear(); }
  if (depth > (TRACK_MAX_DEPTH) ) return false; // prohibit the cycle-ref

  switch(v->m_type) {
  case KindOfNull:
  case KindOfUninit:
  case KindOfInt64:
  case KindOfDouble:
  case KindOfBoolean:
  case KindOfClass:
  case KindOfResource:
  case KindOfString:
  case KindOfStaticString:
    return 0;
  case KindOfRef:
    return containMultiVal(tvToCell(v), depth+1);
  case KindOfMulti:
    return v->m_data.pmulti->valSize();
  case KindOfArray:
    {
      ArrayIter it(v->m_data.parr);
      while(!it.end()) {
        auto val = it.second();
        int size = containMultiVal(val.asTypedValue(), depth+1);
        if (size != 0) {
          return size;
        }
        it.next();
      }
      return 0;
    }
  case KindOfObject:
    {
      // check if we've ever seen this obj
      if (met_obj.find(v->m_data.pobj) != met_obj.end()) {
        // we've seen this obj, just return
        return 0;
      } else {
        // this is a new object, push it to set
        met_obj.insert(v->m_data.pobj);
      }
      auto cls = v->m_data.pobj->getVMClass();
      do {
        auto c_name = cls->nameStr();
        Array arr = v->m_data.pobj->o_toIterArray(c_name);

        ArrayIter it(arr);
        while(!it.end()) {
          auto val = it.second();
          int size = containMultiVal(val.asTypedValue(), depth+1);
          if (size != 0) {
            return size;
          }
          it.next();
        }
        cls = cls->parent();
      } while(cls);
      return 0;
    }
  }
  // should never been here
  not_reached();
}

static int64_t prime = 179424691L;
static inline int64_t addToHash(int64_t hash, int64_t op) {
  return hash*prime + op; 
}
static int64_t calValHash(TypedValue* v) {
  int64_t hash = 1;
  hash = addToHash(hash, (int64_t) (v->m_type));

  int64_t tmp_hash;
  switch(v->m_type) {
  case KindOfNull:
  case KindOfUninit:
    return hash;
  // these are compared by value
  case KindOfInt64:
  case KindOfDouble:
  case KindOfBoolean:
  // these are compared by ptr
  case KindOfClass:
  case KindOfResource:
    hash = addToHash(hash, v->m_data.num); // resource to see their address
    return hash;
  case KindOfRef:
    tmp_hash = calValHash(v->m_data.pref->tv());
    if (tmp_hash == INTMAX_MAX) return INTMAX_MAX;
    hash = addToHash(hash, tmp_hash);
    return hash;
  case KindOfString:
  case KindOfStaticString:
    tmp_hash = std::hash<std::string>{}(v->m_data.pstr->toCppString());
    hash = addToHash(hash, tmp_hash);
    return hash;
  case KindOfMulti:
    return INTMAX_MAX; // this is a single to not merge
  case KindOfArray: {
      ArrayIter it(v->m_data.parr);
      while(!it.end()) {
        auto key = it.first();
        auto key_hash = calValHash(key.asTypedValue());
        if (key_hash == INTMAX_MAX) return INTMAX_MAX;
        hash = addToHash(hash, key_hash);

        auto val = it.second();
        auto val_hash = calValHash(key.asTypedValue());
        if (val_hash == INTMAX_MAX) return INTMAX_MAX;
        hash = addToHash(hash, val_hash);

        it.next();
      }
      return hash;
      }
  case KindOfObject:
    hash = addToHash(hash, (int64_t)v->m_data.pobj);
    return hash; 
  }
  // should never been here
  not_reached();
}

static bool isSameVal (TypedValue* v1, TypedValue* v2) {
  if (v1->m_type != v2->m_type) {
    return false;
  }

  Array a1, a2;
  switch(v1->m_type) {
  case KindOfNull:
  case KindOfUninit:
    return true;
  // these are compared by value
  case KindOfInt64:
  case KindOfDouble:
  case KindOfBoolean:
  // these are compared by ptr
  case KindOfClass:
  case KindOfResource:
    if (v1->m_data.num == v2->m_data.num) {
      return true;
    } else {
      return false;
    }
  case KindOfRef:
    if (v1->m_data.pref->tv() == v2->m_data.pref->tv()) {
      return true;
    } else {
      return false;
    }
  case KindOfString:
  case KindOfStaticString:
    if (v1->m_data.pstr->toCppString() == v2->m_data.pstr->toCppString()) {
      return true;
    } else {
      return false;
    }
  case KindOfMulti:
    // FIXME: it is possible to have multival in multival
    // for example: multi-array->single-obj->multi-val
    //std::cout << "FATAL ERROR: there is a multi-val inside another multi-val\n";
    //HHVM_FN(debug_print_backtrace)();
    //always_assert(false);
    return false;
  // compare all the elements recursively, this may very costy!
  // FIXME: assume the sequence of the attributes are the same
  case KindOfArray: {
      ArrayIter it1(v1->m_data.parr), it2(v2->m_data.parr);
      while(!it1.end() && !it2.end()) {
        auto key1 = it1.first();
        auto key2 = it2.first();
        auto val1 = it1.second();
        auto val2 = it2.second();
        if (!isSameVal(&key1, &key2) || !isSameVal(&val1, &val2)) {
          return false;
        }
        it1.next();
        it2.next();
      }
      if (it1.end() != it2.end()) {
        return false;
      }
      return true;
    }

  case KindOfObject:

#ifdef MV_IN_CONTAINER_WORLD
    // FIXME: how to fix cycle reference problem? i.e. $a->b == $b && $b->a = a
    // There will be an infinite loop
    auto class1 = v1->m_data.pobj->getVMClass();
    auto class2 = v2->m_data.pobj->getVMClass();
    do {
      auto c1_name = class1->nameStr();
      auto c2_name = class2->nameStr();
      a1 = v1->m_data.pobj->o_toIterArray(c1_name);
      a2 = v2->m_data.pobj->o_toIterArray(c2_name);
#ifdef MUL_DETAIL_DEBUG
      debug_log << "!!!!!!!!!!!!!! Class Name [" << c1_name.c_str() << "]!!!!!!!!!!!!!!!!!!!!!\n";
#endif

      ArrayIter it1(a1), it2(a2);
      while(!it1.end() && !it2.end()) {
        auto key1 = it1.first();
        auto key2 = it2.first();
        auto val1 = it1.second();
        auto val2 = it2.second();
#ifdef MUL_DETAIL_DEBUG
        debug_log << "!!!!!!!!!!!!!! KindOf Array or Obj !!!!!!!!!!!!!!!!!!!!!\n";
        auto key1_txt = HHVM_FN(print_r)(tvAsVariant(&key1),true);
        auto key2_txt = HHVM_FN(print_r)(tvAsVariant(&key2),true);
        auto val1_txt = HHVM_FN(print_r)(tvAsVariant(&val1),true);
        auto val2_txt = HHVM_FN(print_r)(tvAsVariant(&val2),true);
        debug_log << "    -- compare two val:\n";
        debug_log << "       key1:{{" << key1_txt.toString().toCppString() << "}}\n";
        debug_log << "       key2:{{" << key2_txt.toString().toCppString() << "}}\n";
        debug_log << "       val1:{{" << val1_txt.toString().toCppString() << "}}\n";
        debug_log << "       val2:{{" << val2_txt.toString().toCppString() << "}}\n";
#endif
        if (!isSameVal(&key1, &key2) || !isSameVal(&val1, &val2)) {
          return false;
        }
        it1.next();
        it2.next();
      }
      if (it1.end() != it2.end()) {
        return false;
      }
      class1 = class1->parent();
      class2 = class2->parent();
      always_assert( (class1!=nullptr) == (class2!=nullptr) );
    } while(class1);
    return true;
#else
    if (v1->m_data.pobj == v2->m_data.pobj) {
      return true;
    } else {
      return false;
    }
#endif
  }
  // should never been here
  not_reached();
}

TypedValue*
MultiVal::shrinkToSingle() {
  // check if every elements are the same
  auto half_indx = valSize() / 2;
  auto first = getByVal(0);
  auto half = getByVal(half_indx);
  auto last = getByVal(valSize()-1);

  bool compare_val_impl = false;

  if (compare_val_impl) {

    int64_t first_hash = calValHash(first);
    int64_t half_hash = calValHash(half);
    // INTMAX_MAX indicates there is MultiVal within
    if (first_hash == INTMAX_MAX || half_hash == INTMAX_MAX || first_hash != half_hash) {
      return nullptr;
    }
    int64_t last_hash = calValHash(last);
    if (last_hash == INTMAX_MAX || first_hash != last_hash) {
      return nullptr;
    }

    for (int i = 1; i < valSize(); i++) {
      auto cur_hash = calValHash(getByVal(i));
      if (cur_hash == INTMAX_MAX || first_hash != cur_hash) {
        return nullptr;
      }
    }

    return first;

  } else {

    // optimization: try to quit quickly
    if (!isSameVal(first, half)) {
      return nullptr;
    }
    if (!isSameVal(first, last)) {
      return nullptr;
    }

    for (int i = 1; i < valSize(); i++) {
      // std::cout << "first: " << first->pretty() << " now: " << getByVal(i)->pretty() << "\n";
      // if (first->m_data.num != getByVal(i)->m_data.num) {
      if (!isSameVal(first, getByVal(i))) {
        return nullptr;
      }
    }
    return first;

  }
  not_reached();
}

// used for debug
static std::string
typeToString(DataType d) {
  switch (d) {
  case KindOfInt64: return "Int";
  case KindOfDouble: return "Double";
  case KindOfString: return "String";
  case KindOfUninit: return "Uninit";
  case KindOfArray: return "Array";
  case KindOfMulti: return "MultiVal";
  case KindOfNull: return "Null";
  case KindOfBoolean: return "Bool";
  case KindOfObject: return "Obj";
  case KindOfResource: return "Res";
  case KindOfClass: return "Class";
  case KindOfStaticString: return "StaticString";
  case KindOfRef: return "Ref";
  }
  return "UNKOWN";
}

std::string
MultiVal::dumpElem(TypedValue* v, int nested) {
  std::stringstream ss;
  
  if (nested > TRACK_MAX_DEPTH) {
    return "\nXXX:  [too deep to display...]\n";
  }

  ss << v->pretty() << ": ";
  switch (v->m_type) {
  case KindOfMulti:
      // NOTE: might have infinite loop
      if (nested == 0) {
        ss << v->m_data.pmulti->dump("");
      } else {
        ss << "[*] MultiVal (\n";
        int counter = 0;
        for (auto it : *v->m_data.pmulti) {
          ss << "    <" << counter++ << ">:: " << it->pretty() << "\n";
        }
        ss << ")\n";
      }
      break;
  case KindOfRef:
      ss << "(" << v->m_data.pref->var()->getRefCount()
        << ") -> " << dumpElem(tvToCell(v), nested+1);
      break;
  case KindOfArray: {
      ArrayIter ait(v->m_data.parr);
      ss << "Array (\n";
      while(!ait.end()) {
        auto key = ait.first();
        auto val = ait.nvSecond();
        ss << "  [" << key.toString().toCppString() << "] => "
          << dumpElem((TypedValue*)val, nested+1) << "\n";
        ait.next();
      }
      ss << ")\n";
      } break;
  case KindOfString:
  case KindOfStaticString:
  case KindOfObject: {
      auto txt = HHVM_FN(print_r)(tvAsVariant(v), true);
      ss << txt.toString().toCppString()
         << "(" << (uint32_t)v->m_data.pstr->getCount() << ")"; 
      } break;
  default: {
      auto txt = HHVM_FN(print_r)(tvAsVariant(v), true);
      ss << " : {{ " << txt.toString().toCppString() << "}}";
      }
  }
  return ss.str();
}

std::string
MultiVal::dump(std::string prefix) {
  std::stringstream ss;
  ss << prefix << "MultiVal, type: " << typeToString(m_multi_type);
  ss << "  valSize: " << valSize() << " ref-count: " << m_count << "\n";
  ss << prefix << "  elements: {\n";
  int counter = 0;
  for (auto it : *this) {
    ss << prefix << "    <" << counter++ << ">:: {{" << dumpElem(it, 1) << " }}\n";
  }
  ss << prefix << "  }\n";

  return ss.str();
}

// end of HPHP
}
