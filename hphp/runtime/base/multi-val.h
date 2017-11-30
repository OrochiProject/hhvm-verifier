#ifndef incl_HPHP_HPHPMULTI_H_
#define incl_HPHP_HPHPMULTI_H_
#include <vector>
#include <set>
#include <memory>

#include "hphp/runtime/base/typed-value.h"
#include "hphp/runtime/base/countable.h"
#include "hphp/runtime/base/memory-manager.h"

// tv-helpers refer us!
//#include "hphp/runtime/base/tv-helpers.h"

#define CHENG_CHECK

namespace HPHP {

template <typename T>
using sptr = std::shared_ptr<T>;

class MultiValIter {
public:
  MultiValIter (MultiVal* multi, int pos) : m_pos(pos), m_multi(multi) {}

  bool operator != (MultiValIter& other) { return m_pos != other.m_pos; }
  TypedValue* operator * ();
  MultiValIter& operator ++ () { m_pos++; return *this; }

private:

  int m_pos;
  MultiVal* m_multi;
};


// one function I should use
void tvDecRefHelper(DataType type, uint64_t datum);

class MultiVal {

public:

  inline MultiVal() : m_multi_type(KindOfUninit), m_count(1) {
    values = new std::vector<TypedValue>(); 
  }

  inline MultiVal(int size) : m_multi_type(KindOfUninit), m_count(1) {
    values = new std::vector<TypedValue>(); 
    values->resize(size);
    TypedValue uninit_tv;
    uninit_tv.m_type = KindOfUninit;
    for (int i=0; i<size; i++) {
      (*values)[i] = uninit_tv;
    }
  }

  inline ~MultiVal() {
    int size = valSize();
    for (int i = 0; i < size; i++) {
      //tvRefcountedDecRef(getByVal(i));
      auto tv = getByVal(i);
      if (IS_REFCOUNTED_TYPE(tv->m_type)) {
        tvDecRefHelper(tv->m_type, tv->m_data.num);
      }
    }
    delete values;
  }

  inline int valSize() const { return values->size();}

  // get the value by the value index
  inline struct TypedValue* getByVal(int indx) { return &(*values)[indx]; }
  TypedValue* operator [] (int indx) { return getByVal(indx); }

  // check if the multi-value is reasonable
  bool valid();

  // used for copy mode
  void addValue(const struct TypedValue& v);
  void addValueNoInc(const struct TypedValue& v);
  // modify multival operations
  void setValById(int index, const struct TypedValue& v, bool setType);
  struct TypedValue popValById(int index);
  // Get the type
  DataType getType() {return m_multi_type;}
  // Set the type
  void setType(DataType d) { m_multi_type = d; valid();}

  // iterator functions
  MultiValIter begin() { return MultiValIter(this, 0); }
  MultiValIter end() { return MultiValIter(this, valSize()); }

  // copy, but will not copy the obj/array
  TypedValue copy();

  // helper function to generate a multivalue
  static TypedValue makeMultiVal();
  // helper function to clone a multivalue
  static TypedValue cloneMultiVal(TypedValue *tv);
  // helper function to debug
  std::string dump(std::string prefix="");
  // helper function to split an array
  static TypedValue splitArray(TypedValue& tv, int size);
  // helper function to split an object
  static TypedValue splitObject(TypedValue& tv, int size);
  // helper function to transfer an array with multi-value as an element
  // to multi-array with only single value elements
  static TypedValue transferArray(TypedValue tv);
  // helper function to transfer a multi-array to an array with multi-value 
  // used in FCallArray
  static TypedValue invertTransferArray(TypedValue tv);
  // helper function to transfer an object with multi-value as an element
  // to multi-obj with only single value elements
  static TypedValue transferObj(TypedValue tv);
  // helper function to transfer a multi-obj to an obj with multi-value 
  static TypedValue invertTransferObj(TypedValue tv);
  // helper function to get the ith value from a multi-value/multi-val-array
  static TypedValue selectIthVal(TypedValue tv, int i, bool skip_obj=false);
  // helper function to shrink the multivalue 
  TypedValue* shrinkToSingle();
  // check if there is any multi-value inside a container (array or obj)
  static int containMultiVal(TypedValue *tv, int depth=0);
  // dump more infomation of a TypedValue
  static std::string dumpElem(TypedValue *v, int nested=0);

  // countable
  IMPLEMENT_COUNTABLENF_METHODS_NO_STATIC
  void setRefCount(RefCount n) { m_count = n; }
  void release();

private:

  std::vector<struct TypedValue>* values;
  union {
    DataType m_multi_type;
    int32_t  padding;
  };
  mutable RefCount m_count;
};


}
#endif

