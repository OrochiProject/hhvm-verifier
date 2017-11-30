/*
   +----------------------------------------------------------------------+
   | HipHop for PHP                                                       |
   +----------------------------------------------------------------------+
   | Copyright (c) 2010-2014 Facebook, Inc. (http://www.facebook.com)     |
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
#include "hphp/runtime/vm/bytecode.h"

#include <algorithm>
#include <string>
#include <vector>
#include <sstream>
#include <iostream>
#include <iomanip>
#include <cinttypes>

#include <boost/filesystem.hpp>
#include <boost/format.hpp>

#include <libgen.h>
#include <sys/mman.h>

#include <folly/String.h>

#include "hphp/runtime/base/array-init.h"
#include "hphp/runtime/base/externals.h"
#include "hphp/runtime/base/tv-comparisons.h"
#include "hphp/runtime/base/tv-conversions.h"
#include "hphp/runtime/base/tv-arith.h"
#include "hphp/runtime/base/apc-stats.h"
#include "hphp/compiler/builtin_symbols.h"
#include "hphp/runtime/vm/event-hook.h"
#include "hphp/runtime/vm/repo.h"
#include "hphp/runtime/vm/repo-global-data.h"
#include "hphp/runtime/base/repo-auth-type-codec.h"
#include "hphp/runtime/vm/func-inline.h"
#include "hphp/runtime/vm/jit/mc-generator.h"
#include "hphp/runtime/vm/jit/translator.h"
#include "hphp/runtime/vm/jit/translator-runtime.h"
#include "hphp/runtime/vm/srckey.h"
#include "hphp/runtime/vm/member-operations.h"
#include "hphp/runtime/base/class-info.h"
#include "hphp/runtime/base/code-coverage.h"
#include "hphp/runtime/base/unit-cache.h"
#include "hphp/runtime/base/base-includes.h"
#include "hphp/runtime/base/execution-context.h"
#include "hphp/runtime/base/runtime-option.h"
#include "hphp/runtime/base/mixed-array.h"
#include "hphp/runtime/base/shape.h"
#include "hphp/runtime/base/struct-array.h"
#include "hphp/runtime/base/program-functions.h"
#include "hphp/runtime/base/strings.h"
#include "hphp/runtime/base/apc-typed-value.h"
#include "hphp/util/text-util.h"
#include "hphp/util/trace.h"
#include "hphp/util/debug.h"
#include "hphp/runtime/base/stat-cache.h"
#include "hphp/runtime/vm/debug/debug.h"
#include "hphp/runtime/vm/hhbc.h"
#include "hphp/runtime/vm/php-debug.h"
#include "hphp/runtime/vm/debugger-hook.h"
#include "hphp/runtime/vm/runtime.h"
#include "hphp/runtime/base/rds.h"
#include "hphp/runtime/vm/treadmill.h"
#include "hphp/runtime/vm/type-constraint.h"
#include "hphp/runtime/vm/unwind.h"
#include "hphp/runtime/vm/jit/translator-inline.h"
#include "hphp/runtime/vm/native.h"
#include "hphp/runtime/vm/resumable.h"
#include "hphp/runtime/ext/ext_closure.h"
#include "hphp/runtime/ext/ext_generator.h"
#include "hphp/runtime/ext/apc/ext_apc.h"
#include "hphp/runtime/ext/array/ext_array.h"
#include "hphp/runtime/ext/asio/async_function_wait_handle.h"
#include "hphp/runtime/ext/asio/async_generator.h"
#include "hphp/runtime/ext/asio/async_generator_wait_handle.h"
#include "hphp/runtime/ext/asio/static_wait_handle.h"
#include "hphp/runtime/ext/asio/wait_handle.h"
#include "hphp/runtime/ext/asio/waitable_wait_handle.h"
#include "hphp/runtime/ext/hh/ext_hh.h"
#include "hphp/runtime/ext/reflection/ext_reflection.h"
#include "hphp/runtime/ext/std/ext_std_function.h"
#include "hphp/runtime/ext/std/ext_std_math.h"
#include "hphp/runtime/ext/std/ext_std_variable.h"
#include "hphp/runtime/ext/string/ext_string.h"
#include "hphp/runtime/base/stats.h"
#include "hphp/runtime/vm/type-profile.h"
#include "hphp/runtime/server/source-root-info.h"
#include "hphp/runtime/server/rpc-request-handler.h"
#include "hphp/runtime/base/extended-logger.h"
#include "hphp/runtime/base/memory-profile.h"
#include "hphp/runtime/base/memory-manager.h"
#include "hphp/runtime/base/runtime-error.h"
#include "hphp/runtime/base/container-functions.h"

#include "hphp/system/systemlib.h"
#include "hphp/runtime/ext/ext_collections.h"

#include "hphp/runtime/vm/globals-array.h"

// cheng-hack:
#include "hphp/runtime/base/multi-val.h"
#include "functional"
#include "mutex"
#include "hphp/runtime/vm/yastopwatch.h"
#include <thread>
#include <time.h>

namespace HPHP {

// TODO: #1746957, #1756122
// we should skip the call in call_user_func_array, if
// by reference params are passed by value, or if its
// argument is not an array, but currently lots of tests
// depend on actually making the call.
const bool skipCufOnInvalidParams = false;

// RepoAuthoritative has been raptured out of runtime_option.cpp. It needs
// to be closer to other bytecode.cpp data.
bool RuntimeOption::RepoAuthoritative = false;

using jit::mcg;

#define IOP_ARGS        PC& pc
#if DEBUG
#define OPTBLD_INLINE
#else
#define OPTBLD_INLINE ALWAYS_INLINE
#endif
TRACE_SET_MOD(bcinterp);

//===========================================
//===========================================
// cheng-hack:

// verification related
bool cheng_verification = false;
thread_local std::stringstream veri_buf;
thread_local bool is_resource_req = false;

//#define CHENG_INS_DEBUG
//#define CHENG_INS_ONLY_DEBUG
//#define CHENG_TIME_EVAL
//#define CHENG_COUNT_INS // will overwrite the CHENG_TIME_EVAL's multi_time
//#define CHENG_CYCLE_WAR_TUNING
//#define CHENG_DEBUG_STACK
//#define CHENG_PRINT_N 0
//#define CHENG_CLASSIFY_INS_PROF
//#define CHENG_PRINT_CF // conflict with CHENG_CLASSIFY_INS_PROF, shut down print_ins

#define CHENG_USE_CLOCK_CPU_TIME

//#define CHENG_CHECK

//#define CHENG_OPT_1
#define CHENG_OPT_DB_UPDATE

//#undef CHENG_CHECK

// for profiling the steps in verification not in normal exec
DEF_SW(db_trans_time);
DEF_SW(db_dedup_time);
DEF_SW(apc_time);
DEF_SW(opmap_time);

// program state variables
std::string site_root;
thread_local int batch_size = 1;
thread_local bool php_code_running = false;

// POINT1: loop capture mode
thread_local bool loop_capture_mode = false;
thread_local std::vector<TypedValue> finish_loop_var;
thread_local std::vector<TypedValue> finish_capture_var;
thread_local std::vector<int> loop_alive;
thread_local TypedValue origin_loop_var_ref;
thread_local TypedValue origin_capture_var_ref;

// POINT2: mode on builtin/constructor/magic methods
thread_local bool single_mode_on = false;
thread_local int  single_mode_cur_iter = -1;
thread_local int  single_mode_size = -1;

thread_local int zone_level = 0;
thread_local int zone_index = -1;

// POINT3: for builtin class __construct
thread_local bool builtin_class_new = false;

std::string builtin_class[] = {
  "DateTime"
};

ALWAYS_INLINE static bool
isBuiltinClass(std::string cname) {
  for (auto str_it : builtin_class) {
    if (str_it == cname) return true;
  }
  return false;
}

bool without_crash = false; 
bool should_count = true;
thread_local int nested_ins_level = 0;
thread_local int64_t ins_counter = 0;
thread_local int64_t multi_ins_counter = 0;

//======== break-even batch size ==========
int64_t batch_upperbound = LONG_MAX;

int64_t
get_batch_upperbound() {
  return batch_upperbound;
}

void
set_batch_upperbound(int64_t bound) {
  cheng_assert(bound > 1);
  batch_upperbound = bound;
}

//======== clock to get cpu time ==========

inline void
flush_clock_cpu_time() {
#ifdef CHENG_USE_CLOCK_CPU_TIME
  // measure the cpu time using clock()
  double time_elapsed = (double)clock() / CLOCKS_PER_SEC * 1000;
  std::ofstream otf6("/tmp/hhvmm_cpu_time.log", std::ofstream::app);
  otf6 << time_elapsed << "\n";
  otf6.close();
#endif
}

//======== alpha related functions =========
#ifdef CHENG_COUNT_INS 

inline void
nested_ins_level_inc() {
  cheng_assert(nested_ins_level>=0);
  nested_ins_level++;
}

inline void
nested_ins_level_dec() {
  cheng_assert(nested_ins_level>0);
  nested_ins_level--;
}

inline void
ins_counter_inc() {
  if (LIKELY(nested_ins_level == 0)) ins_counter++;
  //ins_counter++;
}

#else 

inline void nested_ins_level_inc() { ((void)0); }
inline void nested_ins_level_dec() { ((void)0); }
inline void ins_counter_inc() { ((void)0); }

#endif

//======= scientific functions ========
thread_local int oparr_ins_counter = 0;
thread_local int oparith_ins_counter = 0;
thread_local int opcf_ins_counter = 0;
thread_local int opget_ins_counter = 0;
thread_local int opset_ins_counter = 0;
thread_local int opisset_ins_counter = 0;
thread_local int opcall_ins_counter = 0;
thread_local int opmember_ins_counter = 0;
thread_local int opiter_ins_counter = 0;
thread_local int opmisc_ins_counter = 0;

thread_local int oparr_mins_counter = 0;
thread_local int oparith_mins_counter = 0;
thread_local int opcf_mins_counter = 0;
thread_local int opget_mins_counter = 0;
thread_local int opset_mins_counter = 0;
thread_local int opisset_mins_counter = 0;
thread_local int opcall_mins_counter = 0;
thread_local int opmember_mins_counter = 0;
thread_local int opiter_mins_counter = 0;
thread_local int opmisc_mins_counter = 0;

#ifdef CHENG_CLASSIFY_INS_PROF

inline void clear_classify_ins_counter() {
  oparr_ins_counter = 0;
  oparith_ins_counter = 0;
  opcf_ins_counter = 0;
  opget_ins_counter = 0;
  opset_ins_counter = 0;
  opisset_ins_counter = 0;
  opcall_ins_counter = 0;
  opmember_ins_counter = 0;
  opiter_ins_counter = 0;
  opmisc_ins_counter = 0;

  oparr_mins_counter = 0;
  oparith_mins_counter = 0;
  opcf_mins_counter = 0;
  opget_mins_counter = 0;
  opset_mins_counter = 0;
  opisset_mins_counter = 0;
  opcall_mins_counter = 0;
  opmember_mins_counter = 0;
  opiter_mins_counter = 0;
  opmisc_mins_counter = 0;
}

inline void as_arr() {
  if (LIKELY(nested_ins_level == 0)) oparr_ins_counter++;
}

inline void as_arith() {
  if (LIKELY(nested_ins_level == 0)) oparith_ins_counter++;
}

inline void as_cf() {
  if (LIKELY(nested_ins_level == 0)) opcf_ins_counter++;
}

inline void as_get() {
  if (LIKELY(nested_ins_level == 0)) opget_ins_counter++;
}

inline void as_set() {
  if (LIKELY(nested_ins_level == 0)) opset_ins_counter++;
}

inline void as_isset() {
  if (LIKELY(nested_ins_level == 0)) opisset_ins_counter++;
}

inline void as_call() {
  if (LIKELY(nested_ins_level == 0)) opcall_ins_counter++;
}

inline void as_member() {
  if (LIKELY(nested_ins_level == 0)) opmember_ins_counter++;
}

inline void as_iter() {
  if (LIKELY(nested_ins_level == 0)) opiter_ins_counter++;
}

inline void as_misc() {
  if (LIKELY(nested_ins_level == 0)) opmisc_ins_counter++;
}


inline void as_marr() {
  if (LIKELY(nested_ins_level == 0)) {
    oparr_ins_counter--;
    oparr_mins_counter++;
  }
}

inline void as_marith() {
  if (LIKELY(nested_ins_level == 0)) {
    oparith_ins_counter--;
    oparith_mins_counter++;
  }
}

inline void as_mcf() {
  if (LIKELY(nested_ins_level == 0)) {
    opcf_ins_counter--;
    opcf_mins_counter++;
  }
}

inline void as_mget() {
  if (LIKELY(nested_ins_level == 0)) {
    opget_ins_counter--;
    opget_mins_counter++;
  }
}

inline void as_mset() {
  if (LIKELY(nested_ins_level == 0)) {
    opset_ins_counter--;
    opset_mins_counter++;
  }
}

inline void as_misset() {
  if (LIKELY(nested_ins_level == 0)) {
    opisset_ins_counter--;
    opisset_mins_counter++;
  }
}

inline void as_mcall() {
  if (LIKELY(nested_ins_level == 0)) {
    opcall_ins_counter--;
    opcall_mins_counter++;
  }
}

inline void as_mmember() {
  if (LIKELY(nested_ins_level == 0)) {
    opmember_ins_counter--;
    opmember_mins_counter++;
  }
}

inline void as_miter() {
  if (LIKELY(nested_ins_level == 0)) {
    opiter_ins_counter--;
    opiter_mins_counter++;
  }
}

inline void as_mmisc() {
  if (LIKELY(nested_ins_level == 0)) {
    opmisc_ins_counter--;
    opmisc_mins_counter++;
  }
}

#define CLEAR_CLASSIFY_INS_COUNTER clear_classify_ins_counter()
#define AS_ARR    as_arr() 
#define AS_ARITH  as_arith() 
#define AS_CF     as_cf() 
#define AS_GET    as_get() 
#define AS_SET    as_set() 
#define AS_ISSET  as_isset() 
#define AS_CALL   as_call()
#define AS_MEMBER as_member() 
#define AS_ITER   as_iter() 
#define AS_MISC   as_misc() 

#define AS_MARR    as_marr() 
#define AS_MARITH  as_marith() 
#define AS_MCF     as_mcf() 
#define AS_MGET    as_mget() 
#define AS_MSET    as_mset() 
#define AS_MISSET  as_misset() 
#define AS_MCALL   as_mcall()
#define AS_MMEMBER as_mmember() 
#define AS_MITER   as_miter() 
#define AS_MMISC   as_mmisc() 

#else 

#define CLEAR_CLASSIFY_INS_COUNTER ((void)0) 
#define AS_ARR    ((void)0)
#define AS_ARITH  ((void)0)
#define AS_CF     ((void)0)
#define AS_GET    ((void)0)
#define AS_SET    ((void)0)
#define AS_ISSET  ((void)0)
#define AS_CALL   ((void)0)
#define AS_MEMBER ((void)0)
#define AS_ITER   ((void)0)
#define AS_MISC   ((void)0)

#define AS_MARR    ((void)0)
#define AS_MARITH  ((void)0)
#define AS_MCF     ((void)0)
#define AS_MGET    ((void)0)
#define AS_MSET    ((void)0)
#define AS_MISSET  ((void)0)
#define AS_MCALL   ((void)0)
#define AS_MMEMBER ((void)0)
#define AS_MITER   ((void)0)
#define AS_MMISC   ((void)0)
#endif


//======== helper functions =========
static std::vector<string> str_explode(std::string str, std::string delimiter){
  std::vector<string> ret;
  size_t start = 0, end = str.find(delimiter); 

  while (end != std::string::npos) {
    ret.push_back(str.substr(start, end-start));
    start = end + delimiter.length();
    end = str.find(delimiter, start);
  }

  // the last one
  auto end_piece = str.substr(start);
  if (end_piece != "") {
    ret.push_back(str.substr(start));
  }

  return ret;
}

static inline std::string trim(std::string &s) {
  s.erase(s.begin(), std::find_if(s.begin(), s.end(),
          std::not1(std::ptr_fun<int, int>(std::isspace))));

  s.erase(std::find_if(s.rbegin(), s.rend(),
          std::not1(std::ptr_fun<int, int>(std::isspace))).base(), s.end());
  return s;
}

//======== OpMap ===============
bool opmap_loaded = false;
std::map<std::string, std::pair<int, int> > opmap;

// should be synced with hintprocess
#define HINTPROCESS_MAX_OP_NUM 999998
const static int encode_op_length = (HINTPROCESS_MAX_OP_NUM + 2);

void
load_opmap(std::string fpath) {
  std::ifstream inf(fpath);
  if (!inf.good()) {
    std::cout << "Cannot find " << fpath << "\n"; 
    cheng_assert(false);
  }

  std::stringstream ss;
  ss << inf.rdbuf();
  auto contents = ss.str();

  // format: 
  // reqno*encode_op_length+opnum:type,seq_num;...
  std::vector<std::string> entries = str_explode(contents, ";");

  for (auto entry : entries) {
    if (trim(entry) == "") continue;
    auto kv = str_explode(entry, ":");
    cheng_assert(kv.size() == 2);
    // req-opnum
    // opid is in the form of rid-opnum

    int64_t rid_opnum = stoll(kv[0]);
    int64_t rid = rid_opnum / encode_op_length;
    int op_num = rid_opnum % encode_op_length;
    std::string opid = std::to_string(rid) + "-" + std::to_string(op_num);

    // type and seqnum
    auto info = str_explode(kv[1], ",");
    int type = stoi(info[0]);
    int seqnum = stoi(info[1]);

    opmap[opid] = std::make_pair(type, seqnum);
  }

  inf.close();
  opmap_loaded = true;
}

int
search_opmap(int rid, int opnum, int type) {
  START_SW(opmap_time);
  auto opid = std::to_string(rid) + "-" + std::to_string(opnum);
  // assert this rid-opnum exists
  //cheng_assert(opmap.find(opid) != opmap.end());
  if(opmap.find(opid) == opmap.end()) {
    std::cout << "Cannot find such operation in opmap: rid-opnum=" << opid << " type=" << type << "\n";
    cheng_assert(false);
  }
  auto pair = opmap[opid];
  // assert the type is the same
  if (!(type == TYPE_NONE || pair.first == type ||
    (pair.first == SQL_TXN && (type == SQL_READ|| type == SQL_WRITE)) ) ) {
    std::cout << "opid: " << opid << " is type " << type << 
     " , but should be " << pair.first << ", seqnum " << pair.second << "\n";
    cheng_assert(false);
  }
  // return the seqnum
  STOP_SW(opmap_time);
  return pair.second;
}

//=========MaxOp==============
bool maxop_loaded = false;
std::map<int,int> maxop_map;

void
load_maxop(std::string fpath) {
  std::ifstream inf(fpath);
  if (!inf.good()) {
    std::cout << "Cannot find " << fpath << "\n"; 
    cheng_assert(false);
  }

  std::stringstream ss;
  ss << inf.rdbuf();
  auto contents = ss.str();
  inf.close();

  // format: 
  // reqno-opnum:type,seq_num;...
  std::vector<std::string> entries = str_explode(contents, ",");

  for (auto entry : entries) {
    if (trim(entry) == "") continue;
    auto kv = str_explode(entry, ":");
    if (kv.size() != 2) {
      std::cout << "ill-format maxop entry: [" << entry << "]\n";
      cheng_assert(false);
    }
    // req-opnum
    int rid = stoi(kv[0]);
    int opnum = stoi(kv[1]);
    // should be no duplicated rid
    cheng_assert(maxop_map.find(rid) == maxop_map.end());
    maxop_map[rid] = opnum;
  }

  maxop_loaded = true;
}

bool
check_maxop(int rid,  int last_op_num) {
  cheng_assert(maxop_loaded);
  cheng_assert(maxop_map.find(rid) != maxop_map.end());
  if (maxop_map[rid] != last_op_num) {
    std::cout << "check_maxop, re-exec want to stop at opnum[" << last_op_num 
      << "],  however original maxop is [" << maxop_map[rid] << "]\n";
    cheng_assert(false);
  }
  return true;
}

//======== TTdb ===============
uint64_t max_int = LLONG_MAX; 
bool table_update_log_loaded = false;
std::map<std::string, std::vector<uint64_t> > table_update_log;

#ifdef CHENG_OPT_DB_UPDATE

static std::vector<string> str_split(std::string str, char delimiter){
  std::vector<string> ret;
  size_t start = 0, end = str.find(delimiter); 

  while (end != std::string::npos) {
    ret.push_back(str.substr(start, end-start));
    start = end + 1; 
    end = str.find(delimiter, start);
  }

  // the last one
  ret.push_back(str.substr(start));

  return ret;
}

void dump_table_update_log() {
  std::cout << "=============\n";
  for (auto it = table_update_log.begin(); it != table_update_log.end(); it++) {
    std::cout << it->first << ":\n    ";
    for (auto nit : it->second) {
      std::cout << nit << ", ";
    }
    std::cout << "\n";
  }
  std::cout << "=============\n";
}
#endif

// this will return the last update timestamp of such table
uint64_t
search_table_update_log (std::string tname, uint64_t cur_ts) {
#ifdef CHENG_OPT_DB_UPDATE
  tname = (tname[0]=='`' ? tname.substr(1,tname.length()-2) : tname);
  auto ts_arr = table_update_log[tname];
  if (ts_arr.size() == 0) {
    std::cout << "The table [" << tname << "] upadte log is empty\n";
    cheng_assert(false);
  }

  int size = ts_arr.size();
  for (int i=size-1; i>=0; i--) {
    if (cur_ts > ts_arr[i]) {
      return ts_arr[i];
    }
  }
  cheng_assert(false);
#endif
  return -1;
}

void
load_table_update_log(std::string fpath) {
#ifdef CHENG_OPT_DB_UPDATE
  std::ifstream inf(fpath);
  std::stringstream ss;
  ss << inf.rdbuf();
  auto contents = ss.str();

  auto table_arr = str_split(contents, '|');
  for (auto str_table : table_arr) {
    if (str_table == "") continue;

    auto name_times = str_split(str_table, ':');
    auto name = name_times[0];
    auto str_times = name_times[1];

    auto time_arr = str_split(str_times, ',');
    std::vector<uint64_t> ts_arr;
    ts_arr.push_back(0);
    for (int i = 0; i < time_arr.size(); i++) {
      if (time_arr[i]== "") continue;
      uint64_t ts = stoll(time_arr[i]);
      if (ts!=0) {
        ts_arr.push_back(ts);
      }
    }
    ts_arr.push_back(max_int);
    table_update_log[name] = ts_arr;
  }

  table_update_log_loaded = true;
#endif
}

//==========session=============
bool sess_log_loaded = false;
// {sess_id => vector of ("rid-opnum",  "write"|"read"), ...}
std::map<std::string, std::vector<std::pair<std::string, std::string> > >  sess_history;
// lookup table: rid-opnum => sess_id 
std::map<std::string, std::string> sess_id_map;

void
load_sess_log(std::string fpath) {
  std::ifstream inf(fpath);
  if (!inf.good()) {
    std::cout << "Cannot find " << fpath << "\n";
    cheng_assert(false);
  }

  std::stringstream ss;
  ss << inf.rdbuf();
  auto contents = ss.str();

  // format: 
  // rid #&# opnum #&# [write|read] #&# key |]|
  std::vector<std::string> entries = str_explode(contents, "|]|");

  for (auto entry : entries) {
    if (trim(entry) == "") continue;
    auto info = str_explode(entry, "#&#");
    //if (info.size() != 4) {
    //  std::cout << "[" << entry << "]\n";
    //}
    cheng_assert(info.size() == 4);
    auto rid = info[0];
    auto opnum = info[1];
    auto type = info[2];
    auto sid = info[3];
    auto opid = rid + "-" + opnum;

    if (sess_history.find(sid) == sess_history.end()) {
      std::vector<std::pair<std::string, std::string> > vec;
      sess_history[sid] = vec; 
    }
    sess_history[sid].push_back(std::make_pair(opid, type));
    cheng_assert(sess_id_map.find(opid) == sess_id_map.end());
    sess_id_map[opid] = sid;
  }

  sess_log_loaded = true;
  inf.close();
}


// NOTE: only called during PHP: session_start()
std::string
_sess_get_last_write(int64_t rid, int64_t opnum, std::string sess_id) {
  // check the type
  search_opmap(rid, opnum, REGISTER_READ);
  cheng_assert(sess_history.find(sess_id) != sess_history.end());

  std::pair<std::string, std::string> prev_w = std::make_pair("NULL","NULL");
  std::string cur_op_id = std::to_string(rid) + "-" + std::to_string(opnum);

  for (auto it : sess_history[sess_id]) {
    std::string op_id = it.first;
    std::string op_type = it.second;

    // find cur_op
    if (op_id == cur_op_id)
    {
      cheng_assert(op_type == "read");
      break;
    }

    // keep track previous write
    if (op_type == "write") {
      prev_w = it;
    }
  }

  // return name: S_key_rid_opnum
  std::string op_id = prev_w.first;
  std::string op_type = prev_w.second;
  if (op_id == "NULL") {
    // find nothing
    return "NULL";
  } else {
    cheng_assert(op_type == "write");
    auto info = str_explode(op_id, "-");
    return "S_" + sess_id + "_" + info[0] + "_" + info[1];
  }
} 

std::string
_sess_get_id(int64_t rid, int64_t opnum, bool check) {
  if (check) {
    // check the type
    search_opmap(rid, opnum, REGISTER_WRITE);
  }

  auto cur_op_id = std::to_string(rid) + "-" + std::to_string(opnum);
  if (sess_id_map.find(cur_op_id) == sess_id_map.end()) {
    return "NULL";
  } else {
    return sess_id_map[cur_op_id];
  }
}


//==========tt apc=============
bool apc_log_loaded = false;
// Note: for one key, the elements in apc_tt_vals[key] and apc_tt_seq[key]
// has one-to-one mapping. 
// key => [val1, val2, val3 ...]
std::map<std::string, std::vector<std::string> > apc_tt_vals;
// key => [seq1, seq2, seq3 ...]
std::map<std::string, std::vector<int> > apc_tt_seq;
// a set keeps all the failed ops
std::set<std::string> apc_fail_op_list;


void
load_apc_log(std::string fpath) {
  std::ifstream inf(fpath);
  if (!inf.good()) {
    std::cout << "Cannot find " << fpath << "\n";
    cheng_assert(false);
  }

  std::stringstream ss;
  ss << inf.rdbuf();
  auto contents = ss.str();
  inf.close();

  // format: 
  // store: 7, fetch 4, delete 5 
  // rid,opnum,{store|fetch|delete},key,[val|NULL|ret],[ttl|NULL|NULL],[ret|NULL|NULL]
  std::vector<std::string> key_entries = str_explode(contents, "]&#]");

  int seq_num = 0; // NOTE: matching number in OpMap
  for (auto key_values : key_entries) {
    auto kv = str_explode(key_values, "#&#");
    cheng_assert(kv.size() >= 4);
    auto optype = kv[2];
    std::string key = kv[3];

    if (optype == "store" || optype == "delete") {
      bool is_store = (optype == "store");
      cheng_assert(key != "");
      std::string val = "";
      if (is_store) {
        cheng_assert(kv.size() == 7);
        cheng_assert(kv[6] == "1"); // suppose always success
        val = kv[4];  
      } else {
        cheng_assert(kv.size() == 5);
        if (kv[4] == "0") {
          // if delete fails, add it to failed list
          auto op_id = kv[0] + "-" + kv[1];
          cheng_assert(apc_fail_op_list.find(op_id) == apc_fail_op_list.end());
          apc_fail_op_list.insert(op_id);
        }
      }
      // if first meet this key
      if (apc_tt_vals.find(key) == apc_tt_vals.end()) {
        cheng_assert(apc_tt_seq.find(key) == apc_tt_seq.end());
        vector<std::string> empty_str;
        apc_tt_vals[key] = empty_str; 
        vector<int> empty_int;
        apc_tt_seq[key] = empty_int;
      }
      apc_tt_vals[key].push_back(val);
      apc_tt_seq[key].push_back(seq_num);
    } else if (optype == "fetch") {
      // do nothing
    } else {
      std::cout << "ERROR: unimplement apc type: " << optype << "\n";
      cheng_assert(false);
    }
    seq_num++;
  }

  // validation
  cheng_assert(apc_tt_vals.size() == apc_tt_seq.size());
  for (auto it = apc_tt_vals.begin(); it != apc_tt_vals.end(); it++) {
    auto key = it->first;
    cheng_assert(apc_tt_seq.find(key) != apc_tt_seq.end());
    auto val_vec = it->second;
    cheng_assert(val_vec.size() == apc_tt_seq[key].size());
    // the apc_tt_seq should be sorted
    int prev = -1;
    for (auto seq : apc_tt_seq[key]) {
      cheng_assert(seq > prev);
      prev = seq;
    }
  }

  apc_log_loaded = true; 
}


inline uint64_t
get_last_smaller(const std::vector<uint64_t>& v, uint64_t x) {
  int first = 0, last = int(v.size()) - 1;
  while (first <= last)
  {
    int mid = (first + last) / 2;
    if (v[mid] >= x)
      last = mid - 1;
    else
      first = mid + 1;
  }
  return first - 1 < 0 ? -1 : v[first - 1];
}

inline int 
get_indx_last_smaller_or_equal(const std::vector<int>& v, int x) {
  int first = 0, last = int(v.size()) - 1;
  if (last < 0) {
    return -1;
  }

  // if first and last is within 1, we are good 
  while(first+1 < last) {
    int mid = (first + last) / 2;
    if (v[mid] > x) {
      last = mid;
    } else if (v[mid] < x) {
      first = mid;
    } else {
      first = last = mid;
      break;
    }
  }

  if (v[last] <= x) {
    return last;
  } else if (v[first] <= x) {
    return first;
  } else {
    return -1;
  }
}

// optimization: binary search
bool
search_tt_apc_log(std::string key, int64_t rid, int64_t opnum, std::string &result) {
  START_SW(apc_time);
  int seq_num = search_opmap(rid, opnum, KV_GET);
  // no such key, return ""
  if (apc_tt_seq.find(key) == apc_tt_seq.end()) {
    result = "VALNOTSET"; // FIXME
    STOP_SW(apc_time);
    return true;
  }

  int val_indx = get_indx_last_smaller_or_equal(apc_tt_seq[key], seq_num);
  if (val_indx == -1) {
    result = "VALNOTSET"; // FIXME
    STOP_SW(apc_time);
    return true;
  }

  result = apc_tt_vals[key][val_indx];
  STOP_SW(apc_time);
  return true;
}

void
debug_apc(std::string key, int64_t rid, int64_t opnum, std::string value, std::string reason) {
  std::cout << "key:" << key << " in " << rid << "-" << opnum << " with value:[" << value << "]\n"; 
  std::cout << "   reason: " << reason << "\n";
}

// for store/delete to check if at that point (rid,opnum), there is such an update
bool
match_apc_op(std::string key, int64_t rid, int64_t opnum, std::string value, int type, bool& is_failure) {
  START_SW(apc_time);
  int seq_num = search_opmap(rid, opnum, type);
  // cannot find the key
  if (apc_tt_seq.find(key) == apc_tt_seq.end()) {
    debug_apc(key,rid,opnum,value,"cannot find key");
    STOP_SW(apc_time);
    return false;
  }

  int val_indx = get_indx_last_smaller_or_equal(apc_tt_seq[key], seq_num);
  if (val_indx == -1) {
    debug_apc(key,rid,opnum,value,"cannot find val_indx=-1");
    STOP_SW(apc_time);
    return false;
  }

  // we cannot even get such an update operation
  if (seq_num != apc_tt_seq[key][val_indx]) {
    debug_apc(key,rid,opnum,value,"seq_num doesn't matching");
    STOP_SW(apc_time);
    return false;
  }
  // the values are different
  if (value != apc_tt_vals[key][val_indx]) {
    debug_apc(key,rid,opnum,value,"values are different");
    std::cout << "    should be: [" << apc_tt_vals[key][val_indx] << "]\n";
    STOP_SW(apc_time);
    return false;
  }
  STOP_SW(apc_time);

  // if it is one failure op
  if (apc_fail_op_list.find(std::to_string(rid) + "-" + std::to_string(opnum))
      != apc_fail_op_list.end()) {
    is_failure = true;
  } else {
    is_failure = false;
  }

  return true;
}

//======Initialization========

void thread_init () {
  // reset the flag
  is_resource_req = false;
  if (cheng_verification) {
    veri_buf.str("");
  }
  cheng_assert(php_code_running == false);
  php_code_running = true;
  batch_size = 1;
}

void thread_end () {
  cheng_assert(php_code_running == true);
  php_code_running = false;
  batch_size = 1;
}

//============================

#ifdef CHENG_CYCLE_WAR_TUNING

int rec_counter = 0;

DEF_TSC_SW(ins_time);
DEF_TSC_SW(ins_time_1);
DEF_TSC_SW(ins_time_2);
DEF_TSC_SW(ins_time_3);
DEF_TSC_SW(ins_time_4);

//#define I_START START_SW(ins_time)
//#define I_END   STOP_SW(ins_time)

#define I_START(n) START_SW(ins_time_##n)
#define I_END(n)   STOP_SW(ins_time_##n)

#define I_START_ \
  do {\
    if (rec_counter == 0) {\
      START_SW(ins_time);\
    }\
    rec_counter++;\
  } while(0)

#define I_END_  \
  do {\
    rec_counter--;\
    if (rec_counter == 0) {\
      STOP_SW(ins_time);\
    }\
  } while(0)

#endif

DEF_SW(db_query);
#ifdef CHENG_TIME_EVAL
thread_local struct timeval vm_start_t;
thread_local int64_t concat_time;



DEF_SW(req_time);
DEF_SW(multi_time);

  #ifdef CHENG_COUNT_INS
    // CHENG_COUNT_INS: count multi_ins number
    //  call get_ins_counter/get_multi_ins_counter to get this

    #define START do {multi_ins_counter++;} while(0)
    #define END  ((void)0) 
  
  #else 
    // normal CHENG_TIME_EVAL: calculate multi_ins time
  
    #define START START_SW(multi_time)
    #define END   STOP_SW(multi_time)
  
  #endif

std::mutex t_mtx;
#else

#define START ((void)0)
#define END   ((void)0)

#endif

//==========DEBUG================
#ifdef CHENG_INS_ONLY_DEBUG 
std::ofstream debug_log;

static void
openDebugLog() {
  debug_log.rdbuf()->pubsetbuf(0,0);
  //debug_log.open("/tmp/debug.log", std::ofstream::app);
  debug_log.open("/tmp/debug.log");
}

static void
closeDebugLog() {
  debug_log.close();

}

void write_to_debug_log(std::string symbol, std::string log) {
  debug_log << "    [" << symbol << "] " <<  log << "\n";
}
#endif

void cheng_fail(std::string file, int line) {
    veri_buf.str("");
    veri_buf.str("Orochi doesn't support this case");

#ifdef CHENG_INS_DEBUG
    debug_log << "file: " << file << " loc: " << line << "\n";
#endif
    if (without_crash) {
#ifdef CHENG_INS_DEBUG
      debug_log << "cheng_assert false, go without_crash\n";
#endif
      HHVM_FN(debug_print_backtrace)(); 
      std::cout << "***FAIL*** on file: " << file << " loc: " << line << "\n";
      raise_error("Orochi does not support");
      //throw ExitException(31);
    } else {
      //HHVM_FN(debug_print_backtrace)(); 
      std::ofstream f("/tmp/xx");
      f << "***FAIL*** on file: " << file << " loc: " << line << "\n";
      f.close();

      std::cout << "***FAIL*** on file: " << file << " loc: " << line << "\n";

      always_assert(false);
    }
}

static inline void printFullStack (std::string prefix) {
#ifdef CHENG_DEBUG_STACK 
  debug_log << "  <<-----STACK------\n";
  for (int i = 0; i < vmStack().count(); i++) {
    debug_log << prefix << "    stack[" << i << "]("
      << (vmStack().count() - i) << "): " << vmStack().indTV(i)->pretty()
      << "  addr:" << vmStack().indTV(i) << "\n";
  }
  debug_log << "  >>---------------\n";
#endif
}

#ifdef CHENG_PRINT_CF

#undef AS_CF
#define AS_CF     print_cf() 

static inline void print_ins(std::string name) {}

static inline void print_cf() {
  debug_log << "=-= [" << ins_counter++ << "] JMP";
  auto func = vmfp()->m_func;
  if (func!=nullptr) {
    debug_log <<  "     (" << func->fullName()->toCppString() << ")";
  }
  auto vm = &*g_context;
  if (vm!=nullptr) { 
    debug_log << "  { " << vm->getContainingFileName()->toCppString()
      << " : " << vm->getLine() << "}";
  }
  debug_log << " =-=\n";
}


#else

static inline void print_ins (std::string name) {
#ifdef CHENG_INS_ONLY_DEBUG
  if (should_count) {
    //auto tid = std::this_thread::get_id();
    debug_log << "=-= [" << ins_counter++ << "] " << name;
    auto func = vmfp()->m_func;
    if (func!=nullptr) {
      debug_log <<  "     (" << func->fullName()->toCppString() << ")";
    }
    auto vm = &*g_context;
    if (vm!=nullptr) { 
      debug_log << "  { " << vm->getContainingFileName()->toCppString()
        << " : " << vm->getLine() << "}";
    }
    debug_log << " SM:[" << nested_ins_level << "]";
    debug_log << " =-=\n";
  }
#endif
}
#endif

std::unordered_set<std::string> bypass_func = {
  // API:
  "add_multi",
  "is_multi",
  "is_single_mode_on",
  "split_multi",
  "merge_multi",
  "array_set_multi",
  "array_sys_unset",
  "veri_dump_output",
  "ttdb_query",
  "ttdb_query_mysqli_result",
  "loop_var_capture",
  "loop_var_end",
  "MIC_to_MC",
  "MC_to_MIC",
  "getIthVal",
  // support multivalue args
  "print_r",
  "print_p",
  "session_decode",
  "func_get_args",
  "preg_replace_callback",
  "current",
  "array_key_exists",
  // db
  "multi_mysql_free_result",
  "ttdb_multi_query",
  "multi_mysql_fetch_object",
  "multi_mysql_fetch_array",
  "multi_mysql_data_seek",
  "multi_mysql_field_seek",
  "multi_mysql_fetch_field",
  // apc
  "oro_apc_store_check",
  "oro_apc_fetch_check",
  "oro_apc_delete_check",
  "oro_apc_inc_check",
  "oro_apc_dec_check",
  // for the closure/object with multivalue
  "is_callable",
  "method_exists",
  "get_class"
};

ALWAYS_INLINE static bool
isBypassFunc(const char* name) {
  std::string fname(name);
  auto found = bypass_func.find(fname);
  if (found == bypass_func.end()) {
    return false;
  } else {
    return true;
  }
}

ALWAYS_INLINE static bool
isSystemArr(TypedValue* tv) {
  if (tv->m_type == KindOfRef) {
    tv = tvToCell(tv);
  }
  if (tv->m_type == KindOfArray && tv->m_data.parr->withMulti()) {
    return true; 
  }
  return false; 
}

static inline TypedValue* tvBoxMulti(TypedValue* boxee);
static TypedValue splitElements(TypedValue* orig, int size) {
  TypedValue ret;

  switch (orig->m_type) {
  case KindOfResource:
  case KindOfMulti:
  case KindOfClass:
    std::cout << "Do not support to split these elements\n";
    cheng_assert(false);
    break;
  case KindOfRef:
    // deref, split it, and return the multi-ref
    {
      TypedValue *cell = orig->m_data.pref->tv();
      // if the ref is point to single element, split it!
      // And this will generate ref->multi 
      if (cell->m_type != KindOfMulti) {
        cheng_assert(cell->m_type != KindOfRef); // cannot be nested ref
        TypedValue tmp = splitElements(cell, size);
        // make the multi-val to ref
        tvBoxMulti(&tmp);
        tvCopy(tmp, *cell);
      } // or itself is a multi-val
      ret = *cell;
    }
  case KindOfInt64:
  case KindOfBoolean:
  case KindOfDouble:
  case KindOfUninit:
  case KindOfNull:
    ret = MultiVal::makeMultiVal();
    for (int i=0; i<size; i++) {
      ret.m_data.pmulti->addValue(*orig);
    }
    break;
  case KindOfStaticString:
  case KindOfString:
    ret = MultiVal::makeMultiVal();
    for (int i=0; i<size; i++) {
      ret.m_data.pmulti->addValue(*orig);
    }
    break;
  case KindOfArray:
    ret = MultiVal::splitArray(*orig, size);
    break;
  case KindOfObject:
    ret = MultiVal::splitObject(*orig, size);
    break;
  }

  return ret;
}

static void apply2Elem (TypedValue* tv, std::function<void (TypedValue*)> f) {
  TypedValue * cell = nullptr;
  switch (tv->m_type) {
  case KindOfRef:
    cell = tvToCell(tv);
    apply2Elem(cell, f);
    break;
  case KindOfInt64:
  case KindOfBoolean:
  case KindOfDouble:
  case KindOfUninit:
  case KindOfNull:
  case KindOfStaticString:
  case KindOfString:
    f(tv);
    break;
  case KindOfResource:
  case KindOfMulti:
  case KindOfClass:
    f(tv);
    break;
  case KindOfArray:
    f(tv);
    //for (ArrayIter iter(*tv); iter; ++iter) {
    //  apply2Elem((TypedValue*)iter.nvSecond(), f);
    //}
    break;
  case KindOfObject:
    // FIXME: I do not go through all the elements in object
    f(tv);
    break;
  default:
    // for unknown element, we don't really care
    break;
  }
}

static void iterGlobalVar( std::function<void (TypedValue*)> f) {
  auto globals = g_context->m_globalVarEnv;
  Array all_var = globals->getDefinedVariables();
  for (ArrayIter iter(all_var); iter; ++iter) {
    apply2Elem((TypedValue*)iter.nvSecond(), f);
  }
}

// FIXME: this is not enough, apparently
static void iterLocalVar ( std::function<void (TypedValue*)> f) {
  auto fp_ptr = vmfp();
  do {
    // local variables
    auto num_local = fp_ptr->func()->numLocals();
    for (int i = 0; i < num_local; i++) {
      TypedValue* local = frame_local(fp_ptr, i);
#ifdef CHENG_INS_DEBUG
    debug_log << "    handling " << local->pretty() << "\n"; 
#endif
      apply2Elem(local,f);
    }
    // return values; NOTE: all the frames on the stack are not returned yet
    // apply2Elem(&fp_ptr->m_r, f);

    // maybe new obj value
    if (fp_ptr->isFromFPushCtor()) {
      auto prev_tv_of_fp = (TypedValue*)(fp_ptr+1);
      apply2Elem(prev_tv_of_fp, f);
    }

    // prev call frame
    fp_ptr = fp_ptr->m_sfp;
  } while (fp_ptr!=nullptr);
}

static void dumpTV(TypedValue *tv) {
  int8_t *b_ptr = (int8_t*)tv;
  std::cout << "    64: " << *(int64_t *)b_ptr << "\n"
    << "    8:  " << (int)b_ptr[8] << "\n"
    << "    8:  " << (int)b_ptr[9] << "\n"
    << "    8:  " << (int)b_ptr[10] << "\n"
    << "    8:  " << (int)b_ptr[11] << "\n"
    << "    32: " << *(int32_t *)&b_ptr[12] << "\n";
}

// NOTE: this is return Cell instead of Cell*
inline Cell tvMayMultiToCell(TypedValue* tv) {
  cheng_assert(tv->m_type == KindOfMulti);
  if (tv->m_data.pmulti->getType() == KindOfRef) {
    TypedValue ret = MultiVal::makeMultiVal();
    for (auto it : *tv->m_data.pmulti) {
      ret.m_data.pmulti->addValue(*tvToCell(it));
    }
    return ret;
  } else {
    return *tv;
  }
}

static bool 
is_loop_exit(TypedValue *val, int index, bool jump_forward, Op op) {
  cheng_assert(loop_capture_mode);
  cheng_assert(val->m_type == KindOfMulti);

  auto tv = val->m_data.pmulti->getByVal(index);
  bool equal_zero = false;
  if (tv->m_type == KindOfInt64 || tv->m_type == KindOfBoolean) {
    equal_zero = (tv->m_data.num == 0);
  } else {
    equal_zero = !toBoolean(cellAsCVarRef(*tv));
  }

  // first check the op
  bool jump = false;
  if (op == OpJmpZ) {
    jump = equal_zero;
  } else if (op == OpJmpNZ) {
    jump = !equal_zero;
  } else {
    cheng_assert(false);
  }

  if ( (jump && jump_forward) || 
       (!jump && !jump_forward) )
  {
    return true;
  } else {
    return false;
  }
}

//--------Performance Replacement-----------
// There are good software enginering function,
// but we want PERFORMANCE!!!

// See multi-val.cpp
ALWAYS_INLINE struct TypedValue 
in_makeMultiVal() {
  TypedValue v;
  v.m_type = KindOfMulti;
  v.m_data.pmulti = new (MM().smartMallocSizeLogged(sizeof(MultiVal)))
    MultiVal(); 
  return v;
}

// See multi-val.cpp
ALWAYS_INLINE struct TypedValue 
in_makeMultiVal(int size, DataType t) {
  TypedValue v;
  v.m_type = KindOfMulti;
  v.m_data.pmulti = new (MM().smartMallocSizeLogged(sizeof(MultiVal)))
    MultiVal(size); 
  v.m_data.pmulti->setType(t);
  return v;
}

static ALWAYS_INLINE void
castToStringInPlace(TypedValue* v) {
  cheng_assert(v->m_type == KindOfStaticString);
  auto str_ptr = v->m_data.pstr;
  v->m_type = KindOfString;
  v->m_data.pstr = StringData::Make(str_ptr, CopyString);
  tvRefcountedIncRef(v); 
}

ALWAYS_INLINE void
in_adjust_type(MultiVal* mv) {
  int size = mv->valSize();

  for (int i = 0; i < size; i++) {
    auto m_multi_type = mv->getType();
    auto adding_val = mv->getByVal(i);

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
      HHVM_FN(print_r)(tvAsVariant(&tmp));
      std::cout << "\nAdding element:\n    " << adding_val->pretty() << "\n";
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
}


//---------------helper functions, others may use------------
bool cheng_cellToBool(Cell *cell) {
  switch (cell->m_type) {
    case KindOfUninit:
    case KindOfNull:          return false;
    case KindOfBoolean:       return cell->m_data.num;
    case KindOfInt64:         return cell->m_data.num != 0;
    case KindOfDouble:        return cell->m_data.dbl != 0;
    case KindOfStaticString:
    case KindOfString:        return cell->m_data.pstr->toBoolean();
    case KindOfArray:         return !!cell->m_data.parr->size();
    case KindOfObject:        return cell->m_data.pobj->toBoolean();
    case KindOfResource:      return cell->m_data.pres->o_toBoolean();
    case KindOfMulti:         cheng_assert(false); return false;
    case KindOfRef:
    case KindOfClass:         break;
  }
  not_reached();
}

//===========================================
//===========================================

// Identifies the set of return helpers that we may set m_savedRip to in an
// ActRec.
static bool isReturnHelper(void* address) {
  auto tcAddr = reinterpret_cast<jit::TCA>(address);
  auto& u = mcg->tx().uniqueStubs;
  return tcAddr == u.retHelper ||
         tcAddr == u.genRetHelper ||
         tcAddr == u.retInlHelper ||
         tcAddr == u.callToExit;
}

ActRec* ActRec::sfp() const {
  // Native frame? (used by enterTCHelper)
  if (UNLIKELY(((uintptr_t)m_sfp - s_stackLimit) < s_stackSize)) {
    return nullptr;
  }

  return m_sfp;
}

void ActRec::setReturn(ActRec* fp, PC pc, void* retAddr) {
  assert(fp->func()->contains(pc));
  assert(isReturnHelper(retAddr));
  m_sfp = fp;
  m_savedRip = reinterpret_cast<uintptr_t>(retAddr);
  m_soff = Offset(pc - fp->func()->getEntry());
}

void ActRec::setReturnVMExit() {
  assert(isReturnHelper(mcg->tx().uniqueStubs.callToExit));
  m_sfp = nullptr;
  m_savedRip = reinterpret_cast<uintptr_t>(mcg->tx().uniqueStubs.callToExit);
  m_soff = 0;
}

bool
ActRec::skipFrame() const {
  return m_func && m_func->isSkipFrame();
}

template <>
Class* arGetContextClassImpl<false>(const ActRec* ar) {
  if (ar == nullptr) {
    return nullptr;
  }
  return ar->m_func->cls();
}

template <>
Class* arGetContextClassImpl<true>(const ActRec* ar) {
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
  return ar->m_func->cls();
}

void frame_free_locals_no_hook(ActRec* fp) {
  frame_free_locals_inl_no_hook<false>(fp, fp->func()->numLocals());
}

const StaticString s_call_user_func("call_user_func");
const StaticString s_call_user_func_array("call_user_func_array");
const StaticString s_stdclass("stdclass");
const StaticString s___call("__call");
const StaticString s___callStatic("__callStatic");
const StaticString s_file("file");
const StaticString s_line("line");

///////////////////////////////////////////////////////////////////////////////

//=============================================================================
// Miscellaneous decoders.

inline const char* prettytype(int) { return "int"; }
inline const char* prettytype(long) { return "long"; }
inline const char* prettytype(double) { return "double"; }
inline const char* prettytype(unsigned) { return "unsigned"; }
inline const char* prettytype(OODeclExistsOp) { return "OpDeclExistsOp"; }
inline const char* prettytype(FatalOp) { return "FatalOp"; }
inline const char* prettytype(IsTypeOp) { return "IsTypeOp"; }
inline const char* prettytype(SetOpOp) { return "SetOpOp"; }
inline const char* prettytype(IncDecOp) { return "IncDecOp"; }
inline const char* prettytype(ObjMethodOp) { return "ObjMethodOp"; }
inline const char* prettytype(BareThisOp) { return "BareThisOp"; }
inline const char* prettytype(InitPropOp) { return "InitPropOp"; }
inline const char* prettytype(SilenceOp) { return "SilenceOp"; }

// load a T value from *pc without incrementing
template<class T> T peek(PC pc) {
  T v;
  std::memcpy(&v, pc, sizeof v); // should compile to a load
  ONTRACE(2, Trace::trace("decode:     Immediate %s %" PRIi64"\n",
          prettytype(v), int64_t(v)));
  return v;
}

template<class T> T decode(PC& pc) {
  auto v = peek<T>(pc);
  pc += sizeof(T);
  return v;
}

inline int32_t decode_iva(PC& pc) {
  auto v = decodeVariableSizeImm(&pc);
  ONTRACE(2, Trace::trace("decode:     Immediate int32 %" PRIi64"\n",
          int64_t(v)));
  return v;
}

StringData* decode_litstr(PC& pc) {
  auto id = decode<Id>(pc);
  return vmfp()->m_func->unit()->lookupLitstrId(id);
}

inline int32_t decode_la(PC& pc) {
  return decode_iva(pc);
}

inline int32_t decode_ia(PC& pc) {
  return decode_iva(pc);
}

template<class T> T decode_oa(PC& pc) {
  return decode<T>(pc);
}

//=============================================================================
// Miscellaneous helpers.

static inline Class* frameStaticClass(ActRec* fp) {
  if (fp->hasThis()) {
    // cheng-hack:
    return fp->getThisDefault()->getVMClass();
  } else if (fp->hasClass()) {
    return fp->getClass();
  } else {
    return nullptr;
  }
}

static Offset pcOff() {
  return vmfp()->m_func->unit()->offsetOf(vmpc());
}

//=============================================================================
// VarEnv.

const StaticString s_GLOBALS("GLOBALS");

VarEnv::VarEnv()
  : m_nvTable()
  , m_extraArgs(nullptr)
  , m_depth(0)
  , m_global(true)
{
  TRACE(3, "Creating VarEnv %p [global scope]\n", this);
  assert(!g_context->m_globalVarEnv);
  g_context->m_globalVarEnv = this;
  auto globals = new (MM().objMalloc(sizeof(GlobalsArray)))
                 GlobalsArray(&m_nvTable);
  auto globalArray = make_tv<KindOfArray>(globals->asArrayData());
  m_nvTable.set(s_GLOBALS.get(), &globalArray);
}

VarEnv::VarEnv(ActRec* fp, ExtraArgs* eArgs)
  : m_nvTable(fp)
  , m_extraArgs(eArgs)
  , m_depth(1)
  , m_global(false)
{
  TRACE(3, "Creating lazily attached VarEnv %p on stack\n", this);
}

VarEnv::VarEnv(const VarEnv* varEnv, ActRec* fp)
  : m_nvTable(varEnv->m_nvTable, fp)
  , m_extraArgs(varEnv->m_extraArgs ? varEnv->m_extraArgs->clone(fp) : nullptr)
  , m_depth(1)
  , m_global(false)
{
  assert(varEnv->m_depth == 1);
  assert(!varEnv->m_global);

  TRACE(3, "Cloning VarEnv %p to %p\n", varEnv, this);
}

VarEnv::~VarEnv() {
  TRACE(3, "Destroying VarEnv %p [%s]\n",
           this,
           isGlobalScope() ? "global scope" : "local scope");
  assert(isGlobalScope() == (g_context->m_globalVarEnv == this));

  if (isGlobalScope()) {
    /*
     * When detaching the global scope, we leak any live objects (and
     * let the smart allocator clean them up).  This is because we're
     * not supposed to run destructors for objects that are live at
     * the end of a request.
     */
    m_nvTable.leak();
  }
}

VarEnv* VarEnv::createGlobal() {
  return smart_new<VarEnv>();
}

VarEnv* VarEnv::createLocal(ActRec* fp) {
  return smart_new<VarEnv>(fp, fp->getExtraArgs());
}

VarEnv* VarEnv::clone(ActRec* fp) const {
  return smart_new<VarEnv>(this, fp);
}

void VarEnv::suspend(const ActRec* oldFP, ActRec* newFP) {
  m_nvTable.suspend(oldFP, newFP);
}

void VarEnv::enterFP(ActRec* oldFP, ActRec* newFP) {
  TRACE(3, "Attaching VarEnv %p [%s] %d fp @%p\n",
           this,
           isGlobalScope() ? "global scope" : "local scope",
           int(newFP->m_func->numNamedLocals()), newFP);
  assert(newFP);
  if (oldFP == nullptr) {
    assert(isGlobalScope() && m_depth == 0);
  } else {
    assert(m_depth >= 1);
    assert(g_context->getPrevVMStateUNSAFE(newFP) == oldFP);
    m_nvTable.detach(oldFP);
  }

  m_nvTable.attach(newFP);
  m_depth++;
}

void VarEnv::exitFP(ActRec* fp) {
  TRACE(3, "Detaching VarEnv %p [%s] @%p\n",
           this,
           isGlobalScope() ? "global scope" : "local scope",
           fp);
  assert(fp);
  assert(m_depth > 0);

  m_depth--;
  m_nvTable.detach(fp);

  if (m_depth == 0) {
    // don't free global VarEnv
    if (!isGlobalScope()) {
      smart_delete(this);
    }
  } else {
    m_nvTable.attach(g_context->getPrevVMStateUNSAFE(fp));
  }
}

void VarEnv::set(const StringData* name, const TypedValue* tv) {
  m_nvTable.set(name, tv);
}

void VarEnv::bind(const StringData* name, TypedValue* tv) {
  m_nvTable.bind(name, tv);
}

void VarEnv::setWithRef(const StringData* name, TypedValue* tv) {
  if (tv->m_type == KindOfRef) {
    bind(name, tv);
  } else {
    set(name, tv);
  }
}

TypedValue* VarEnv::lookup(const StringData* name) {
  return m_nvTable.lookup(name);
}

TypedValue* VarEnv::lookupAdd(const StringData* name) {
  return m_nvTable.lookupAdd(name);
}

bool VarEnv::unset(const StringData* name) {
  m_nvTable.unset(name);
  return true;
}

static const StaticString s_closure_var("0Closure");

Array VarEnv::getDefinedVariables() const {
  Array ret = Array::Create();

  NameValueTable::Iterator iter(&m_nvTable);
  for (; iter.valid(); iter.next()) {
    auto const sd = iter.curKey();
    auto const tv = iter.curVal();
    // Closures have an interal 0Closure variable (see emitter.cpp:6539)
    if (s_closure_var.equal(sd)) {
      continue;
    }
    if (tvAsCVarRef(tv).isReferenced()) {
      ret.setWithRef(StrNR(sd).asString(), tvAsCVarRef(tv));
    } else {
      ret.add(StrNR(sd).asString(), tvAsCVarRef(tv));
    }
  }
  // ksort the array, result is independent of the hashtable implementation.
  ArrayData* sorted = ret.get()->escalateForSort();
  sorted->incRefCount();
  sorted->ksort(0, true);
  if (sorted != ret.get()) {
    ret = sorted;
  }
  sorted->decRefCount();

  return ret;
}

TypedValue* VarEnv::getExtraArg(unsigned argInd) const {
  return m_extraArgs->getExtraArg(argInd);
}

//=============================================================================

ExtraArgs::ExtraArgs() {}
ExtraArgs::~ExtraArgs() {}

void* ExtraArgs::allocMem(unsigned nargs) {
  assert(nargs > 0);
  return smart_malloc(sizeof(TypedValue) * nargs + sizeof(ExtraArgs));
}

ExtraArgs* ExtraArgs::allocateCopy(TypedValue* args, unsigned nargs) {
  void* mem = allocMem(nargs);
  ExtraArgs* ea = new (mem) ExtraArgs();

  /*
   * The stack grows downward, so the args in memory are "backward"; i.e. the
   * leftmost (in PHP) extra arg is highest in memory.
   */
  std::reverse_copy(args, args + nargs, &ea->m_extraArgs[0]);
  return ea;
}

ExtraArgs* ExtraArgs::allocateUninit(unsigned nargs) {
  void* mem = ExtraArgs::allocMem(nargs);
  return new (mem) ExtraArgs();
}

void ExtraArgs::deallocate(ExtraArgs* ea, unsigned nargs) {
  assert(nargs > 0);

  for (unsigned i = 0; i < nargs; ++i) {
    tvRefcountedDecRef(ea->m_extraArgs + i);
  }
  ea->~ExtraArgs();
  smart_free(ea);
}

void ExtraArgs::deallocate(ActRec* ar) {
  const int numExtra = ar->numArgs() - ar->m_func->numNonVariadicParams();
  deallocate(ar->getExtraArgs(), numExtra);
}

ExtraArgs* ExtraArgs::clone(ActRec* ar) const {
  const int numExtra = ar->numArgs() - ar->m_func->numParams();
  auto ret = allocateUninit(numExtra);
  for (int i = 0; i < numExtra; ++i) {
    tvDupFlattenVars(&m_extraArgs[i], &ret->m_extraArgs[i]);
  }
  return ret;
}

TypedValue* ExtraArgs::getExtraArg(unsigned argInd) const {
  return const_cast<TypedValue*>(&m_extraArgs[argInd]);
}

//=============================================================================
// Stack.

// Store actual stack elements array in a thread-local in order to amortize the
// cost of allocation.
class StackElms {
 public:
  StackElms() : m_elms(nullptr) {}
  ~StackElms() {
    flush();
  }
  TypedValue* elms() {
    if (m_elms == nullptr) {
      // RuntimeOption::EvalVMStackElms-sized and -aligned.
      size_t algnSz = RuntimeOption::EvalVMStackElms * sizeof(TypedValue);
      if (posix_memalign((void**)&m_elms, algnSz, algnSz) != 0) {
        throw std::runtime_error(
          std::string("VM stack initialization failed: ") +
                      folly::errnoStr(errno).c_str());
      }

      madvise(m_elms, algnSz, MADV_DONTNEED);
      numa_bind_to(m_elms, algnSz, s_numaNode);
    }
    return m_elms;
  }
  void flush() {
    if (m_elms != nullptr) {
      free(m_elms);
      m_elms = nullptr;
    }
  }
 private:
  TypedValue* m_elms;
};
IMPLEMENT_THREAD_LOCAL(StackElms, t_se);

const int Stack::sSurprisePageSize = sysconf(_SC_PAGESIZE);
// We reserve the bottom page of each stack for use as the surprise
// page, so the minimum useful stack size is the next power of two.
const uint Stack::sMinStackElms = 2 * sSurprisePageSize / sizeof(TypedValue);

void Stack::ValidateStackSize() {
  if (RuntimeOption::EvalVMStackElms < sMinStackElms) {
    throw std::runtime_error(str(
      boost::format("VM stack size of 0x%llx is below the minimum of 0x%x")
        % RuntimeOption::EvalVMStackElms
        % sMinStackElms));
  }
  if (!folly::isPowTwo(RuntimeOption::EvalVMStackElms)) {
    throw std::runtime_error(str(
      boost::format("VM stack size of 0x%llx is not a power of 2")
        % RuntimeOption::EvalVMStackElms));
  }
}

Stack::Stack()
  : m_elms(nullptr), m_top(nullptr), m_base(nullptr) {
}

Stack::~Stack() {
  requestExit();
}

void
Stack::requestInit() {
  m_elms = t_se->elms();
  // Burn one element of the stack, to satisfy the constraint that
  // valid m_top values always have the same high-order (>
  // log(RuntimeOption::EvalVMStackElms)) bits.
  m_top = m_base = m_elms + RuntimeOption::EvalVMStackElms - 1;

  // Because of the surprise page at the bottom of the stack we lose an
  // additional 256 elements which must be taken into account when checking for
  // overflow.
  UNUSED size_t maxelms =
    RuntimeOption::EvalVMStackElms - sSurprisePageSize / sizeof(TypedValue);
  assert(!wouldOverflow(maxelms - 1));
  assert(wouldOverflow(maxelms));
  // cheng-hack: open the debug log
  thread_init();
  flush_clock_cpu_time();
#ifdef CHENG_INS_ONLY_DEBUG
  openDebugLog();
#endif
#ifdef CHENG_TIME_EVAL
  START_SW(req_time);
  ins_counter=0;
  multi_ins_counter=0;
#endif
  if (UNLIKELY(!table_update_log_loaded)) {
    load_table_update_log("/tmp/table_update.log");
  }
  if (UNLIKELY(!apc_log_loaded)) {
    load_apc_log("/tmp/apc.log");
  }
  if (UNLIKELY(!sess_log_loaded)) {
    load_sess_log("/tmp/sess.log");
  }
  if (UNLIKELY(!opmap_loaded)) {
    load_opmap("/tmp/opmap.mem");
  }
  if (UNLIKELY(!maxop_loaded)) {
    load_maxop("/tmp/maxop.log");
  }
  // turn off single_mode_on
  nested_ins_level = 0;
  nested_ins_level = false;
#ifdef CHENG_INS_ONLY_DEBUG
    debug_log << "reqinit: single_mode_on = false\n";
#endif
  single_mode_cur_iter = -1;
  single_mode_size = -1;
  CLEAR_CLASSIFY_INS_COUNTER;
}

void
Stack::requestExit() {
  m_elms = nullptr;
}

void flush_evaluation_stack() {
  if (vmStack().isAllocated()) {
    // For RPCRequestHandler threads, the ExecutionContext can stay
    // alive across requests, but its always ok to kill it between
    // requests, so do so now
    RPCRequestHandler::cleanupState();
  }

  if (!g_context.isNull()) {
    /*
     * It is possible to create a new thread, but then not use it
     * because another thread became available and stole the job.
     * If that thread becomes idle, it will have a g_context, and
     * some smart allocated memory
     */
    hphp_memory_cleanup();
  }
  MM().flush();

  if (!t_se.isNull()) {
    t_se->flush();
  }
  RDS::flush();

  always_assert(MM().empty());
}

static std::string toStringElm(const TypedValue* tv) {
  std::ostringstream os;

  if (tv->m_type < kMinDataType || tv->m_type > kMaxDataType) {
    os << " ??? type " << tv->m_type << "\n";
    return os.str();
  }
  if (IS_REFCOUNTED_TYPE(tv->m_type) && tv->m_data.parr->getCount() <= 0 &&
      !tv->m_data.parr->isStatic()) {
    // OK in the invoking frame when running a destructor.
    os << " ??? inner_count " << tv->m_data.parr->getCount() << " ";
    return os.str();
  }

  auto print_count = [&] {
    if (tv->m_data.parr->isStatic()) {
      os << ":c(static)";
    } else {
      os << ":c(" << tv->m_data.parr->getCount() << ")";
    }
  };

  switch (tv->m_type) {
  case KindOfRef:
    os << "V:(";
    os << "@" << tv->m_data.pref;
    os << toStringElm(tv->m_data.pref->tv());
    os << ")";
    return os.str();
  case KindOfClass:
    os << "A:";
    break;
  case KindOfUninit:
  case KindOfNull:
  case KindOfBoolean:
  case KindOfInt64:
  case KindOfDouble:
  case KindOfStaticString:
  case KindOfString:
  case KindOfArray:
  case KindOfObject:
  case KindOfResource:
    os << "C:";
    break;
  case KindOfMulti:
    os << "M:";
    break;
  }

  do {
    switch (tv->m_type) {
    case KindOfUninit:
      os << "Uninit";
      continue;
    case KindOfNull:
      os << "Null";
      continue;
    case KindOfBoolean:
      os << (tv->m_data.num ? "True" : "False");
      continue;
    case KindOfInt64:
      os << "0x" << std::hex << tv->m_data.num << std::dec;
      continue;
    case KindOfDouble:
      os << tv->m_data.dbl;
      continue;
    case KindOfStaticString:
    case KindOfString:
      {
        int len = tv->m_data.pstr->size();
        bool truncated = false;
        if (len > 128) {
          len = 128;
          truncated = true;
        }
        os << tv->m_data.pstr;
        print_count();
        os << ":\""
           << escapeStringForCPP(tv->m_data.pstr->data(), len)
           << "\"" << (truncated ? "..." : "");
      }
      continue;
    case KindOfArray:
      assert(check_refcount_nz(tv->m_data.parr->getCount()));
      os << tv->m_data.parr;
      print_count();
      os << ":Array";
      continue;
    case KindOfObject:
      assert(check_refcount_nz(tv->m_data.pobj->getCount()));
      os << tv->m_data.pobj;
      print_count();
      os << ":Object("
         << tv->m_data.pobj->getClassName().get()->data()
         << ")";
      continue;
    case KindOfResource:
      assert(check_refcount_nz(tv->m_data.pres->getCount()));
      os << tv->m_data.pres;
      print_count();
      os << ":Resource("
         << const_cast<ResourceData*>(tv->m_data.pres)
              ->o_getClassName().get()->data()
         << ")";
      continue;
    case KindOfRef:
      break;
    case KindOfClass:
      os << tv->m_data.pcls
         << ":" << tv->m_data.pcls->name()->data();
      continue;
    // TODO(cheng): need a implementation
    case KindOfMulti:
      os << "multivalue!";
      continue;
    }
    not_reached();
  } while (0);

  return os.str();
}

static std::string toStringIter(const Iter* it, bool itRef) {
  if (itRef) return "I:MutableArray";

  // TODO(#2458166): it might be a CufIter, but we're just lucky that
  // the bit pattern for the CufIter is going to have a 0 in
  // getIterType for now.
  switch (it->arr().getIterType()) {
  case ArrayIter::TypeUndefined:
    return "I:Undefined";
  case ArrayIter::TypeArray:
    return "I:Array";
  case ArrayIter::TypeIterator:
    return "I:Iterator";
  }
  assert(false);
  return "I:?";
}

/*
 * Return true if Offset o is inside the protected region of a fault
 * funclet for iterId, otherwise false. itRef will be set to true if
 * the iterator was initialized with MIterInit*, false if the iterator
 * was initialized with IterInit*.
 */
static bool checkIterScope(const Func* f, Offset o, Id iterId, bool& itRef) {
  assert(o >= f->base() && o < f->past());
  for (auto const& eh : f->ehtab()) {
    if (eh.m_type == EHEnt::Type::Fault &&
        eh.m_base <= o && o < eh.m_past &&
        eh.m_iterId == iterId) {
      itRef = eh.m_itRef;
      return true;
    }
  }
  return false;
}

static void toStringFrame(std::ostream& os, const ActRec* fp,
                          int offset, const TypedValue* ftop,
                          const std::string& prefix, bool isTop = true) {
  assert(fp);

  // Use depth-first recursion to output the most deeply nested stack frame
  // first.
  {
    Offset prevPc = 0;
    TypedValue* prevStackTop = nullptr;
    ActRec* prevFp = g_context->getPrevVMStateUNSAFE(fp, &prevPc, &prevStackTop);
    if (prevFp != nullptr) {
      toStringFrame(os, prevFp, prevPc, prevStackTop, prefix, false);
    }
  }

  os << prefix;
  const Func* func = fp->m_func;
  assert(func);
  func->validate();
  std::string funcName(func->fullName()->data());
  os << "{func:" << funcName
     << ",soff:" << fp->m_soff
     // cheng-hack: I don't really care the toStringFrame
     << ",this:0x" << std::hex << (fp->hasThis() ? fp->getThisDefault() : nullptr) 
     << std::dec << "}";
  TypedValue* tv = (TypedValue*)fp;
  tv--;

  if (func->numLocals() > 0) {
    // Don't print locals for parent frames on a Ret(C|V) since some of them
    // may already be destructed.
    if (isRet(func->unit()->getOpcode(offset)) && !isTop) {
      os << "<locals destroyed>";
    } else {
      os << "<";
      int n = func->numLocals();
      for (int i = 0; i < n; i++, tv--) {
        if (i > 0) {
          os << " ";
        }
        os << toStringElm(tv);
      }
      os << ">";
    }
  }

  assert(!func->methInfo() || func->numIterators() == 0);
  if (func->numIterators() > 0) {
    os << "|";
    Iter* it = &((Iter*)&tv[1])[-1];
    for (int i = 0; i < func->numIterators(); i++, it--) {
      if (i > 0) {
        os << " ";
      }
      bool itRef;
      if (checkIterScope(func, offset, i, itRef)) {
        os << toStringIter(it, itRef);
      } else {
        os << "I:Undefined";
      }
    }
    os << "|";
  }

  std::vector<std::string> stackElems;
  visitStackElems(
    fp, ftop, offset,
    [&](const ActRec* ar) {
      stackElems.push_back(
        folly::format("{{func:{}}}", ar->m_func->fullName()->data()).str()
      );
    },
    [&](const TypedValue* tv) {
      stackElems.push_back(toStringElm(tv));
    }
  );
  std::reverse(stackElems.begin(), stackElems.end());
  os << ' ' << folly::join(' ', stackElems);

  os << '\n';
}

std::string Stack::toString(const ActRec* fp, int offset,
                       const std::string prefix/* = "" */) const {
  // The only way to figure out which stack elements are activation records is
  // to follow the frame chain. However, the goal for each stack frame is to
  // print stack fragments from deepest to shallowest -- a then b in the
  // following example:
  //
  //   {func:foo,soff:51}<C:8> {func:bar} C:8 C:1 {func:biz} C:0
  //                           aaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbb
  //
  // Use depth-first recursion to get the output order correct.

  std::ostringstream os;
  auto unit = fp->unit();
  auto func = fp->func();
  os << prefix << "=== Stack at "
     << unit->filepath()->data() << ":"
     << unit->getLineNumber(unit->offsetOf(vmpc()))
     << " func " << func->fullName()->data() << " ===\n";

  toStringFrame(os, fp, offset, m_top, prefix);

  return os.str();
}

bool Stack::wouldOverflow(int numCells) const {
  // The funny approach here is to validate the translator's assembly
  // technique. We've aligned and sized the stack so that the high order
  // bits of valid cells are all the same. In the translator, numCells
  // can be hardcoded, and m_top is wired into a register,
  // so the expression requires no loads.
  intptr_t truncatedTop = intptr_t(m_top) / sizeof(TypedValue);
  truncatedTop &= RuntimeOption::EvalVMStackElms - 1;
  intptr_t diff = truncatedTop - numCells -
    sSurprisePageSize / sizeof(TypedValue);
  return diff < 0;
}

TypedValue* Stack::frameStackBase(const ActRec* fp) {
  assert(!fp->resumed());
  return (TypedValue*)fp - fp->func()->numSlotsInFrame();
}

TypedValue* Stack::resumableStackBase(const ActRec* fp) {
  assert(fp->resumed());
  auto const sfp = fp->sfp();
  if (sfp) {
    // The non-reentrant case occurs when a non-async or async generator is
    // resumed via ContEnter or ContRaise opcode. These opcodes leave a single
    // value on the stack that becomes part of the generator's stack. So we
    // find the caller's FP, compensate for its locals and iterators, and then
    // we've found the base of the generator's stack.
    assert(fp->func()->isGenerator());
    return (TypedValue*)sfp - sfp->func()->numSlotsInFrame();
  } else {
    // The reentrant case occurs when asio scheduler resumes an async function
    // or async generator. We simply use the top of stack of the previous VM
    // frame (since the ActRec, locals, and iters for this frame do not reside
    // on the VM stack).
    assert(fp->func()->isAsync());
    return g_context.getNoCheck()->m_nestedVMs.back().sp;
  }
}

//=============================================================================
// ExecutionContext.

ActRec* ExecutionContext::getOuterVMFrame(const ActRec* ar) {
  ActRec* sfp = ar->sfp();
  if (LIKELY(sfp != nullptr)) return sfp;
  return LIKELY(!m_nestedVMs.empty()) ? m_nestedVMs.back().fp : nullptr;
}

Cell ExecutionContext::lookupClsCns(const NamedEntity* ne,
                                      const StringData* cls,
                                      const StringData* cns) {
  Class* class_ = Unit::loadClass(ne, cls);
  if (class_ == nullptr) {
    raise_error(Strings::UNKNOWN_CLASS, cls->data());
  }
  Cell clsCns = class_->clsCnsGet(cns);
  if (clsCns.m_type == KindOfUninit) {
    raise_error("Couldn't find constant %s::%s",
                cls->data(), cns->data());
  }
  return clsCns;
}

Cell ExecutionContext::lookupClsCns(const StringData* cls,
                                      const StringData* cns) {
  return lookupClsCns(NamedEntity::get(cls), cls, cns);
}

// Look up the method specified by methodName from the class specified by cls
// and enforce accessibility. Accessibility checks depend on the relationship
// between the class that first declared the method (baseClass) and the context
// class (ctx).
//
// If there are multiple accessible methods with the specified name declared in
// cls and ancestors of cls, the method from the most derived class will be
// returned, except if we are doing an ObjMethod call ("$obj->foo()") and there
// is an accessible private method, in which case the accessible private method
// will be returned.
//
// Accessibility rules:
//
//   | baseClass/ctx relationship | public | protected | private |
//   +----------------------------+--------+-----------+---------+
//   | anon/unrelated             | yes    | no        | no      |
//   | baseClass == ctx           | yes    | yes       | yes     |
//   | baseClass derived from ctx | yes    | yes       | no      |
//   | ctx derived from baseClass | yes    | yes       | no      |
//   +----------------------------+--------+-----------+---------+

const StaticString s_construct("__construct");

const Func* ExecutionContext::lookupMethodCtx(const Class* cls,
                                              const StringData* methodName,
                                              const Class* ctx,
                                              CallType callType,
                                              bool raise /* = false */) {
  const Func* method;
  if (callType == CallType::CtorMethod) {
    assert(methodName == nullptr);
    method = cls->getCtor();
  } else {
    assert(callType == CallType::ObjMethod || callType == CallType::ClsMethod);
    assert(methodName != nullptr);
    method = cls->lookupMethod(methodName);
    while (!method) {
      if (UNLIKELY(methodName->isame(s_construct.get()))) {
        // We were looking up __construct and failed to find it. Fall back
        // to old-style constructor: same as class name.
        method = cls->getCtor();
        if (!Func::isSpecial(method->name())) break;
      }
      // We didn't find any methods with the specified name in cls's method
      // table, handle the failure as appropriate.
      if (raise) {
        raise_error("Call to undefined method %s::%s()",
                    cls->name()->data(),
                    methodName->data());
      }
      return nullptr;
    }
  }
  assert(method);
  bool accessible = true;
  // If we found a protected or private method, we need to do some
  // accessibility checks.
  if ((method->attrs() & (AttrProtected|AttrPrivate)) &&
      !g_context->debuggerSettings.bypassCheck) {
    Class* baseClass = method->baseCls();
    assert(baseClass);
    // If ctx is the class that first declared this method, then we know we
    // have the right method and we can stop here.
    if (ctx == baseClass) {
      return method;
    }
    // The invalid context cannot access protected or private methods,
    // so we can fail fast here.
    if (ctx == nullptr) {
      if (raise) {
        raise_error("Call to %s %s::%s() from invalid context",
                    (method->attrs() & AttrPrivate) ? "private" : "protected",
                    cls->name()->data(),
                    method->name()->data());
      }
      return nullptr;
    }
    assert(ctx);
    if (method->attrs() & AttrPrivate) {
      // ctx is not the class that declared this private method, so this
      // private method is not accessible. We need to keep going because
      // ctx might define a private method with this name.
      accessible = false;
    } else {
      // If ctx is derived from the class that first declared this protected
      // method, then we know this method is accessible and thus (due to
      // semantic checks) we know ctx cannot have a private method with the
      // same name, so we're done.
      if (ctx->classof(baseClass)) {
        return method;
      }
      if (!baseClass->classof(ctx)) {
        // ctx is not related to the class that first declared this protected
        // method, so this method is not accessible. Because ctx is not the
        // same or an ancestor of the class which first declared the method,
        // we know that ctx not the same or an ancestor of cls, and therefore
        // we don't need to check if ctx declares a private method with this
        // name, so we can fail fast here.
        if (raise) {
          raise_error("Call to protected method %s::%s() from context '%s'",
                      cls->name()->data(),
                      method->name()->data(),
                      ctx->name()->data());
        }
        return nullptr;
      }
      // We now know this protected method is accessible, but we need to
      // keep going because ctx may define a private method with this name.
      assert(accessible && baseClass->classof(ctx));
    }
  }
  // If this is an ObjMethod call ("$obj->foo()") AND there is an ancestor
  // of cls that declares a private method with this name AND ctx is an
  // ancestor of cls, we need to check if ctx declares a private method with
  // this name.
  if (method->hasPrivateAncestor() && callType == CallType::ObjMethod &&
      ctx && cls->classof(ctx)) {
    const Func* ctxMethod = ctx->lookupMethod(methodName);
    if (ctxMethod && ctxMethod->cls() == ctx &&
        (ctxMethod->attrs() & AttrPrivate)) {
      // For ObjMethod calls, a private method declared by ctx trumps
      // any other method we may have found.
      return ctxMethod;
    }
  }
  // If we found an accessible method in cls's method table, return it.
  if (accessible) {
    return method;
  }
  // If we reach here it means we've found an inaccessible private method
  // in cls's method table, handle the failure as appropriate.
  if (raise) {
    raise_error("Call to private method %s::%s() from %s'%s'",
                method->baseCls()->name()->data(),
                method->name()->data(),
                ctx ? "context " : "invalid context",
                ctx ? ctx->name()->data() : "");
  }
  return nullptr;
}

LookupResult ExecutionContext::lookupObjMethod(const Func*& f,
                                                 const Class* cls,
                                                 const StringData* methodName,
                                                 const Class* ctx,
                                                 bool raise /* = false */) {
  f = lookupMethodCtx(cls, methodName, ctx, CallType::ObjMethod, false);
  if (!f) {
    f = cls->lookupMethod(s___call.get());
    if (!f) {
      if (raise) {
        // Throw a fatal error
        lookupMethodCtx(cls, methodName, ctx, CallType::ObjMethod, true);
      }
      return LookupResult::MethodNotFound;
    }
    return LookupResult::MagicCallFound;
  }
  if (f->attrs() & AttrStatic && !f->isClosureBody()) {
    return LookupResult::MethodFoundNoThis;
  }
  return LookupResult::MethodFoundWithThis;
}

LookupResult
ExecutionContext::lookupClsMethod(const Func*& f,
                                    const Class* cls,
                                    const StringData* methodName,
                                    ObjectData* obj,
                                    const Class* ctx,
                                    bool raise /* = false */) {
  f = lookupMethodCtx(cls, methodName, ctx, CallType::ClsMethod, false);
  if (!f) {
    if (obj && obj->instanceof(cls)) {
      f = obj->getVMClass()->lookupMethod(s___call.get());
    }
    if (!f) {
      f = cls->lookupMethod(s___callStatic.get());
      if (!f) {
        if (raise) {
          // Throw a fatal error
          lookupMethodCtx(cls, methodName, ctx, CallType::ClsMethod, true);
        }
        return LookupResult::MethodNotFound;
      }
      f->validate();
      assert(f);
      assert(f->attrs() & AttrStatic);
      return LookupResult::MagicCallStaticFound;
    }
    assert(f);
    assert(obj);
    // __call cannot be static, this should be enforced by semantic
    // checks defClass time or earlier
    assert(!(f->attrs() & AttrStatic));
    return LookupResult::MagicCallFound;
  }
  if (obj && !(f->attrs() & AttrStatic) && obj->instanceof(cls)) {
    return LookupResult::MethodFoundWithThis;
  }
  return LookupResult::MethodFoundNoThis;
}

LookupResult ExecutionContext::lookupCtorMethod(const Func*& f,
                                                const Class* cls,
                                                bool raise /* = false */) {
  f = cls->getCtor();
  if (!(f->attrs() & AttrPublic)) {
    Class* ctx = arGetContextClass(vmfp());
    f = lookupMethodCtx(cls, nullptr, ctx, CallType::CtorMethod, raise);
    if (!f) {
      // If raise was true than lookupMethodCtx should have thrown,
      // so we should only be able to get here if raise was false
      assert(!raise);
      return LookupResult::MethodNotFound;
    }
  }
  return LookupResult::MethodFoundWithThis;
}

static Class* loadClass(StringData* clsName) {
  Class* class_ = Unit::loadClass(clsName);
  if (class_ == nullptr) {
    raise_error(Strings::UNKNOWN_CLASS, clsName->data());
  }
  return class_;
}

ObjectData* ExecutionContext::createObject(StringData* clsName,
                                           const Variant& params,
                                           bool init /* = true */) {
  return createObject(loadClass(clsName), params, init);
}

ObjectData* ExecutionContext::createObject(const Class* class_,
                                           const Variant& params,
                                           bool init) {
  Object o;
  o = newInstance(const_cast<Class*>(class_));
  if (init) {
    initObject(class_, params, o.get());
  }

  ObjectData* ret = o.detach();
  ret->decRefCount();
  return ret;
}

ObjectData* ExecutionContext::createObjectOnly(StringData* clsName) {
  return createObject(clsName, init_null_variant, false);
}

ObjectData* ExecutionContext::initObject(StringData* clsName,
                                         const Variant& params,
                                         ObjectData* o) {
  return initObject(loadClass(clsName), params, o);
}

// cheng-hack:
// This is for multi_mysql_fetch_object()
sptr<std::vector<ObjectData*> >
ExecutionContext::initObject_multi(StringData* className,
                             const Variant& params,
                             sptr< std::vector<ObjectData*> > o_arr) {
  auto class_ = loadClass(className);
  auto ctor = class_->getCtor();
  if (!(ctor->attrs() & AttrPublic)) {
    std::string msg = "Access to non-public constructor of class ";
    msg += class_->name()->data();
    throw Object(Reflection::AllocReflectionExceptionObject(msg));
  }
  // call constructor
  if (!isContainerOrNull(params)) {
    throw_param_is_not_container();
  }
  TypedValue ret;
  invokeFunc(&ret, ctor, params, nullptr, nullptr, nullptr, nullptr, InvokeNormal, o_arr);
  tvRefcountedDecRef(&ret);
  return o_arr;
}

ObjectData* ExecutionContext::initObject(const Class* class_,
                                         const Variant& params,
                                         ObjectData* o) {
  auto ctor = class_->getCtor();
  if (!(ctor->attrs() & AttrPublic)) {
    std::string msg = "Access to non-public constructor of class ";
    msg += class_->name()->data();
    throw Object(Reflection::AllocReflectionExceptionObject(msg));
  }
  // call constructor
  if (!isContainerOrNull(params)) {
    throw_param_is_not_container();
  }
  TypedValue ret;
  invokeFunc(&ret, ctor, params, o);
  tvRefcountedDecRef(&ret);
  return o;
}

ActRec* ExecutionContext::getStackFrame() {
  VMRegAnchor _;
  return vmfp();
}

ObjectData* ExecutionContext::getThis() {
  VMRegAnchor _;
  ActRec* fp = vmfp();
  if (fp->skipFrame()) {
    fp = getPrevVMStateUNSAFE(fp);
    if (!fp) return nullptr;
  }
  if (fp->hasThis()) {
    // cheng-hack: no choice, but crash when meet multi
    return fp->getThisSingle();
  }
  return nullptr;
}

Class* ExecutionContext::getContextClass() {
  VMRegAnchor _;
  ActRec* ar = vmfp();
  assert(ar != nullptr);
  if (ar->skipFrame()) {
    ar = getPrevVMStateUNSAFE(ar);
    if (!ar) return nullptr;
  }
  return ar->m_func->cls();
}

Class* ExecutionContext::getParentContextClass() {
  if (Class* ctx = getContextClass()) {
    return ctx->parent();
  }
  return nullptr;
}

StringData* ExecutionContext::getContainingFileName() {
  VMRegAnchor _;
  ActRec* ar = vmfp();
  if (ar == nullptr) return staticEmptyString();
  if (ar->skipFrame()) {
    ar = getPrevVMStateUNSAFE(ar);
    if (ar == nullptr) return staticEmptyString();
  }
  Unit* unit = ar->m_func->unit();
  assert(unit->filepath()->isStatic());
  // XXX: const StringData* -> Variant(bool) conversion problem makes this ugly
  return const_cast<StringData*>(unit->filepath());
}

int ExecutionContext::getLine() {
  VMRegAnchor _;
  ActRec* ar = vmfp();
  Unit* unit = ar ? ar->m_func->unit() : nullptr;
  Offset pc = unit ? pcOff() : 0;
  if (ar == nullptr) return -1;
  if (ar->skipFrame()) {
    ar = getPrevVMStateUNSAFE(ar, &pc);
  }
  if (ar == nullptr || (unit = ar->m_func->unit()) == nullptr) return -1;
  return unit->getLineNumber(pc);
}

Array ExecutionContext::getCallerInfo() {
  VMRegAnchor _;
  Array result = Array::Create();
  ActRec* ar = vmfp();
  if (ar->skipFrame()) {
    ar = getPrevVMStateUNSAFE(ar);
  }
  while (ar->m_func->name()->isame(s_call_user_func.get())
         || ar->m_func->name()->isame(s_call_user_func_array.get())) {
    ar = getPrevVMStateUNSAFE(ar);
    if (ar == nullptr) {
      return result;
    }
  }

  Offset pc = 0;
  ar = getPrevVMStateUNSAFE(ar, &pc);
  while (ar != nullptr) {
    if (!ar->m_func->name()->isame(s_call_user_func.get())
        && !ar->m_func->name()->isame(s_call_user_func_array.get())) {
      Unit* unit = ar->m_func->unit();
      int lineNumber;
      if ((lineNumber = unit->getLineNumber(pc)) != -1) {
        result.set(s_file, unit->filepath()->data(), true);
        result.set(s_line, lineNumber);
        return result;
      }
    }
    ar = getPrevVMStateUNSAFE(ar, &pc);
  }
  return result;
}

VarEnv* ExecutionContext::getVarEnv(int frame) {
  VMRegAnchor _;

  ActRec* fp = vmfp();
  for (; frame > 0; --frame) {
    if (!fp) break;
    fp = getPrevVMStateUNSAFE(fp);
  }
  if (UNLIKELY(!fp)) return NULL;
  if (fp->skipFrame()) {
    fp = getPrevVMStateUNSAFE(fp);
  }
  if (!fp) return nullptr;
  assert(!fp->hasInvName());
  if (!fp->hasVarEnv()) {
    fp->setVarEnv(VarEnv::createLocal(fp));
  }
  return fp->m_varEnv;
}

void ExecutionContext::setVar(StringData* name, const TypedValue* v) {
  VMRegAnchor _;
  ActRec *fp = vmfp();
  if (!fp) return;
  if (fp->skipFrame()) fp = getPrevVMStateUNSAFE(fp);
  fp->getVarEnv()->set(name, v);
}

void ExecutionContext::bindVar(StringData* name, TypedValue* v) {
  VMRegAnchor _;
  ActRec *fp = vmfp();
  if (!fp) return;
  if (fp->skipFrame()) fp = getPrevVMStateUNSAFE(fp);
  fp->getVarEnv()->bind(name, v);
}

Array ExecutionContext::getLocalDefinedVariables(int frame) {
  VMRegAnchor _;
  ActRec *fp = vmfp();
  for (; frame > 0; --frame) {
    if (!fp) break;
    fp = getPrevVMStateUNSAFE(fp);
  }
  if (!fp) {
    return empty_array();
  }
  assert(!fp->hasInvName());
  if (fp->hasVarEnv()) {
    return fp->m_varEnv->getDefinedVariables();
  }
  const Func *func = fp->m_func;
  auto numLocals = func->numNamedLocals();
  ArrayInit ret(numLocals, ArrayInit::Map{});
  for (Id id = 0; id < numLocals; ++id) {
    TypedValue* ptv = frame_local(fp, id);
    if (ptv->m_type == KindOfUninit) {
      continue;
    }
    Variant name(func->localVarName(id), Variant::StaticStrInit{});
    ret.add(name, tvAsVariant(ptv));
  }
  return ret.toArray();
}

NEVER_INLINE
static void shuffleExtraStackArgs(ActRec* ar) {
  const Func* func = ar->m_func;
  assert(func);
  assert(!ar->m_varEnv);

  // the last (variadic) param is included in numParams (since it has a
  // name), but the arg in that slot should be included as the first
  // element of the variadic array
  const auto numArgs = ar->numArgs();
  const auto numVarArgs = numArgs - func->numNonVariadicParams();
  assert(numVarArgs > 0);

  const auto takesVariadicParam = func->hasVariadicCaptureParam();
  auto& stack = vmStack();
  if (func->attrs() & AttrMayUseVV) {
    auto const tvArgs = reinterpret_cast<TypedValue*>(ar) - numArgs;
    ar->setExtraArgs(ExtraArgs::allocateCopy(tvArgs, numVarArgs));
    if (takesVariadicParam) {
      auto varArgsArray =
        Array::attach(MixedArray::MakePacked(numVarArgs, tvArgs));
      // Incref the args (they're already referenced in extraArgs) but now
      // additionally referenced in varArgsArray ...
      auto tv = tvArgs; uint32_t i = 0;
      for (; i < numVarArgs; ++i, ++tv) { tvRefcountedIncRef(tv); }
      // ... and now remove them from the stack
      stack.ndiscard(numVarArgs);
      auto const ad = varArgsArray.detach();
      assert(ad->hasExactlyOneRef());
      stack.pushArrayNoRc(ad);
      // Before, for each arg: refcount = n + 1 (stack)
      // After, for each arg: refcount = n + 2 (ExtraArgs, varArgsArray)
    } else {
      // Discard the arguments from the stack; they were all moved
      // into the extra args so we don't decref.
      stack.ndiscard(numVarArgs);
    }
    // leave ar->numArgs reflecting the actual number of args passed
  } else {
    assert(takesVariadicParam); // called only if extra args are used
    auto const tvArgs = reinterpret_cast<TypedValue*>(ar) - numArgs;
    auto varArgsArray =
      Array::attach(MixedArray::MakePacked(numVarArgs, tvArgs));
    // Discard the arguments from the stack; they were all moved into the
    // variadic args array so we don't need to decref the values.
    stack.ndiscard(numVarArgs);
    auto const ad = varArgsArray.detach();
    assert(ad->hasExactlyOneRef());
    stack.pushArrayNoRc(ad);
    assert(func->numParams() == (numArgs - numVarArgs + 1));
    ar->setNumArgs(func->numParams());
  }
}

static void shuffleMagicArgs(ActRec* ar) {
  // We need to put this where the first argument is
  StringData* invName = ar->getInvName();
  int nargs = ar->numArgs();
  ar->setVarEnv(nullptr);
  assert(!ar->hasVarEnv() && !ar->hasInvName());

  // We need to make an array containing all the arguments passed by
  // the caller and put it where the second argument is.
  auto argArray = Array::attach(
    nargs ? MixedArray::MakePacked(
              nargs, reinterpret_cast<TypedValue*>(ar) - nargs)
          : staticEmptyArray()
  );

  auto& stack = vmStack();
  // Remove the arguments from the stack; they were moved into the
  // array so we don't need to decref.
  stack.ndiscard(nargs);

  // Move invName to where the first argument belongs, no need
  // to incRef/decRef since we are transferring ownership
  stack.pushStringNoRc(invName);

  // Move argArray to where the second argument belongs. We've already
  // incReffed the array above so we don't need to do it here.
  stack.pushArrayNoRc(argArray.detach());

  ar->setNumArgs(2);
}

// This helper only does a stack overflow check for the native stack
static inline void checkNativeStack() {
  auto const info = ThreadInfo::s_threadInfo.getNoCheck();
  // Check whether func's maximum stack usage would overflow the stack.
  // Both native and VM stack overflows are independently possible.
  if (!stack_in_bounds(info)) {
    TRACE(1, "Maximum stack depth exceeded.\n");
    raise_error("Stack overflow");
  }
}

/*
 * This helper does a stack overflow check on *both* the native stack
 * and the VM stack.
 *
 * In some cases for re-entry, we're checking for space other than
 * just the callee, and `extraCells' may need to be passed with a
 * non-zero value.  (We over-check in these situations, but it's fine.)
 */
ALWAYS_INLINE
static void checkStack(Stack& stk, const Func* f, int32_t extraCells) {
  assert(f);
  auto const info = ThreadInfo::s_threadInfo.getNoCheck();
  /*
   * Check whether func's maximum stack usage would overflow the stack.
   * Both native and VM stack overflows are independently possible.
   *
   * All stack checks are inflated by kStackCheckPadding to ensure
   * there is space both for calling leaf functions /and/ for
   * re-entry.  (See kStackCheckReenterPadding and
   * kStackCheckLeafPadding.)
   */
  auto limit = f->maxStackCells() + kStackCheckPadding + extraCells;
  if (!stack_in_bounds(info) || stk.wouldOverflow(limit)) {
    TRACE(1, "Maximum stack depth exceeded.\n");
    raise_error("Stack overflow");
  }
}

// This helper is meant to be called if an exception or invalidation takes
// place in the process of function entry; the ActRec ar is on the stack
// but is not (yet) the current (executing) frame and is followed by a
// number of params
static NEVER_INLINE void cleanupParamsAndActRec(Stack& stack,
                                                ActRec* ar,
                                                ExtraArgs* extraArgs,
                                                int* numParams) {
  assert(stack.top() + (numParams != nullptr ? (*numParams) :
                        extraArgs != nullptr ? ar->m_func->numParams() :
                        ar->numArgs())
         == (void*)ar);
  if (extraArgs) {
    const int numExtra = ar->numArgs() - ar->m_func->numNonVariadicParams();
    ExtraArgs::deallocate(extraArgs, numExtra);
  }
  while (stack.top() != (void*)ar) {
    stack.popTV();
  }
  stack.popAR();
}

static NEVER_INLINE void shuffleMagicArrayArgs(ActRec* ar, const Cell args,
                                               Stack& stack, int nregular) {
  assert(ar != nullptr && ar->hasInvName());
  assert(!cellIsNull(&args));
  assert(nregular >= 0);
  assert((stack.top() + nregular) == (void*) ar);
  assert(isContainer(args));
  DEBUG_ONLY const Func* f = ar->m_func;
  assert(f &&
         (f->name()->isame(s___call.get()) ||
          f->name()->isame(s___callStatic.get())));

  // We'll need to make this the first argument
  StringData* invName = ar->getInvName();
  ar->setVarEnv(nullptr);
  assert(!ar->hasVarEnv() && !ar->hasInvName());

  auto nargs = getContainerSize(args);

  if (UNLIKELY(0 == nargs)) {
    // We need to make an array containing all the arguments passed by
    // the caller and put it where the second argument is.
    auto argArray = Array::attach(
      nregular
      ? MixedArray::MakePacked(
        nregular, reinterpret_cast<TypedValue*>(ar) - nregular)
      : staticEmptyArray()
    );

    // Remove the arguments from the stack; they were moved into the
    // array so we don't need to decref.
    stack.ndiscard(nregular);

    // Move invName to where the first argument belongs, no need
    // to incRef/decRef since we are transferring ownership
    assert(stack.top() == (void*) ar);
    stack.pushStringNoRc(invName);

    // Move argArray to where the second argument belongs. We've already
    // incReffed the array above so we don't need to do it here.
    stack.pushArrayNoRc(argArray.detach());
  } else {
    if (nregular == 0
        && args.m_type == KindOfArray
        && args.m_data.parr->isVectorData()) {
      assert(stack.top() == (void*) ar);
      stack.pushStringNoRc(invName);
      stack.pushArray(args.m_data.parr);
    } else {
      PackedArrayInit ai(nargs + nregular);
      for (int i = 0; i < nregular; ++i) {
        // appendWithRef bumps the refcount and splits if necessary, to
        // compensate for the upcoming pop from the stack
        ai.appendWithRef(tvAsVariant(stack.top()));
        stack.popTV();
      }
      assert(stack.top() == (void*) ar);
      stack.pushStringNoRc(invName);
      for (ArrayIter iter(args); iter; ++iter) {
        ai.appendWithRef(iter.secondRefPlus());
      }
      stack.pushArray(ai.create());
    }
  }

  ar->setNumArgs(2);
}

// offset is the number of params already on the stack to which the
// contents of args are to be added; for call_user_func_array, this is
// always 0; for unpacked arguments, it may be greater if normally passed
// params precede the unpack.
static bool prepareArrayArgs(ActRec* ar, const Cell args,
                             Stack& stack,
                             int nregular,
                             bool doCufRefParamChecks,
                             TypedValue* retval) {
  assert(ar != nullptr);
  assert(!cellIsNull(&args));
  assert(nregular >= 0);
  assert((stack.top() + nregular) == (void*) ar);
  const Func* f = ar->m_func;
  assert(f);

  assert(!ar->hasExtraArgs());

  // cheng-hack: if args is multi-value array, we should
  //             make it array of multi-value
  auto new_args = args;
  if (UNLIKELY(args.m_type == KindOfMulti)) {
    START;
    AS_MCALL;
    new_args = MultiVal::invertTransferArray(new_args);
    END;
  }

  always_assert(isContainer(new_args));
  int nargs = nregular + getContainerSize(new_args);
  assert(!ar->hasVarEnv() || (0 == nargs));
  if (UNLIKELY(ar->hasInvName())) {
    shuffleMagicArrayArgs(ar, new_args, stack, nregular);
    return true;
  }

  int nparams = f->numNonVariadicParams();
  int nextra_regular = std::max(nregular - nparams, 0);
  ArrayIter iter(new_args);
  if (LIKELY(nextra_regular == 0)) {
    for (int i = nregular; iter && (i < nparams); ++i, ++iter) {
      TypedValue* from = const_cast<TypedValue*>(
        iter.secondRefPlus().asTypedValue());
      TypedValue* to = stack.allocTV();
      if (LIKELY(!f->byRef(i))) {
        cellDup(*tvToCell(from), *to);
      } else if (LIKELY(from->m_type == KindOfRef &&
                        from->m_data.pref->getCount() >= 2)) {
        refDup(*from, *to);
      } else if (from->m_type == KindOfMulti &&
                 from->m_data.pmulti->getType() == KindOfRef) {
        // copy the multi-ref to the dst location
        cellDup(*from, *to);
      } else {
        if (doCufRefParamChecks && f->mustBeRef(i)) {
          try {
            raise_warning("Parameter %d to %s() expected to be a reference, "
                          "value given", i + 1, f->fullName()->data());
          } catch (...) {
            // If the user error handler throws an exception, discard the
            // uninitialized value(s) at the top of the eval stack so that the
            // unwinder doesn't choke
            stack.discard();
            if (retval) { tvWriteNull(retval); }
            throw;
          }
          if (skipCufOnInvalidParams) {
            stack.discard();
            cleanupParamsAndActRec(stack, ar, nullptr, &i);
            if (retval) { tvWriteNull(retval); }
            return false;
          }
        }
        cellDup(*tvToCell(from), *to);
      }
    }

    if (LIKELY(!iter)) {
      // argArray was exhausted, so there are no "extra" arguments but there
      // may be a deficit of non-variadic arguments, and the need to push an
      // empty array for the variadic argument ... that work is left to
      // prepareFuncEntry
      ar->initNumArgs(nargs);
      return true;
    }
  }

  // there are "extra" arguments; passed as standard arguments prior to the
  // ... unpack operator and/or still remaining in argArray
  assert(nargs > nparams);
  assert(nextra_regular > 0 || !!iter);
  if (LIKELY(f->discardExtraArgs())) {
    if (UNLIKELY(nextra_regular > 0)) {
      // if unpacking, any regularly passed arguments on the stack
      // in excess of those expected by the function need to be discarded
      // in addition to the ones held in the arry
      do { stack.popTV(); } while (--nextra_regular);
    }

    // the extra args are not used in the function; no reason to add them
    // to the stack
    ar->initNumArgs(f->numParams());
    return true;
  }

  auto const hasVarParam = f->hasVariadicCaptureParam();
  auto const extra = nargs - nparams;
  if (f->attrs() & AttrMayUseVV) {
    ExtraArgs* extraArgs = ExtraArgs::allocateUninit(extra);
    PackedArrayInit ai(extra);
    if (UNLIKELY(nextra_regular > 0)) {
      for (int i = 0; i < nextra_regular; ++i) {
        TypedValue* to = extraArgs->getExtraArg(i);
        const TypedValue* from = stack.top();
        if (from->m_type == KindOfRef && from->m_data.pref->isReferenced()) {
          refDup(*from, *to);
        } else {
          cellDup(*tvToCell(from), *to);
        }
        if (hasVarParam) {
          // appendWithRef bumps the refcount: this accounts for the fact
          // that the extra args values went from being present on the stack
          // to being in (both) ExtraArgs and the variadic args
          ai.appendWithRef(tvAsCVarRef(from));
        }
        stack.discard();
      }
    }
    for (int i = nextra_regular; i < extra; ++i, ++iter) {
      TypedValue* to = extraArgs->getExtraArg(i);
      const TypedValue* from = iter.secondRefPlus().asTypedValue();
      if (from->m_type == KindOfRef && from->m_data.pref->isReferenced()) {
        refDup(*from, *to);
      } else {
        cellDup(*tvToCell(from), *to);
      }
      if (hasVarParam) {
        // appendWithRef bumps the refcount: this accounts for the fact
        // that the extra args values went from being present in
        // arrayArgs to being in (both) ExtraArgs and the variadic args
        ai.appendWithRef(iter.secondRefPlus());
      }
    }
    assert(!iter); // iter should now be exhausted
    if (hasVarParam) {
      auto const ad = ai.create();
      stack.pushArray(ad);
      assert(ad->hasExactlyOneRef());
    }
    ar->initNumArgs(nargs);
    ar->setExtraArgs(extraArgs);
  } else {
    assert(hasVarParam);
    if (nparams == 0
        && nextra_regular == 0
        && new_args.m_type == KindOfArray
        && new_args.m_data.parr->isVectorData()) {
      stack.pushArray(new_args.m_data.parr);
    } else {
      PackedArrayInit ai(extra);
      if (UNLIKELY(nextra_regular > 0)) {
        for (int i = 0; i < nextra_regular; ++i) {
          // appendWithRef bumps the refcount and splits if necessary,
          // to compensate for the upcoming pop from the stack
          ai.appendWithRef(tvAsVariant(stack.top()));
          stack.popTV();
        }
      }
      for (int i = nextra_regular; i < extra; ++i, ++iter) {
        // appendWithRef bumps the refcount to compensate for the
        // eventual decref of arrayArgs.
        ai.appendWithRef(iter.secondRefPlus());
      }
      assert(!iter); // iter should now be exhausted
      auto const ad = ai.create();
      stack.pushArray(ad);
      assert(ad->hasExactlyOneRef());
    }
    ar->initNumArgs(f->numParams());
  }
  return true;
}

enum class StackArgsState { // tells prepareFuncEntry how much work to do
  // the stack may contain more arguments than the function expects
  Untrimmed,
  // the stack has already been trimmed of any extra arguments, which
  // have been teleported away into ExtraArgs and/or a variadic param
  Trimmed
};

static void prepareFuncEntry(ActRec *ar, PC& pc, StackArgsState stk) {
  assert(!ar->resumed());
  const Func* func = ar->m_func;
  Offset firstDVInitializer = InvalidAbsoluteOffset;
  bool raiseMissingArgumentWarnings = false;
  const int nparams = func->numNonVariadicParams();
  auto& stack = vmStack();

  if (UNLIKELY(ar->m_varEnv != nullptr)) {
    // m_varEnv != nullptr means we have a varEnv, extraArgs, or an invName.
    if (ar->hasInvName()) {
      // shuffleMagicArgs deals with everything. no need for further
      // argument munging
      shuffleMagicArgs(ar);
    } else if (ar->hasVarEnv()) {
      assert(func->isPseudoMain());
      pushLocalsAndIterators(func);
      ar->m_varEnv->enterFP(vmfp(), ar);
      vmfp() = ar;
      pc = func->getEntry();
      // Nothing more to do; get out
      return;
    } else {
      assert(ar->hasExtraArgs());
      assert(nparams < ar->numArgs());
    }
  } else {
    int nargs = ar->numArgs();
    if (UNLIKELY(nargs > nparams)) {
      if (LIKELY(stk != StackArgsState::Trimmed && func->discardExtraArgs())) {
        // In the common case, the function won't use the extra arguments,
        // so act as if they were never passed (NOTE: this has the effect
        // of slightly misleading backtraces that don't reflect the
        // discarded args)
        for (int i = nparams; i < nargs; ++i) { stack.popTV(); }
        ar->setNumArgs(nparams);
      } else if (stk == StackArgsState::Trimmed) {
        assert(nargs == func->numParams());
        assert(((TypedValue*)ar - stack.top()) == func->numParams());
      } else {
        shuffleExtraStackArgs(ar);
      }
    } else {
      if (nargs < nparams) {
        // Push uninitialized nulls for missing arguments. Some of them may
        // end up getting default-initialized, but regardless, we need to
        // make space for them on the stack.
        const Func::ParamInfoVec& paramInfo = func->params();
        for (int i = nargs; i < nparams; ++i) {
          stack.pushUninit();
          Offset dvInitializer = paramInfo[i].funcletOff;
          if (dvInitializer == InvalidAbsoluteOffset) {
            // We wait to raise warnings until after all the locals have been
            // initialized. This is important because things need to be in a
            // consistent state in case the user error handler throws.
            raiseMissingArgumentWarnings = true;
          } else if (firstDVInitializer == InvalidAbsoluteOffset) {
            // This is the first unpassed arg with a default value, so
            // this is where we'll need to jump to.
            firstDVInitializer = dvInitializer;
          }
        }
      }
      if (UNLIKELY(func->hasVariadicCaptureParam())) {
        stack.pushArrayNoRc(staticEmptyArray());
      }
    }
  }

  int nlocals = func->numParams();
  if (UNLIKELY(func->isClosureBody())) {
    int nuse = init_closure(ar, stack.top());
    // init_closure doesn't move stack
    stack.nalloc(nuse);
    nlocals += nuse;
    func = ar->m_func;
  }

  pushLocalsAndIterators(func, nlocals);

  vmfp() = ar;
  if (firstDVInitializer != InvalidAbsoluteOffset) {
    pc = func->unit()->entry() + firstDVInitializer;
  } else {
    pc = func->getEntry();
  }
  // cppext functions/methods have their own logic for raising
  // warnings for missing arguments, so we only need to do this work
  // for non-cppext functions/methods
  if (raiseMissingArgumentWarnings && !func->isCPPBuiltin()) {
    // need to sync vmpc() to pc for backtraces/re-entry
    vmpc() = pc;
    HPHP::jit::raiseMissingArgument(func, ar->numArgs());
  }
}

void ExecutionContext::syncGdbState() {
  if (RuntimeOption::EvalJit && !RuntimeOption::EvalJitNoGdb) {
    mcg->getDebugInfo()->debugSync();
  }
}

static void dispatch();
static void enterVMAtCurPC();

static void enterVMAtAsyncFunc(ActRec* enterFnAr, Resumable* resumable,
                               ObjectData* exception) {
  assert(enterFnAr);
  assert(enterFnAr->func()->isAsync());
  assert(enterFnAr->resumed());
  assert(resumable);

  vmfp() = enterFnAr;
  vmpc() = vmfp()->func()->unit()->at(resumable->resumeOffset());
  assert(vmfp()->func()->contains(vmpc()));
  EventHook::FunctionResumeAwait(enterFnAr);

  if (UNLIKELY(exception != nullptr)) {
    assert(exception->instanceof(SystemLib::s_ExceptionClass));
    Object e(exception);
    throw e;
  }

  bool useJit = ThreadInfo::s_threadInfo->m_reqInjectionData.getJit();
  if (LIKELY(useJit && resumable->resumeAddr())) {
    Stats::inc(Stats::VMEnter);
    mcg->enterTCAfterPrologue(resumable->resumeAddr());
  } else {
    enterVMAtCurPC();
  }
}

static void enterVMAtFunc(ActRec* enterFnAr, StackArgsState stk) {
  assert(enterFnAr);
  assert(!enterFnAr->resumed());
  Stats::inc(Stats::VMEnter);

  bool useJit = ThreadInfo::s_threadInfo->m_reqInjectionData.getJit();
  bool useJitPrologue = useJit && vmfp()
    && !enterFnAr->m_varEnv
    && (stk != StackArgsState::Trimmed);
  // The jit prologues only know how to do limited amounts of work; cannot
  // be used for magic call/pseudo-main/extra-args already determined or
  // ... or if the stack args have been explicitly been prepared (e.g. via
  // entry as part of invoke func).

  if (LIKELY(useJitPrologue)) {
    const int np = enterFnAr->m_func->numNonVariadicParams();
    int na = enterFnAr->numArgs();
    if (na > np) na = np + 1;
    jit::TCA start = enterFnAr->m_func->getPrologue(na);
    mcg->enterTCAtPrologue(enterFnAr, start);
    return;
  }

  prepareFuncEntry(enterFnAr, vmpc(), stk);
  if (!EventHook::FunctionCall(enterFnAr, EventHook::NormalFunc)) return;
  checkStack(vmStack(), enterFnAr->m_func, 0);
  assert(vmfp()->func()->contains(vmpc()));

  if (useJit) {
    jit::TCA start = enterFnAr->m_func->getFuncBody();
    mcg->enterTCAfterPrologue(start);
  } else {
    dispatch();
  }
}

static void enterVMAtCurPC() {
  assert(vmfp());
  assert(vmpc());
  assert(vmfp()->func()->contains(vmpc()));
  Stats::inc(Stats::VMEnter);
  if (ThreadInfo::s_threadInfo->m_reqInjectionData.getJit()) {
    mcg->enterTC();
  } else {
    dispatch();
  }
}

/**
 * Enter VM and invoke a function or resume an async function. The 'ar'
 * argument points to an ActRec of the invoked/resumed function. When
 * an async function is resumed, a 'pc' pointing to the resume location
 * inside the async function must be provided. Optionally, the resumed
 * async function will throw an 'exception' upon entering VM if passed.
 */
static void enterVM(ActRec* ar, StackArgsState stk,
                    Resumable* resumable = nullptr,
                    ObjectData* exception = nullptr) {
  assert(ar);
  assert(!ar->sfp());
  assert(isReturnHelper(reinterpret_cast<void*>(ar->m_savedRip)));
  assert(ar->m_soff == 0);
  assert(!resumable || (stk == StackArgsState::Untrimmed));

  auto ec = &*g_context;
  DEBUG_ONLY int faultDepth = ec->m_faults.size();
  SCOPE_EXIT { assert(ec->m_faults.size() == faultDepth); };

  vmFirstAR() = ar;

  /*
   * When an exception is propagating, each nesting of the VM is
   * responsible for unwinding its portion of the execution stack, and
   * finding user handlers if it is a catchable exception.
   *
   * This try/catch is where all this logic is centered.  The actual
   * unwinding happens under exception_handler in unwind.cpp, which
   * returns a UnwindAction here to indicate what to do next.
   *
   * Either we'll enter the VM loop again at a user error/fault
   * handler, or propagate the exception to a less-nested VM.
   */
  bool first = true;
resume:
  try {
    if (first) {
      first = false;
      if (!resumable) {
        enterVMAtFunc(ar, stk);
      } else {
        enterVMAtAsyncFunc(ar, resumable, exception);
      }
    } else {
      enterVMAtCurPC();
    }

    // Everything succeeded with no exception---return to the previous
    // VM nesting level.
    return;

  } catch (...) {
    always_assert(tl_regState == VMRegState::CLEAN);
    switch (exception_handler()) {
      case UnwindAction::Propagate:
        break;
      case UnwindAction::ResumeVM:
        if (vmpc()) { goto resume; }
        return;
    }
  }

  /*
   * Here we have to propagate an exception out of this VM's nesting
   * level.
   */

  assert(ec->m_faults.size() > 0);
  Fault fault = ec->m_faults.back();
  ec->m_faults.pop_back();

  switch (fault.m_faultType) {
  case Fault::Type::UserException:
    {
      Object obj = fault.m_userException;
      fault.m_userException->decRefCount();
      throw obj;
    }
  case Fault::Type::CppException:
    // throwException() will take care of deleting heap-allocated
    // exception object for us
    fault.m_cppException->throwException();
    not_reached();
  }

  not_reached();
}

void ExecutionContext::invokeFunc(TypedValue* retptr,
                                  const Func* f,
                                  const Variant& args_,
                                  ObjectData* this_ /* = NULL */,
                                  Class* cls /* = NULL */,
                                  VarEnv* varEnv /* = NULL */,
                                  StringData* invName /* = NULL */,
                                  InvokeFlags flags /* = InvokeNormal */,
                                  sptr< std::vector<ObjectData*> > multi_this_ /*=NULL*/) {
  assert(retptr);
  assert(f);
  // If f is a regular function, this_ and cls must be NULL
  assert(f->preClass() || f->isPseudoMain() || ( (!this_ || !multi_this_) && !cls));
  // If f is a method, either this_ or cls must be non-NULL
  assert(!f->preClass() || ((this_ || multi_this_) || cls));
  // If f is a static method, this_ must be NULL
  assert(!(f->attrs() & AttrStatic && !f->isClosureBody()) ||
         ((!this_ || !multi_this_)));
  // invName should only be non-NULL if we are calling __call or
  // __callStatic
  assert(!invName || f->name()->isame(s___call.get()) ||
         f->name()->isame(s___callStatic.get()));
  const auto& args = *args_.asCell();
  assert(isContainerOrNull(args));
  // If we are inheriting a variable environment then args_ must be empty
  assert(!varEnv || cellIsNull(&args) || !getContainerSize(args));

  Cell* originalSP = vmRegsUnsafe().stack.top();

  VMRegAnchor _;
  DEBUG_ONLY Cell* reentrySP = vmStack().top();

  if (this_ != nullptr) {
    this_->incRefCount();
  }
  // cheng-hack: inc refcount for obj
  else if (multi_this_ != nullptr) {
    for (auto it : *multi_this_) {
      it->incRefCount();
    }
  }

  // We must do a stack overflow check for leaf functions on re-entry,
  // because we won't have checked that the stack is deep enough for a
  // leaf function /after/ re-entry, and the prologue for the leaf
  // function will not make a check.
  if (f->attrs() & AttrPhpLeafFn ||
      !(f->numParams() + kNumActRecCells <= kStackCheckReenterPadding)) {
    // Check both the native stack and VM stack for overflow.
    checkStack(vmStack(), f,
      kNumActRecCells /* numParams is included in f->maxStackCells */);
  } else {
    // invokeFunc() must always check the native stack for overflow no
    // matter what.
    checkNativeStack();
  }

  if (flags & InvokePseudoMain) {
    assert(f->isPseudoMain());
    assert(cellIsNull(&args) || !getContainerSize(args));
    Unit* toMerge = f->unit();
    toMerge->merge();
    if (toMerge->isMergeOnly()) {
      *retptr = *toMerge->getMainReturn();
      return;
    }
  }

  ActRec* ar = vmStack().allocA();
  ar->setReturnVMExit();
  ar->m_func = f;
  if (this_) {
    ar->setThisSingle(this_);
  }
  // cheng-hack:
  else if (multi_this_) {
    ar->setThisMulti(multi_this_);
  } else if (cls) {
    ar->setClass(cls);
  } else {
    ar->setThisSingle(nullptr);
  }
  auto numPassedArgs = cellIsNull(&args) ? 0 : getContainerSize(args);
  if (invName) {
    ar->setInvName(invName);
  } else {
    ar->setVarEnv(varEnv);
  }

  ar->initNumArgs(numPassedArgs);

#ifdef HPHP_TRACE
  if (vmfp() == nullptr) {
    TRACE(1, "Reentry: enter %s(%p) from top-level\n",
          f->name()->data(), ar);
  } else {
    TRACE(1, "Reentry: enter %s(pc %p ar %p) from %s(%p)\n",
          f->name()->data(), vmpc(), ar,
          vmfp()->m_func ? vmfp()->m_func->name()->data()
                         : "unknownBuiltin",
          vmfp());
  }
#endif

  if (!varEnv) {
    auto const& prepArgs = cellIsNull(&args)
      ? make_tv<KindOfArray>(staticEmptyArray())
      : args;
    auto prepResult = prepareArrayArgs(
      ar, prepArgs,
      vmStack(), 0,
      (bool) (flags & InvokeCuf), retptr);
    if (UNLIKELY(!prepResult)) {
      assert(KindOfNull == retptr->m_type);
      return;
    }
  }

  TypedValue retval;
  {
    pushVMState(originalSP);
    SCOPE_EXIT {
      assert_flog(
        vmStack().top() == reentrySP,
        "vmsp after reentry: {} doesn't match original vmsp: {}",
        vmStack().top(), reentrySP
      );
      popVMState();
    };

    // cheng-hack: just try to set the multi_this bit
    if (UNLIKELY(multi_this_!=nullptr)) {
      ar->setThisMulti(multi_this_);
    }

    enterVM(ar, varEnv ? StackArgsState::Untrimmed : StackArgsState::Trimmed);

    // retptr might point somewhere that is affected by (push|pop)VMState, so
    // don't write to it until after we pop the nested VM state.
    tvCopy(*vmStack().topTV(), retval);
    vmStack().discard();
  }

  tvCopy(retval, *retptr);
}

void ExecutionContext::invokeFuncFew(TypedValue* retptr,
                                     const Func* f,
                                     void* thisOrCls,
                                     StringData* invName,
                                     int argc,
                                     const TypedValue* argv) {
  assert(retptr);
  assert(f);
  // If this is a regular function, this_ and cls must be NULL
  assert(f->preClass() || !thisOrCls);
  // If this is a method, either this_ or cls must be non-NULL
  assert(!f->preClass() || thisOrCls);
  // If this is a static method, this_ must be NULL
  assert(!(f->attrs() & AttrStatic && !f->isClosureBody()) ||
         !ActRec::decodeThis(thisOrCls));
  // invName should only be non-NULL if we are calling __call or
  // __callStatic
  assert(!invName || f->name()->isame(s___call.get()) ||
         f->name()->isame(s___callStatic.get()));

  Cell* originalSP = vmRegsUnsafe().stack.top();

  VMRegAnchor _;
  DEBUG_ONLY Cell* reentrySP = vmStack().top();

  // See similar block of code above for why this is needed on
  // AttrPhpLeafFn.
  if (f->attrs() & AttrPhpLeafFn ||
      !(argc + kNumActRecCells <= kStackCheckReenterPadding)) {
    // Check both the native stack and VM stack for overflow
    checkStack(vmStack(), f, argc + kNumActRecCells);
  } else {
    // invokeFuncFew() must always check the native stack for overflow
    // no matter what
    checkNativeStack();
  }

  if (ObjectData* thiz = ActRec::decodeThis(thisOrCls)) {
    thiz->incRefCount();
  }

  ActRec* ar = vmStack().allocA();
  ar->setReturnVMExit();
  ar->m_func = f;
  ar->m_this = (ObjectData*)thisOrCls;
  ar->initNumArgs(argc);
  if (UNLIKELY(invName != nullptr)) {
    ar->setInvName(invName);
  } else {
    ar->m_varEnv = nullptr;
  }

#ifdef HPHP_TRACE
  if (vmfp() == nullptr) {
    TRACE(1, "Reentry: enter %s(%p) from top-level\n",
          f->name()->data(), ar);
  } else {
    TRACE(1, "Reentry: enter %s(pc %p ar %p) from %s(%p)\n",
          f->name()->data(), vmpc(), ar,
          vmfp()->m_func ? vmfp()->m_func->name()->data()
                         : "unknownBuiltin",
          vmfp());
  }
#endif

  for (ssize_t i = 0; i < argc; ++i) {
    const TypedValue *from = &argv[i];
    TypedValue *to = vmStack().allocTV();
    if (LIKELY(from->m_type != KindOfRef || !f->byRef(i))) {
      cellDup(*tvToCell(from), *to);
    } else {
      refDup(*from, *to);
    }
  }


  TypedValue retval;
  {
    pushVMState(originalSP);
    SCOPE_EXIT {
      assert(vmStack().top() == reentrySP);
      popVMState();
    };

    enterVM(ar, StackArgsState::Untrimmed);

    // retptr might point somewhere that is affected by (push|pop)VMState, so
    // don't write to it until after we pop the nested VM state.
    tvCopy(*vmStack().topTV(), retval);
    vmStack().discard();
  }

  tvCopy(retval, *retptr);
}

void ExecutionContext::resumeAsyncFunc(Resumable* resumable,
                                       ObjectData* freeObj,
                                       const Cell awaitResult) {
  assert(tl_regState == VMRegState::CLEAN);
  SCOPE_EXIT { assert(tl_regState == VMRegState::CLEAN); };

  auto fp = resumable->actRec();
  // We don't need to check for space for the ActRec (unlike generally
  // in normal re-entry), because the ActRec isn't on the stack.
  checkStack(vmStack(), fp->func(), 0);

  Cell* savedSP = vmStack().top();
  cellDup(awaitResult, *vmStack().allocC());

  // decref after awaitResult is on the stack
  decRefObj(freeObj);

  pushVMState(savedSP);
  SCOPE_EXIT { popVMState(); };

  enterVM(fp, StackArgsState::Untrimmed, resumable);
}

void ExecutionContext::resumeAsyncFuncThrow(Resumable* resumable,
                                            ObjectData* freeObj,
                                            ObjectData* exception) {
  assert(exception);
  assert(exception->instanceof(SystemLib::s_ExceptionClass));
  assert(tl_regState == VMRegState::CLEAN);
  SCOPE_EXIT { assert(tl_regState == VMRegState::CLEAN); };

  auto fp = resumable->actRec();
  checkStack(vmStack(), fp->func(), 0);

  // decref after we hold reference to the exception
  Object e(exception);
  decRefObj(freeObj);

  pushVMState(vmStack().top());
  SCOPE_EXIT { popVMState(); };

  enterVM(fp, StackArgsState::Untrimmed, resumable, exception);
}

namespace {

std::atomic<bool> s_foundHHConfig(false);
void checkHHConfig(const Unit* unit) {

  if (!RuntimeOption::EvalAuthoritativeMode &&
      RuntimeOption::LookForTypechecker &&
      !s_foundHHConfig &&
      unit->isHHFile()) {
    const std::string &s = unit->filepath()->toCppString();
    boost::filesystem::path p(s);

    while (p != "/") {
      p.remove_filename();
      p /= ".hhconfig";

      if (boost::filesystem::exists(p)) {
        break;
      }

      p.remove_filename();
    }

    if (p == "/") {
      raise_error(
        "%s appears to be a Hack file, but you do not appear to be running "
        "the Hack typechecker. See the documentation at %s for information on "
        "getting it running. You can also set Hack.Lang.LookForTypechecker=0 "
        "to disable this check (not recommended).",
        s.c_str(),
        "http://docs.hhvm.com/manual/en/install.hack.bootstrapping.php"
      );
    } else {
      s_foundHHConfig = true;
    }
  }
}

}

void ExecutionContext::invokeUnit(TypedValue* retval, const Unit* unit) {
  checkHHConfig(unit);

  auto const func = unit->getMain();
  invokeFunc(retval, func, init_null_variant, nullptr, nullptr,
             m_globalVarEnv, nullptr, InvokePseudoMain);
}

/*
 * Given a pointer to a VM frame, returns the previous VM frame in the call
 * stack. This function will also pass back by reference the previous PC (if
 * prevPc is non-null) and the previous SP (if prevSp is non-null).
 *
 * If there is no previous VM frame, this function returns NULL and does not
 * set prevPc and prevSp.
 */
ActRec* ExecutionContext::getPrevVMStateUNSAFE(const ActRec* fp,
                                               Offset* prevPc /* = NULL */,
                                               TypedValue** prevSp /* = NULL */,
                                               bool* fromVMEntry /* = NULL */) {
  if (fp == nullptr) {
    return nullptr;
  }
  ActRec* prevFp = fp->sfp();
  if (LIKELY(prevFp != nullptr)) {
    if (prevSp) {
      if (UNLIKELY(fp->resumed())) {
        assert(fp->func()->isGenerator());
        *prevSp = (TypedValue*)prevFp - prevFp->func()->numSlotsInFrame();
      } else {
        *prevSp = (TypedValue*)(fp + 1);
      }
    }
    if (prevPc) *prevPc = prevFp->func()->base() + fp->m_soff;
    if (fromVMEntry) *fromVMEntry = false;
    return prevFp;
  }
  // Linear search from end of m_nestedVMs. In practice, we're probably
  // looking for something recently pushed.
  int i = m_nestedVMs.size() - 1;
  ActRec* firstAR = vmFirstAR();
  while (i >= 0 && firstAR != fp) {
    firstAR = m_nestedVMs[i--].firstAR;
  }
  if (i == -1) return nullptr;
  const VMState& vmstate = m_nestedVMs[i];
  prevFp = vmstate.fp;
  assert(prevFp);
  assert(prevFp->func()->unit());
  if (prevSp) *prevSp = vmstate.sp;
  if (prevPc) {
    *prevPc = prevFp->func()->unit()->offsetOf(vmstate.pc);
  }
  if (fromVMEntry) *fromVMEntry = true;
  return prevFp;
}

/*
  Instantiate hoistable classes and functions.
  If there is any more work left to do, setup a
  new frame ready to execute the pseudomain.

  return true iff the pseudomain needs to be executed.
*/
bool ExecutionContext::evalUnit(Unit* unit, PC& pc, int funcType) {
  vmpc() = pc;
  unit->merge();
  if (unit->isMergeOnly()) {
    Stats::inc(Stats::PseudoMain_Skipped);
    *vmStack().allocTV() = *unit->getMainReturn();
    return false;
  }
  Stats::inc(Stats::PseudoMain_Executed);

  ActRec* ar = vmStack().allocA();
  assert((uintptr_t)&ar->m_func < (uintptr_t)&ar->m_r);
  Class* cls = liveClass();
  if (vmfp()->hasThis()) {
    // cheng-hack: this can be a bummer, check carefully
    if (UNLIKELY(vmfp()->isMultiThis())) {
      auto mthis_ = vmfp()->getThisMulti(); // cheng-hack: no idea
      for (auto it : *mthis_) {
        it->incRefCount();
      }
      ar->setThisMulti(mthis_);
    } else {
      // original case
    ObjectData *this_ = vmfp()->getThisSingle(); // cheng-hack: no idea
    this_->incRefCount();
    ar->setThisSingle(this_);
    }
  } else if (vmfp()->hasClass()) {
    ar->setClass(vmfp()->getClass());
  } else {
    ar->setThisSingle(nullptr);
  }
  Func* func = unit->getMain(cls);
  assert(!func->isCPPBuiltin());
  ar->m_func = func;
  ar->initNumArgs(0);
  assert(vmfp());
  assert(!vmfp()->hasInvName());
  ar->setReturn(vmfp(), pc, mcg->tx().uniqueStubs.retHelper);
  pushLocalsAndIterators(func);
  if (!vmfp()->hasVarEnv()) {
    vmfp()->setVarEnv(VarEnv::createLocal(vmfp()));
  }
  ar->m_varEnv = vmfp()->m_varEnv;
  ar->m_varEnv->enterFP(vmfp(), ar);

  vmfp() = ar;
  pc = func->getEntry();
  vmpc() = pc;
  bool ret = EventHook::FunctionCall(vmfp(), funcType);
  pc = vmpc();
  checkStack(vmStack(), func, 0);
  return ret;
}

StaticString
  s_php_namespace("<?php namespace "),
  s_curly_return(" { return "),
  s_semicolon_curly("; }"),
  s_php_return("<?php return "),
  s_semicolon(";");

const Variant& ExecutionContext::getEvaledArg(const StringData* val,
                                         const String& namespacedName) {
  auto key = StrNR(val);

  if (m_evaledArgs.get()) {
    const Variant& arg = m_evaledArgs.get()->get(key);
    if (&arg != &null_variant) return arg;
  }

  String code;
  int pos = namespacedName.rfind('\\');
  if (pos != -1) {
    auto ns = namespacedName.substr(0, pos);
    code = s_php_namespace + ns + s_curly_return + key + s_semicolon_curly;
  } else {
    code = s_php_return + key + s_semicolon;
  }
  Unit* unit = compileEvalString(code.get());
  assert(unit != nullptr);
  Variant v;
  // Default arg values are not currently allowed to depend on class context.
  g_context->invokeFunc((TypedValue*)&v, unit->getMain(),
                          init_null_variant, nullptr, nullptr, nullptr, nullptr,
                          InvokePseudoMain);
  Variant &lv = m_evaledArgs.lvalAt(key, AccessFlags::Key);
  lv = v;
  return lv;
}

void ExecutionContext::recordLastError(const Exception &e, int errnum) {
  m_lastError = String(e.getMessage());
  m_lastErrorNum = errnum;
  m_lastErrorPath = String::attach(getContainingFileName());
  m_lastErrorLine = getLine();
}

void ExecutionContext::clearLastError() {
  m_lastError = String();
  m_lastErrorNum = 0;
  m_lastErrorPath = staticEmptyString();
  m_lastErrorLine = 0;
}

/*
 * Helper for function entry, including pseudo-main entry.
 */
void pushLocalsAndIterators(const Func* func, int nparams /*= 0*/) {
  // Push locals.
  for (int i = nparams; i < func->numLocals(); i++) {
    vmStack().pushUninit();
  }
  // Push iterators.
  for (int i = 0; i < func->numIterators(); i++) {
    vmStack().allocI();
  }
}

void ExecutionContext::enqueueAPCHandle(APCHandle* handle, size_t size) {
  assert(handle->isUncounted() && size > 0);
  assert(handle->type() == KindOfString ||
         handle->type() == KindOfArray);
  m_apcHandles.push_back(handle);
  m_apcMemSize += size;
}

// Treadmill solution for the SharedVariant memory management
namespace {
class FreedAPCHandle {
  size_t m_memSize;
  std::vector<APCHandle*> m_apcHandles;
public:
  explicit FreedAPCHandle(std::vector<APCHandle*>&& shandles, size_t size)
    : m_memSize(size), m_apcHandles(std::move(shandles))
  {}
  void operator()() {
    for (auto handle : m_apcHandles) {
      APCTypedValue::fromHandle(handle)->deleteUncounted();
    }
    APCStats::getAPCStats().removePendingDelete(m_memSize);
  }
};
}

void ExecutionContext::manageAPCHandle() {
  assert(apcExtension::UseUncounted || m_apcHandles.size() == 0);
  if (m_apcHandles.size() > 0) {
    std::vector<APCHandle*> handles;
    handles.swap(m_apcHandles);
    Treadmill::enqueue(
      FreedAPCHandle(std::move(handles), m_apcMemSize)
    );
    APCStats::getAPCStats().addPendingDelete(m_apcMemSize);
  }
}

void ExecutionContext::destructObjects() {
  if (UNLIKELY(RuntimeOption::EnableObjDestructCall)) {
    while (!m_liveBCObjs.empty()) {
      ObjectData* obj = *m_liveBCObjs.begin();
      obj->destruct(); // Let the instance remove the node.
    }
    m_liveBCObjs.clear();
  }
}

// Evaled units have a footprint in the TC and translation metadata. The
// applications we care about tend to have few, short, stereotyped evals,
// where the same code keeps getting eval'ed over and over again; so we
// keep around units for each eval'ed string, so that the TC space isn't
// wasted on each eval.
typedef RankedCHM<StringData*, HPHP::Unit*,
        StringDataHashCompare,
        RankEvaledUnits> EvaledUnitsMap;
static EvaledUnitsMap s_evaledUnits;
Unit* ExecutionContext::compileEvalString(
    StringData* code,
    const char* evalFilename /* = nullptr */) {
  EvaledUnitsMap::accessor acc;
  // Promote this to a static string; otherwise it may get swept
  // across requests.
  code = makeStaticString(code);
  if (s_evaledUnits.insert(acc, code)) {
    acc->second = compile_string(
      code->data(),
      code->size(),
      evalFilename
    );
  }
  return acc->second;
}

StrNR ExecutionContext::createFunction(const String& args,
                                       const String& code) {
  if (UNLIKELY(RuntimeOption::EvalAuthoritativeMode)) {
    // Whole program optimizations need to assume they can see all the
    // code.
    raise_error("You can't use create_function in RepoAuthoritative mode; "
                "use a closure instead");
  }

  VMRegAnchor _;
  // It doesn't matter if there's a user function named __lambda_func; we only
  // use this name during parsing, and then change it to an impossible name
  // with a NUL byte before we merge it into the request's func map.  This also
  // has the bonus feature that the value of __FUNCTION__ inside the created
  // function will match Zend. (Note: Zend will actually fatal if there's a
  // user function named __lambda_func when you call create_function. Huzzah!)
  static StringData* oldName = makeStaticString("__lambda_func");
  std::ostringstream codeStr;
  codeStr << "<?php function " << oldName->data()
          << "(" << args.data() << ") {"
          << code.data() << "}\n";
  std::string evalCode = codeStr.str();
  Unit* unit = compile_string(evalCode.data(), evalCode.size());
  // Move the function to a different name.
  std::ostringstream newNameStr;
  newNameStr << '\0' << "lambda_" << ++m_lambdaCounter;
  StringData* newName = makeStaticString(newNameStr.str());
  unit->renameFunc(oldName, newName);
  m_createdFuncs.push_back(unit);
  unit->merge();

  // Technically we shouldn't have to eval the unit right now (it'll execute
  // the pseudo-main, which should be empty) and could get away with just
  // mergeFuncs. However, Zend does it this way, as proven by the fact that you
  // can inject code into the evaled unit's pseudo-main:
  //
  //   create_function('', '} echo "hi"; if (0) {');
  //
  // We have to eval now to emulate this behavior.
  TypedValue retval;
  invokeFunc(&retval, unit->getMain(), init_null_variant,
             nullptr, nullptr, nullptr, nullptr,
             InvokePseudoMain);

  // __lambda_func will be the only hoistable function.
  // Any functions or closures defined in it will not be hoistable.
  Func* lambda = unit->firstHoistable();
  return lambda->nameStr();
}

bool ExecutionContext::evalPHPDebugger(TypedValue* retval,
                                       StringData* code,
                                       int frame) {
  assert(retval);
  // The code has "<?php" prepended already
  Unit* unit = compile_string(code->data(), code->size());
  if (unit == nullptr) {
    raise_error("Syntax error");
    tvWriteNull(retval);
    return true;
  }

  // Do not JIT this unit, we are using it exactly once.
  unit->setInterpretOnly();
  return evalPHPDebugger(retval, unit, frame);
}

bool ExecutionContext::evalPHPDebugger(TypedValue* retval,
                                       Unit* unit,
                                       int frame) {
  assert(retval);

  bool failed = true;
  ActRec *fp = vmfp();
  if (fp) {
    for (; frame > 0; --frame) {
      ActRec* prevFp = getPrevVMStateUNSAFE(fp);
      if (!prevFp) {
        // To be safe in case we failed to get prevFp. This would mean we've
        // been asked to eval in a frame which is beyond the top of the stack.
        // This suggests the debugger client has made an error.
        break;
      }
      fp = prevFp;
    }
    if (!fp->hasVarEnv()) {
      fp->setVarEnv(VarEnv::createLocal(fp));
    }
  }
  ObjectData *this_ = nullptr;
  // NB: the ActRec and function within the AR may have different classes. The
  // class in the ActRec is the type used when invoking the function (i.e.,
  // Derived in Derived::Foo()) while the class obtained from the function is
  // the type that declared the function Foo, which may be Base. We need both
  // the class to match any object that this function may have been invoked on,
  // and we need the class from the function execution is stopped in.
  Class *frameClass = nullptr;
  Class *functionClass = nullptr;
  if (fp) {
    if (fp->hasThis()) {
      this_ = fp->getThisSingle(); // cheng-hack: no idea
    } else if (fp->hasClass()) {
      frameClass = fp->getClass();
    }
    functionClass = fp->m_func->cls();
    phpDebuggerEvalHook(fp->m_func);
  }

  const static StaticString s_cppException("Hit an exception");
  const static StaticString s_phpException("Hit a php exception");
  const static StaticString s_exit("Hit exit");
  const static StaticString s_fatal("Hit fatal");
  try {
    // Start with the correct parent FP so that VarEnv can properly exitFP().
    // Note that if the same VarEnv is used across multiple frames, the most
    // recent FP must be used. This can happen if we are trying to debug
    // an eval() call or a call issued by debugger itself.
    auto savedFP = vmfp();
    if (fp) {
      vmfp() = fp->m_varEnv->getFP();
    }
    SCOPE_EXIT { vmfp() = savedFP; };

    // Invoke the given PHP, possibly specialized to match the type of the
    // current function on the stack, optionally passing a this pointer or
    // class used to execute the current function.
    invokeFunc(retval, unit->getMain(functionClass), init_null_variant,
               this_, frameClass, fp ? fp->m_varEnv : nullptr, nullptr,
               InvokePseudoMain);
    failed = false;
  } catch (FatalErrorException &e) {
    g_context->write(s_fatal);
    g_context->write(" : ");
    g_context->write(e.getMessage().c_str());
    g_context->write("\n");
    g_context->write(ExtendedLogger::StringOfStackTrace(e.getBacktrace()));
  } catch (ExitException &e) {
    g_context->write(s_exit.data());
    g_context->write(" : ");
    std::ostringstream os;
    os << ExitException::ExitCode;
    g_context->write(os.str());
  } catch (Eval::DebuggerException &e) {
  } catch (Exception &e) {
    g_context->write(s_cppException.data());
    g_context->write(" : ");
    g_context->write(e.getMessage().c_str());
    ExtendedException* ee = dynamic_cast<ExtendedException*>(&e);
    if (ee) {
      g_context->write("\n");
      g_context->write(
        ExtendedLogger::StringOfStackTrace(ee->getBacktrace()));
    }
  } catch (Object &e) {
    g_context->write(s_phpException.data());
    g_context->write(" : ");
    g_context->write(e->invokeToString().data());
  } catch (...) {
    g_context->write(s_cppException.data());
  }
  return failed;
}

void ExecutionContext::enterDebuggerDummyEnv() {
  static Unit* s_debuggerDummy = compile_string("<?php?>", 7);
  // Ensure that the VM stack is completely empty (vmfp() should be null)
  // and that we're not in a nested VM (reentrancy)
  assert(vmfp() == nullptr);
  assert(m_nestedVMs.size() == 0);
  assert(m_nesting == 0);
  assert(vmStack().count() == 0);
  ActRec* ar = vmStack().allocA();
  ar->m_func = s_debuggerDummy->getMain();
  ar->initNumArgs(0);
  ar->setThisSingle(nullptr);
  ar->setReturnVMExit();
  vmfp() = ar;
  vmpc() = s_debuggerDummy->entry();
  vmFirstAR() = ar;
  vmfp()->setVarEnv(m_globalVarEnv);
  m_globalVarEnv->enterFP(nullptr, vmfp());
}

void ExecutionContext::exitDebuggerDummyEnv() {
  assert(m_globalVarEnv);
  // Ensure that vmfp() is valid
  assert(vmfp() != nullptr);
  // Ensure that vmfp() points to the only frame on the call stack.
  // In other words, make sure there are no VM frames directly below
  // this one and that we are not in a nested VM (reentrancy)
  assert(!vmfp()->sfp());
  assert(m_nestedVMs.size() == 0);
  assert(m_nesting == 0);
  // Teardown the frame we erected by enterDebuggerDummyEnv()
  const Func* func = vmfp()->m_func;
  try {
    frame_free_locals_inl_no_hook<true>(vmfp(), func->numLocals());
  } catch (...) {}
  vmStack().ndiscard(func->numSlotsInFrame());
  vmStack().discardAR();
  // After tearing down this frame, the VM stack should be completely empty
  assert(vmStack().count() == 0);
  vmfp() = nullptr;
  vmpc() = nullptr;
}

// Walk the stack and find any return address to jitted code and bash it to
// the appropriate RetFromInterpreted*Frame helper. This ensures that we don't
// return into jitted code and gives the system the proper chance to interpret
// blacklisted tracelets.
void ExecutionContext::preventReturnsToTC() {
  assert(isDebuggerAttached());
  if (RuntimeOption::EvalJit) {
    ActRec *ar = vmfp();
    while (ar) {
      preventReturnToTC(ar);
      ar = getPrevVMStateUNSAFE(ar);
    }
  }
}

// Bash the return address for the given actrec into the appropriate
// RetFromInterpreted*Frame helper.
void ExecutionContext::preventReturnToTC(ActRec* ar) {
  assert(isDebuggerAttached());
  if (!RuntimeOption::EvalJit) {
    return;
  }

  if (!isReturnHelper(reinterpret_cast<void*>(ar->m_savedRip)) &&
      (mcg->isValidCodeAddress((jit::TCA)ar->m_savedRip))) {
    TRACE_RB(2, "Replace RIP in fp %p, savedRip 0x%" PRIx64 ", "
             "func %s\n", ar, ar->m_savedRip,
             ar->m_func->fullName()->data());
    if (ar->resumed()) {
      ar->m_savedRip =
        reinterpret_cast<uintptr_t>(mcg->tx().uniqueStubs.genRetHelper);
    } else {
      ar->m_savedRip =
        reinterpret_cast<uintptr_t>(mcg->tx().uniqueStubs.retHelper);
    }
    assert(isReturnHelper(reinterpret_cast<void*>(ar->m_savedRip)));
  }
}

static inline StringData* lookup_name(TypedValue* key) {
  return prepareKey(*key);
}

static inline void lookup_var(ActRec* fp,
                              StringData*& name,
                              TypedValue* key,
                              TypedValue*& val) {
  name = lookup_name(key);
  const Func* func = fp->m_func;
  Id id = func->lookupVarId(name);
  if (id != kInvalidId) {
    val = frame_local(fp, id);
  } else {
    assert(!fp->hasInvName());
    if (fp->hasVarEnv()) {
      val = fp->m_varEnv->lookup(name);
    } else {
      val = nullptr;
    }
  }
}

static inline void lookupd_var(ActRec* fp,
                               StringData*& name,
                               TypedValue* key,
                               TypedValue*& val) {
  name = lookup_name(key);
  const Func* func = fp->m_func;
  Id id = func->lookupVarId(name);
  if (id != kInvalidId) {
    val = frame_local(fp, id);
  } else {
    assert(!fp->hasInvName());
    if (!fp->hasVarEnv()) {
      fp->setVarEnv(VarEnv::createLocal(fp));
    }
    val = fp->m_varEnv->lookup(name);
    if (val == nullptr) {
      TypedValue tv;
      tvWriteNull(&tv);
      fp->m_varEnv->set(name, &tv);
      val = fp->m_varEnv->lookup(name);
    }
  }
}

static inline void lookup_gbl(ActRec* fp,
                              StringData*& name,
                              TypedValue* key,
                              TypedValue*& val) {
  name = lookup_name(key);
  assert(g_context->m_globalVarEnv);
  val = g_context->m_globalVarEnv->lookup(name);
}

static inline void lookupd_gbl(ActRec* fp,
                               StringData*& name,
                               TypedValue* key,
                               TypedValue*& val) {
  name = lookup_name(key);
  assert(g_context->m_globalVarEnv);
  VarEnv* varEnv = g_context->m_globalVarEnv;
  val = varEnv->lookup(name);
  if (val == nullptr) {
    TypedValue tv;
    tvWriteNull(&tv);
    varEnv->set(name, &tv);
    val = varEnv->lookup(name);
  }
}

static inline void lookup_sprop(ActRec* fp,
                                TypedValue* clsRef,
                                StringData*& name,
                                TypedValue* key,
                                TypedValue*& val,
                                bool& visible,
                                bool& accessible) {
  assert(clsRef->m_type == KindOfClass);
  name = lookup_name(key);
  auto const ctx = arGetContextClass(fp);

  auto const lookup = clsRef->m_data.pcls->getSProp(ctx, name);

  val = lookup.prop;
  visible = lookup.prop != nullptr;
  accessible = lookup.accessible;
}

static inline void lookupClsRef(TypedValue* input,
                                TypedValue* output,
                                bool decRef = false) {
  const Class* class_ = nullptr;
  if (IS_STRING_TYPE(input->m_type)) {
    class_ = Unit::loadClass(input->m_data.pstr);
    if (class_ == nullptr) {
      output->m_type = KindOfNull;
      raise_error(Strings::UNKNOWN_CLASS, input->m_data.pstr->data());
    }
  } else if (input->m_type == KindOfObject) {
    class_ = input->m_data.pobj->getVMClass();
  } else {
    output->m_type = KindOfNull;
    raise_error("Cls: Expected string or object");
  }
  if (decRef) {
    tvRefcountedDecRef(input);
  }
  output->m_data.pcls = const_cast<Class*>(class_);
  output->m_type = KindOfClass;
}

static UNUSED int innerCount(const TypedValue* tv) {
  if (IS_REFCOUNTED_TYPE(tv->m_type)) {
    if (tv->m_type == KindOfRef) {
      return tv->m_data.pref->getRealCount();
    } else {
      return tv->m_data.pref->getCount();
    }
  }
  return -1;
}

static inline void ratchetRefs(TypedValue*& result, TypedValue& tvRef,
                               TypedValue& tvRef2) {
  TRACE(5, "Ratchet: result %p(k%d c%d), ref %p(k%d c%d) ref2 %p(k%d c%d)\n",
        result, result->m_type, innerCount(result),
        &tvRef, tvRef.m_type, innerCount(&tvRef),
        &tvRef2, tvRef2.m_type, innerCount(&tvRef2));
  // Due to complications associated with ArrayAccess, it is possible to acquire
  // a reference as a side effect of vector operation processing. Such a
  // reference must be retained until after the next iteration is complete.
  // Therefore, move the reference from tvRef to tvRef2, so that the reference
  // will be released one iteration later. But only do this if tvRef was used in
  // this iteration, otherwise we may wipe out the last reference to something
  // that we need to stay alive until the next iteration.
  if (tvRef.m_type != KindOfUninit) {
    if (IS_REFCOUNTED_TYPE(tvRef2.m_type)) {
      tvDecRef(&tvRef2);
      TRACE(5, "Ratchet: decref tvref2\n");
      tvWriteUninit(&tvRef2);
    }

    memcpy(&tvRef2, &tvRef, sizeof(TypedValue));
    tvWriteUninit(&tvRef);
    // Update result to point to relocated reference. This can be done
    // unconditionally here because we maintain the invariant throughout that
    // either tvRef is KindOfUninit, or tvRef contains a valid object that
    // result points to.
    assert(result == &tvRef);
    result = &tvRef2;
  }
}

// cheng-hack: for staticEmptyArray check
extern std::aligned_storage<
  sizeof(ArrayData),
  alignof(ArrayData)
>::type s_theEmptyArray;

inline bool
checkStaticEmptyArray(TypedValue* tvp) {
  if(tvToCell(tvp)->m_type == KindOfArray && 
     (void*) tvToCell(tvp)->m_data.parr == (void*) &s_theEmptyArray)
  {
    return true;
  }
  return false;
}

struct MemberState {
  unsigned ndiscard;
  MemberCode mcode{MEL};
  TypedValue* base;
  // cheng-hack:
  // used to check which is good: base or base_list
  //   false: normal case
  //   true: base will store the very first base, in order to provide the mapping
  bool isMultiBase;
  bool isVGetM;
  sptr< std::vector<TypedValue*> > base_list; // ONLY used for multiVal
  TypedValue* orig_base;
  TypedValue scratch;
  TypedValue literal;
  Variant ref;
  Variant ref2;
  TypedValue* curMember{nullptr};
};

enum class VectorLeaveCode {
  ConsumeAll,
  LeaveLast
};

template <bool setMember, bool warn, bool define, bool unset, bool reffy,
          unsigned mdepth, // extra args on stack for set (e.g. rhs)
          VectorLeaveCode mleave, bool saveResult>
OPTBLD_INLINE bool memberHelperPre(PC& pc, MemberState& mstate) {
  // The caller must move pc to the vector immediate before calling
  // {get, set}HelperPre.
  const ImmVector immVec = ImmVector::createFromStream(pc);
  const uint8_t* vec = immVec.vec();
  assert(immVec.size() > 0);

  // PC needs to be advanced before we do anything, otherwise if we
  // raise a notice in the middle of this we could resume at the wrong
  // instruction.

  // cheng: prepare for the isMultiIndex but !isMultiBase
  auto init_pc = pc;
  auto init_vec = vec;
  bool read_multi_indx_from_single_base = false;
multi_index_start:
  pc += immVec.size() + sizeof(int32_t) + sizeof(int32_t);

  if (!setMember) {
    assert(mdepth == 0);
    assert(!define);
    assert(!unset);
  }

  mstate.ndiscard = immVec.numStackValues();
  int depth = mdepth + mstate.ndiscard - 1;
  const LocationCode lcode = LocationCode(*vec++);

  TypedValue* loc = nullptr;
  Class* const ctx = arGetContextClass(vmfp());

  StringData* name;
  TypedValue* fr = nullptr;
  TypedValue* cref;
  TypedValue* pname;
  tvWriteUninit(&mstate.scratch);

  // find the base
  switch (lcode) {
  case LNL:
    loc = frame_local_inner(vmfp(), decodeVariableSizeImm(&vec));
    goto lcodeName;
  case LNC:
    loc = vmStack().indTV(depth--);
    goto lcodeName;

  lcodeName:
    if (define) {
      lookupd_var(vmfp(), name, loc, fr);
    } else {
      lookup_var(vmfp(), name, loc, fr);
    }
    if (fr == nullptr) {
      if (warn) {
        raise_notice(Strings::UNDEFINED_VARIABLE, name->data());
      }
      tvWriteNull(&mstate.scratch);
      loc = &mstate.scratch;
    } else {
      loc = fr;
    }
    decRefStr(name);
    break;

  case LGL:
    loc = frame_local_inner(vmfp(), decodeVariableSizeImm(&vec));
    goto lcodeGlobal;
  case LGC:
    loc = vmStack().indTV(depth--);
    goto lcodeGlobal;

  lcodeGlobal:
    if (define) {
      lookupd_gbl(vmfp(), name, loc, fr);
    } else {
      lookup_gbl(vmfp(), name, loc, fr);
    }
    if (fr == nullptr) {
      if (warn) {
        raise_notice(Strings::UNDEFINED_VARIABLE, name->data());
      }
      tvWriteNull(&mstate.scratch);
      loc = &mstate.scratch;
    } else {
      loc = fr;
    }
    decRefStr(name);
    break;

  case LSC:
    cref = vmStack().indTV(mdepth);
    pname = vmStack().indTV(depth--);
    goto lcodeSprop;
  case LSL:
    cref = vmStack().indTV(mdepth);
    pname = frame_local_inner(vmfp(), decodeVariableSizeImm(&vec));
    goto lcodeSprop;

  lcodeSprop: {
    assert(cref->m_type == KindOfClass);
    auto const class_ = cref->m_data.pcls;
    auto const name = lookup_name(pname);
    auto const lookup = class_->getSProp(ctx, name);
    loc = lookup.prop;
    if (!lookup.prop || !lookup.accessible) {
      raise_error("Invalid static property access: %s::%s",
                  class_->name()->data(),
                  name->data());
    }
    decRefStr(name);
    break;
  }

  case LL: {
    int localInd = decodeVariableSizeImm(&vec);
    loc = frame_local_inner(vmfp(), localInd);
    if (warn) {
      if (loc->m_type == KindOfUninit) {
        raise_notice(Strings::UNDEFINED_VARIABLE,
                     vmfp()->m_func->localVarName(localInd)->data());
      }
    }
    break;
  }
  case LC:
  case LR:
    loc = vmStack().indTV(depth--);
    break;
  case LH:
    assert(vmfp()->hasThis());
    // cheng-hack: provide multi this support
    if (UNLIKELY(vmfp()->isMultiThis())) {
#ifdef CHENG_INS_DEBUG
      debug_log << "    We encounter multi-this as base\n";
#endif
      mstate.scratch = genMultiVal(vmfp()->getThisMulti());
      loc = &mstate.scratch;
    } else {
#ifdef CHENG_INS_DEBUG
      debug_log << "    We encounter this as base\n";
#endif
      // normal case
    mstate.scratch.m_type = KindOfObject;
    mstate.scratch.m_data.pobj = vmfp()->getThisSingle(); // cheng-hack: should be single
    loc = &mstate.scratch;
    }
    break;

  case InvalidLocationCode:
    not_reached();
  }

  // base found, save to mstate.base
  mstate.base = loc;
  tvWriteUninit(&mstate.literal);
  tvWriteUninit(mstate.ref.asTypedValue());
  tvWriteUninit(mstate.ref2.asTypedValue());

  // Used to be a BUG. Why do we need deref? but original doesn't?
  if (UNLIKELY(mstate.base->m_type == KindOfRef)) {
    mstate.base = tvToCell(mstate.base);
  }
  // We check if mutli-to-one-ref-or-obj happen
  if (UNLIKELY(mstate.base->m_type == KindOfMulti &&
               (mstate.base->m_data.pmulti->getType() == KindOfRef ||
                mstate.base->m_data.pmulti->getType() == KindOfObject))) {
    TypedValue* first_elem = tvToCell(mstate.base->m_data.pmulti->getByVal(0));
    // check if we have same ret
    bool found_same_ref_obj = true;
    for (int i=1; i<mstate.base->m_data.pmulti->valSize(); i++) {
      if (first_elem->m_data.num != tvToCell(mstate.base->m_data.pmulti->getByVal(i))->m_data.num) {
        found_same_ref_obj = false; break;
      }
    }
    // if mstate.base point to one obj/ref, shrink it
    if (found_same_ref_obj) {
      mstate.base = first_elem;
#ifdef CHENG_INS_ONLY_DEBUG
      debug_log << "   memberHelperPre: found_same_ref_obj, shrink to one\n";
#endif
    }
  }

  // cheng-hack:
  // ASSUME: only the base can be multi-value
  // EXCEPT: the base is a system array (e.g. $_SERVER)
  auto base = mstate.base;
  auto base_type = base->m_type;
  bool isMultiBase = (base_type == KindOfMulti);
  bool isMultiIndex = false;
  bool isMultiInternal = false;

  // (1) Preserve the initial environment 
  // (2) Iterate the value in multiVal and collect the result
  // (3) Use mstate.base_list instead of base (except for CGetM which set the saveResult)

  // curtis:
  mstate.orig_base = mstate.base;

  // Prepare for multi cascading indexing
  int iter_counter = 0, multi_size = 0;
  // these two field of mstate is tricky, since mstate will be reset several times
  mstate.isMultiBase = isMultiBase;

  struct MemberState orig_mstate;

  // remember all the pointer inside the struct is point to the original
  // memory slots, which may be messed up after one iteration.
  // If you have any BUG, please check here to see if you are using
  // any pointer in orig_mstate which can be really bad idea.
  // we have to do it here, for case multi-index-single-base
  memcpy(&orig_mstate, &mstate, sizeof(struct MemberState) );

  // save the original variables
  const uint8_t* orig_vec = vec;
  int orig_depth = depth; 

  // single_mode_on:
  // There are two things: (1) base is multi, (2) index is multi
  if (UNLIKELY(single_mode_on)) {
#ifdef CHENG_INS_DEBUG
    debug_log << "    In single mode, mode iter: " << single_mode_cur_iter << "\n";
#endif
    if (isMultiBase && mstate.scratch.m_type == KindOfMulti) {
      // NOTE: this is the only case which scratch is non-trival:
      // We got a multi-this as the base
      TypedValue *nexttv = orig_mstate.base->m_data.pmulti->getByVal(single_mode_cur_iter);
      tvCopy(*nexttv, mstate.scratch);
      mstate.base = &mstate.scratch;
    } else if (isMultiBase) {
      // other cases
      mstate.base = orig_mstate.base->m_data.pmulti->getByVal(single_mode_cur_iter);
    }
    mstate.isMultiBase = false;
    isMultiBase = false;
  }

  // NOTE2: multi-to-one-obj problem & multi-array-same-slot problem
  // for multi-array-same-slot problem, there are three cases:
  //  -- the return values are from a multi-array (might have point to the same array,
  //  lazy copy), which should not shrink to one.
  //  -- the return values are from a single-array with multi-array-single-obj as parent,
  //  which should shrink to one (so that it will be OK for GetM, but will be split by SetM)
  static std::vector<void*> iter_last_obj_ref;

multi_begin:
  if (UNLIKELY(isMultiBase || isMultiIndex || isMultiInternal)) {

    static TypedValue read_result = {0}; // used for CGetM only (saveResult)
    static sptr< std::vector<TypedValue*> > multi_base_ptr = nullptr;

    // initialization
    if (iter_counter == 0) {
      START;
      AS_MMEMBER;
#ifdef CHENG_INS_ONLY_DEBUG
      if (isMultiBase) {
        debug_log << "  Cascading Indexing meets a multi-base\n";
#ifdef CHENG_INS_DEBUG
        debug_log << "     multiVal is:\n" << mstate.base->m_data.pmulti->dump("    ");
#endif
      } else if (isMultiIndex) {
        debug_log << "    Single-base multi-index\n";
      } else if (isMultiInternal) {
        debug_log << "    Single-base multi-value\n";
      }
#endif
      // isMultiInternal for the case $obj->multi_arr
      if (isMultiBase || isMultiInternal) {
        multi_size = mstate.base->m_data.pmulti->valSize();
        orig_vec = vec;
        orig_depth = depth; 
        /*
         * In order to fix the following case:
         *   $new_arr = $old_multi_arr;
         *   unset($new_arr[0]); // or any other write 
         * This may affect the $old_multi_arr, since the multi-array ref is >1,
         * but the array within multival might be still 1.
         */
        if (UNLIKELY(setMember && isMultiBase)) {
          auto pmulti = mstate.base->m_data.pmulti;
          if (pmulti->getType() == KindOfArray &&
              pmulti->getCount() > 1 /*&&
              pmulti->getByVal(0)->m_data.parr->getCount() == 1*/) {
            // used to be a performance BUG: clone will not be freed
            // Actually, clone will not solve the problem either!
            //*mstate.base = MultiVal::cloneMultiVal(mstate.base);

            // TODO: need to check the correctness of following code
            // current solution, add all array within by 1:
            auto tmp = in_makeMultiVal(pmulti->valSize(), KindOfUninit);
            cheng_assert(multi_size==pmulti->valSize());
            for(int i=0; i<multi_size; i++) {
              tvDup(*pmulti->getByVal(i), *tmp.m_data.pmulti->getByVal(i));
            }
            in_adjust_type(tmp.m_data.pmulti);
            *mstate.base = tmp;
          }
        }
      }
      cheng_assert(multi_size != 0);

      if (multi_base_ptr != nullptr) {
        multi_base_ptr->clear();
      } else {
        multi_base_ptr = std::make_shared< std::vector<TypedValue*> >();
      }
      read_result = in_makeMultiVal(multi_size, KindOfUninit);

      // This is for finding multi value (MultiInternal) in the middle of the procedure.
      // copy current environment, if we find multi during loop
      if (!isMultiBase && isMultiInternal) {
        mstate.isMultiBase = true;
        memcpy(&orig_mstate, &mstate, sizeof(struct MemberState) );
      }
      // This is for finding multi-index in the middle of the procedure.
      // If isMultiIndex ONLY, then
      // Must be: (1) read (2) return NULL
      // copy current environment
      if (!isMultiBase && !isMultiInternal && isMultiIndex) {
        cheng_assert(!setMember); // must be read
        read_multi_indx_from_single_base = true; // must be NULL
        // collect all the results
        mstate.isMultiBase = true;
        memcpy(&orig_mstate, &mstate, sizeof(struct MemberState) );
      }

      // if(setMember):
      // if !isMultiBase && isMultiIndex, it should be split during
      // finding the isMultiIndex, then isMultiBase should = true.
      // Never (!isMultiBase && isMultiIndex)
      if (setMember) {
        cheng_assert( (!isMultiBase && isMultiIndex) == false);
      }

      // see NOTE2
      // since this is static variable (for performance reason), we clear first
      iter_last_obj_ref.clear();
    } else {
      // after at lease one iteration
      // collect the result
#ifdef CHENG_INS_DEBUG
      debug_log << "  Round[" << iter_counter << "], result is:" 
        << mstate.base->pretty() << "\n";
#endif
      if (saveResult) {
        // CGetM, if we have seen a ref, we should deref here! (Why?)
        // Because: like cgetl, they need deref.
        //read_result.m_data.pmulti->addValue(*tvToCell(mstate.base));
        tvDup(*tvToCell(mstate.base), *read_result.m_data.pmulti->getByVal(iter_counter-1));
      } else {
        // Others
        if (mstate.base == &mstate.scratch) {
          // Used to be a BUG, that only the last obj is modified, since
          // the base pointer of obj is point to the TypedValue mstate.scratch
          cheng_assert(orig_mstate.scratch.m_type == KindOfMulti);
          auto cur_this = orig_mstate.scratch.m_data.pmulti->getByVal(iter_counter-1);
          multi_base_ptr->push_back(cur_this);
        } else {
          multi_base_ptr->push_back(mstate.base);
        }
#ifdef CHENG_CHECK
        // FIXME: is this universeal truth?
        if ((*multi_base_ptr)[0]->m_type != mstate.base->m_type) {
          std::cout << "Different types, used to be " << (*multi_base_ptr)[0]->pretty() 
            << " and now is " << mstate.base->pretty() << "\n";
          cheng_assert(false);
        }
#endif
      }
    }

    // check if the end
    if (iter_counter >= multi_size) {
      // end of the cascading indexing, mstate is the one who return value
      // if saveResult, save the result to scratch
      if (saveResult) {
        in_adjust_type(read_result.m_data.pmulti);
        // decide the type
        // check if the results are the same, shrink them if true
        auto single = read_result.m_data.pmulti->shrinkToSingle();
        // assert the return values are all NULL
        if (read_multi_indx_from_single_base) {
          cheng_assert(single != nullptr);
          cheng_assert(single->m_type == KindOfNull || single->m_type == KindOfUninit); 
        }
        if (single == nullptr) {
          tvCopy(read_result, mstate.scratch);
        } else {
#ifdef CHENG_INS_DEBUG
          debug_log << "    Shrink the result to single: " << single->pretty() << "\n";
#endif
          tvDup(*single, mstate.scratch);
          // free the read_result
          tvRefcountedDecRef(&read_result);
        }
      } else {
        mstate.base_list = multi_base_ptr;
        mstate.base = orig_mstate.base; // used for get the mapping 

        // It is possible that we got the same "return base" from
        // all iterations. For example:
        //   $multi_arr[$s_obj_indx]->indx = $val;
        // If the final results are the same, we should just return one value
        // check NOTE2
        cheng_assert(iter_last_obj_ref.size() == multi_size);
        cheng_assert(multi_size >= 1);
        // If we meet some ref/obj after multival
        if (iter_last_obj_ref[0] != nullptr) {

          bool same_path = true;
          void* first_ref_obj = iter_last_obj_ref[0];
          for (int i=1; i<multi_size; i++) {
            if (first_ref_obj != iter_last_obj_ref[i]) {
              same_path = false;
              break;
            }
          }

          // staticEmptyArray check: ref->empty_array which are all the same
          // Solution: detect empty_array, and set found_path as false.
          bool is_empty_arr = checkStaticEmptyArray(tvToCell((*mstate.base_list)[0]));
          if (same_path && is_empty_arr) {
            same_path = false;
#ifdef CHENG_INS_ONLY_DEBUG
            debug_log << "    found staticEmptyArray, set same_path to FALSE\n";
#endif
          }

          // if same_path is true, we should have the same ret
          if (same_path) {
#ifdef CHENG_CHECK
            // used to be a BUG: sometime the last elem is a Ref, need to deref
            TypedValue* first_ret_elem = tvToCell((*mstate.base_list)[0]);
            // check if we have same ret
            bool found_same_ret = true;
            for (int i=1; i<multi_size; i++) {
              if (first_ret_elem->m_data.num != tvToCell((*mstate.base_list)[i])->m_data.num) {
                found_same_ret = false; break;
              }
            }

#ifdef CHENG_INS_ONLY_DEBUG 
            if (!found_same_ret) {
              debug_log << "    memberHelperPre: find same_path, but not same_ret!\n"
                << "    same_path ptr: (" << first_ref_obj << ")\n"
                << "    rets are:\n" ;
              for (int i=0; i<multi_size; i++) {
                debug_log << "      [" << i << "] " << tvToCell((*mstate.base_list)[i])->pretty() << "\n";
              }
            }
#endif
            cheng_assert(found_same_ret == same_path);
#endif

            // if we find a single obj shared by multi-container, we must make sure
            // the following cascading indexing without any multi-index.
            // e.g. $multi->single_obj[$multi_index] is prohibitive
#ifdef CHENG_INS_ONLY_DEBUG
            debug_log << "  the same path/ret is found, shrink to isMultiBase=false\n";
#endif
            cheng_assert(!isMultiIndex);
            mstate.isMultiBase = false;
            mstate.base = (*mstate.base_list)[0];
          }
        }
      }

      END;
      return false;
    }

    // construct new mstate
    memcpy(&mstate, &orig_mstate, sizeof(struct MemberState));
    vec = orig_vec;
    depth = orig_depth;
    if (mstate.scratch.m_type == KindOfMulti) {
      // NOTE: this is the only case which scratch is non-trival:
      // We got a multi-this as the base
      TypedValue *nexttv = orig_mstate.base->m_data.pmulti->getByVal(iter_counter);
      tvCopy(*nexttv, mstate.scratch);
      mstate.base = &mstate.scratch;
    } else if (isMultiBase || isMultiInternal) {
      // multi-index do not have multi-this
      // other cases
      mstate.base = orig_mstate.base->m_data.pmulti->getByVal(iter_counter);
    }


    iter_last_obj_ref.push_back(nullptr); // push nullptr as default
    iter_counter++;
  }

  // cheng-hack:
  // sys_arr may have multi-value elements
  // e.g. $_FILES['paperUpload']['tmp_name']
  // Three situations:
  // (1) Good to go: finish the processing, either single value or multi-value at first layer
  // (2) Re-initialize: find cascading indexing in multi-value of first layer
  // (3) Next/End: already de-multiplexing, choose next value

  // Iterate through the members.
  while (vec < pc) {
    // cheng-hack: save for recovery
    auto loop_start_vec = vec;
    auto loop_start_depth = depth;

    mstate.mcode = MemberCode(*vec++);
    if (memberCodeHasImm(mstate.mcode)) {
      int64_t memberImm = decodeMemberCodeImm(&vec, mstate.mcode);
      if (memberCodeImmIsString(mstate.mcode)) {
        tvAsVariant(&mstate.literal) =
          vmfp()->m_func->unit()->lookupLitstrId(memberImm);
        assert(!IS_REFCOUNTED_TYPE(mstate.literal.m_type));
        mstate.curMember = &mstate.literal;
      } else if (mstate.mcode == MEI) {
        tvAsVariant(&mstate.literal) = memberImm;
        mstate.curMember = &mstate.literal;
      } else {
        assert(memberCodeImmIsLoc(mstate.mcode));
        mstate.curMember = frame_local_inner(vmfp(), memberImm);
      }
    } else {
      mstate.curMember = (setMember && mstate.mcode == MW) ? nullptr
                                             : vmStack().indTV(depth--);
    }

    if (mleave == VectorLeaveCode::LeaveLast) {
      if (vec >= pc) {
        assert(vec == pc);
        break;
      }
    }

    // cheng-hack: choose the correct index here 
    if (UNLIKELY(mstate.curMember && mstate.curMember->m_type == KindOfMulti)) {
      if (UNLIKELY(single_mode_on)) {
        mstate.curMember = mstate.curMember->m_data.pmulti->getByVal(single_mode_cur_iter);
      } else if (!isMultiBase && !isMultiIndex && !isMultiInternal) {
#ifdef CHENG_INS_ONLY_DEBUG
        debug_log << "    find multi-index for single-base\n";
#endif
        // we find a multi-index on single-base 
        // two cases:
        //  if (setMember): we split the container, FIXME: do not support object so far
        //  if (!setMember): the only case valid is return empty, FIXME: otherwise, fail
        if (setMember) {
#ifdef CHENG_INS_ONLY_DEBUG
          debug_log << "    split the base (setMember==true)\n";
#endif
          multi_size = mstate.curMember->m_data.pmulti->valSize();
          TypedValue *orig_base = mstate.orig_base;
          // FIXME: need to track obj, do not support here
          if (orig_base->m_type != KindOfArray) {
            std::cout << "\n[ERROR] met a multi-index, for single base: "
              <<  orig_base->pretty() << "\n";
            cheng_assert(false);
          }
          TypedValue split_multi = MultiVal::splitArray(*orig_base, multi_size);
          tvCopy(split_multi, *mstate.orig_base);
          pc = init_pc;
          vec = init_vec;
          goto multi_index_start;
        } else {
          // $a = $single_obj[$multi_ind]
          // NULL is the only option!
#ifdef CHENG_INS_ONLY_DEBUG
          debug_log << "    continue the base (setMember==false)\n";
#endif
          isMultiIndex = true;
          multi_size = mstate.curMember->m_data.pmulti->valSize();
          orig_vec = loop_start_vec;
          orig_depth = loop_start_depth;
          goto multi_begin;
        }
      } else {
        mstate.curMember = mstate.curMember->m_data.pmulti->getByVal(iter_counter-1);
      }
    }

#ifdef CHENG_INS_DEBUG
    auto ind_txt = HHVM_FN(print_r)(tvAsVariant(mstate.curMember), true);
    debug_log << "    ---> index as [" << ind_txt.toString().toCppString() << "]\n";
    //debug_log << "-------------------\n";
    //HHVM_FN(print_r)(tvAsVariant(mstate.base));
    //debug_log << ">>==============\n";
#endif

    /*
    // FIXME: this is used for __get()/__set() with global variable
    single_mode_on = true;
    single_mode_cur_iter = iter_counter-1;
    */
    cheng_assert(mstate.curMember==nullptr || mstate.curMember->m_type != KindOfMulti);
    cheng_assert(mstate.base->m_type != KindOfMulti);

    TypedValue* result;
    switch (mstate.mcode) {
    case MEL:
    case MEC:
    case MET:
    case MEI:
      if (unset) {
        result = ElemU(mstate.scratch, *mstate.ref.asTypedValue(), mstate.base,
                       *mstate.curMember);
      } else if (define) {
        result = ElemD<warn,reffy>(mstate.scratch, *mstate.ref.asTypedValue(),
                                   mstate.base, *mstate.curMember);
      } else {
        result =
          // We're not really going to modify it in the non-D case, so
          // this is safe.
          const_cast<TypedValue*>(
            Elem<warn>(mstate.scratch, *mstate.ref.asTypedValue(),
                       mstate.base, *mstate.curMember)
          );
      }
      break;
    case MPL:
    case MPC:
    case MPT:
      result = Prop<warn,define,unset>(
          mstate.scratch, *mstate.ref.asTypedValue(), ctx, mstate.base,
          *mstate.curMember
      );
      break;
    case MW:
      if (setMember) {
        assert(define);
        result = NewElem<reffy>(
            mstate.scratch, *mstate.ref.asTypedValue(), mstate.base
        );
      } else {
        raise_error("Cannot use [] for reading");
        result = nullptr;
      }
      break;
    case InvalidMemberCode:
      assert(false);
      result = nullptr; // Silence compiler warning.
    }

    /*
    // FIXME: this is used for __get()/__set() with global variable
    single_mode_on = false;
    single_mode_cur_iter = -1;
    */

    assert(result != nullptr);
    ratchetRefs(result, *mstate.ref.asTypedValue(),
                *mstate.ref2.asTypedValue());
    // Check whether an error occurred (i.e. no result was set).
    if (setMember && result == &mstate.scratch &&
        result->m_type == KindOfUninit) {
      return true;
    }

#ifdef CHENG_INS_DEBUG
    //auto txt = HHVM_FN(print_r)(tvAsVariant(result), true);
    debug_log << "    ---> Intermediate Result: " << result->pretty() << "\n";
    debug_log << "    ---> after derf : " << tvToCell(result)->pretty() << "\n";
    debug_log << "    ---> after 2 derf : " << tvToCell(tvToCell(result))->pretty() << "\n";
    //debug_log << "         {{" << txt.toString().toCppString() << "}}\n";
#endif

    // cheng-hack:
    if (UNLIKELY(tvToCell(result)->m_type == KindOfMulti)) {
      // Used to be a BUG: if we deref here, for the VGetM, there will be multiple-ref!
      // correct version:
      auto orig_result = result; // for VGetM
      result = tvToCell(result);

      if (UNLIKELY(single_mode_on)) {
        result = result->m_data.pmulti->getByVal(single_mode_cur_iter);
      } else if (!isMultiBase && !isMultiIndex && !isMultiInternal) {
        // we find a multi-index on single-base  or multi-value on single-base
        // first try to find out if we're going to continue the loop 
        if (vec < pc) {
          // if so, jump to multi_begin
          isMultiInternal = true;
          mstate.base = result;
          goto multi_begin;
        } else {
#ifdef CHENG_INS_ONLY_DEBUG
          debug_log << "    ---> get multi-value as result and quit\n"; 
#endif
          if (mstate.isVGetM) {
            mstate.base = orig_result;
          } else {
            mstate.base = result;
          }
          break;
        }
      }
      // not in single_Mode and (isMultiBase || isMultiIndex || isMultiInternal)
      else
      {
        // find one multival, clear previous iter_last_obj_ref
        cheng_assert(iter_last_obj_ref.size() == iter_counter);
        iter_last_obj_ref[iter_counter-1] = nullptr;
        // Can be: multi_arr->obj->multi_arr
        // should not do deref! for cases like VGetM!
        result = result->m_data.pmulti->getByVal(iter_counter-1);
#ifdef CHENG_INS_ONLY_DEBUG
        debug_log << "    ---> Multi-Result, get the result[" << iter_counter - 1 << "]: " << result->pretty() << "\n";
#endif
      }
    } 
    // for NOTE2: only happen when we're in iteration mode
    else if (UNLIKELY(multi_size > 0)) {
      // set iter_last_obj_ref
      // FIXME: is it possible that ref->obj->[SAME ObjectData]?
      if (result->m_type == KindOfRef || result->m_type == KindOfObject) {
        cheng_assert(iter_last_obj_ref.size() == iter_counter); 
        iter_last_obj_ref[iter_counter-1] = (void*)result->m_data.pobj; // save last met obj/ref
      }
    }

    mstate.base = result;
  }

  if (mleave == VectorLeaveCode::ConsumeAll) {
    assert(vec == pc);
    if (debug) {
      if (lcode == LSC || lcode == LSL) {
        assert(depth == int(mdepth));
      } else {
        assert(depth == int(mdepth) - 1);
      }
    }
  }

  if (saveResult) {
    assert(!setMember);
    // If requested, save a copy of the result.  If base already points to
    // mstate.scratch, no reference counting is necessary, because (with the
    // exception of the following block), mstate.scratch is never populated
    // such that it owns a reference that must be accounted for.
    if (mstate.base != &mstate.scratch) {
      // Acquire a reference to the result via tvDup(); base points to the
      // result but does not own a reference.
      tvDup(*mstate.base, mstate.scratch);
    }
  }

  // cheng-hack:
  if (UNLIKELY(isMultiBase||isMultiIndex||isMultiInternal)) goto multi_begin;

  return false;
}

// The following arguments are outputs:
// pc:         bytecode instruction after the vector instruction
// mstate
//  ndiscard:  number of stack elements to discard
//  base:      ultimate result of the vector-get
//  scratch:   temporary result storage
//  ref:       temporary result storage
//  ref2:      temporary result storage
//  mcode:     output MemberCode for the last member if LeaveLast
//  curMember: output last member value one if LeaveLast; but undefined
//             if the last mcode == MW
//
// If saveResult is true, then upon completion of getHelperPre(),
// mstate.scratch contains a reference to the result (a duplicate of what
// base refers to).  getHelperPost<true>(...)  then saves the result
// to its final location.
template<bool warn,bool saveResult,VectorLeaveCode mleave>
OPTBLD_INLINE void getHelperPre(PC& pc, MemberState& mstate) {
  memberHelperPre<false,warn,false,false,false,0,mleave,saveResult>(
    pc, mstate
  );
}

OPTBLD_INLINE
TypedValue* getHelperPost(unsigned ndiscard) {
  // Clean up all ndiscard elements on the stack.  Actually discard
  // only ndiscard - 1, and overwrite the last cell with the result,
  // or if ndiscard is zero we actually need to allocate a cell.
  for (unsigned depth = 0; depth < ndiscard; ++depth) {
    TypedValue* tv = vmStack().indTV(depth);
    tvRefcountedDecRef(tv);
  }

  TypedValue* tvRet;
  if (!ndiscard) {
    tvRet = vmStack().allocTV();
  } else {
    vmStack().ndiscard(ndiscard - 1);
    tvRet = vmStack().topTV();
  }
  return tvRet;
}

OPTBLD_INLINE
TypedValue* getHelper(PC& pc, MemberState& mstate) {
  getHelperPre<true, true, VectorLeaveCode::ConsumeAll>(pc, mstate);
  auto tvRet = getHelperPost(mstate.ndiscard);
  // If tvRef wasn't just allocated, we've already decref'd it in
  // the loop above. (XXX tvRef? or mstate.ref/scratch/tvRet)
  tvCopy(mstate.scratch, *tvRet);
  return tvRet;
}

// The following arguments are outputs:
// pc:          bytecode instruction after the vector instruction
// mstate
//  ndiscard:   number of stack elements to discard
//  base:       ultimate result of the vector-get
//  scratch:    temporary result storage
//  ref:        temporary result storage
//  ref2:       temporary result storage
//  mcode:      output MemberCode for the last member if LeaveLast
//  curMember:  output last member value one if LeaveLast; but undefined
//              if the last mcode == MW
template <bool warn, bool define, bool unset, bool reffy,
          unsigned mdepth, // extra args on stack for set (e.g. rhs)
          VectorLeaveCode mleave>
OPTBLD_INLINE bool setHelperPre(PC& pc, MemberState& mstate) {
  return memberHelperPre<true,warn,define,unset,reffy,mdepth,mleave,false>(
    pc, mstate
  );
}

template <unsigned mdepth>
OPTBLD_INLINE void setHelperPost(unsigned ndiscard) {
  // Clean up the stack.  Decref all the elements for the vector, but
  // leave the first mdepth (they are not part of the vector data).
  for (unsigned depth = mdepth; depth-mdepth < ndiscard; ++depth) {
    TypedValue* tv = vmStack().indTV(depth);
    tvRefcountedDecRef(tv);
  }

  // NOTE: currently the only instructions using this that have return
  // values on the stack also have more inputs than the -vector, so
  // mdepth > 0.  They also always return the original top value of
  // the stack.
  if (mdepth > 0) {
    assert(mdepth == 1 &&
           "We don't really support mdepth > 1 in setHelperPost");

    if (ndiscard > 0) {
      TypedValue* retSrc = vmStack().topTV();
      TypedValue* dest = vmStack().indTV(ndiscard + mdepth - 1);
      assert(dest != retSrc);
      memcpy(dest, retSrc, sizeof *dest);
    }
  }

  vmStack().ndiscard(ndiscard);
}

/* cheng-hack:
 * Used by VGetL/VGetN/VGetG/FPassL
 * Here and VGetG is the only places where can generate Ref (aka. tvBox(...))
 * Used by more places
 *
 * modify the reference in-place.
 */
static inline TypedValue* tvBoxMulti(TypedValue* boxee) {
#ifdef CHENG_CHECK
  cheng_assert(boxee->m_type == KindOfMulti);
  cheng_assert(boxee->m_data.pmulti->getType() != KindOfRef);
#endif
#ifdef CHENG_INS_DEBUG
  debug_log << "  Before VGetX:\n" << boxee->m_data.pmulti->dump("    ");
#endif
  // box each of the element in multiVal
  for (auto it : *boxee->m_data.pmulti) {
    tvBox(it);
  }
  // set the type to multiRef
  boxee->m_data.pmulti->setType(KindOfRef);
#ifdef CHENG_INS_DEBUG
  debug_log << "  After VGetX:\n" << boxee->m_data.pmulti->dump("    ");
#endif
  return boxee;
}

// forward-declare iop functions.
#define O(name, imm, push, pop, flags) void iop##name(PC& pc);
OPCODES
#undef O

OPTBLD_INLINE void iopLowInvalid(IOP_ARGS) {
  fprintf(stderr, "invalid bytecode executed\n");
  abort();
}

OPTBLD_INLINE void iopHighInvalid(IOP_ARGS) {
  fprintf(stderr, "invalid bytecode executed\n");
  abort();
}

// Good to go
OPTBLD_INLINE void iopNop(IOP_ARGS) {
  pc++;
}

// Good to go
OPTBLD_INLINE void iopPopA(IOP_ARGS) {
  pc++;
  vmStack().popA();
}

// Good to go
OPTBLD_INLINE void iopPopC(IOP_ARGS) {
  pc++;
  vmStack().popC();
}

// Good to go
OPTBLD_INLINE void iopPopV(IOP_ARGS) {
  pc++;
  vmStack().popV();
}

// Good to go
OPTBLD_INLINE void iopPopR(IOP_ARGS) {
  pc++;
  if (vmStack().topTV()->m_type != KindOfRef) {
    vmStack().popC();
  } else {
    vmStack().popV();
  }
}

// Good to go
OPTBLD_INLINE void iopDup(IOP_ARGS) {
  pc++;
  vmStack().dup();
}

// Not impl 
OPTBLD_INLINE void iopBox(IOP_ARGS) {
  pc++;
#ifdef CHENG_CHECK
  cheng_assert(vmStack().topTV()->m_type != KindOfMulti);
#endif
  vmStack().box();
}

// Not impl 
OPTBLD_INLINE void iopUnbox(IOP_ARGS) {
  pc++;
#ifdef CHENG_CHECK
  cheng_assert(vmStack().topTV()->m_type != KindOfMulti);
#endif
  vmStack().unbox();
}

// Not impl
OPTBLD_INLINE void iopBoxR(IOP_ARGS) {
  pc++;
  TypedValue* tv = vmStack().topTV();
#ifdef CHENG_CHECK
  cheng_assert(tv->m_type != KindOfMulti);
#endif
  if (tv->m_type != KindOfRef) {
    tvBox(tv);
  }
}

// Not impl
OPTBLD_INLINE void iopBoxRNop(IOP_ARGS) {
  pc++;
#ifdef CHENG_CHECK
  cheng_assert(vmStack().topTV()->m_type != KindOfMulti);
#endif
  assert(refIsPlausible(*vmStack().topTV()));
}

// cheng: deref multi-ref
ALWAYS_INLINE static
void unboxMulti(TypedValue* tv) {
#ifdef CHENG_CHECK
  cheng_assert(tv->m_type == KindOfMulti);
#endif
  if (tv->m_data.pmulti->getType() == KindOfRef) {
#ifdef CHENG_INS_DEBUG
    debug_log << "    deref the multi-ref\n";
#endif
    // unbox a multi-ref
    TypedValue ret = MultiVal::makeMultiVal();
    for (auto it : *tv->m_data.pmulti) {
      // addValue() will add the refcount for TV 
      ret.m_data.pmulti->addValue(*tvToCell(it));
    }
    // decrease multi-ref's counter
    tvDecRefMulti(tv);
    // copy the newly multi to the right place
    tvCopy(ret, *tv);
  }
}

// cheng-hack:
OPTBLD_INLINE void iopUnboxR(IOP_ARGS) {
  AS_MISC;
  pc++;
  auto type = vmStack().topTV()->m_type;
  // This is a multi-ref
  if (UNLIKELY(type == KindOfMulti)) {
    START;
    AS_MMISC;
    TypedValue* tv = vmStack().topTV();
#ifdef CHENG_INS_DEBUG
    auto txt = HHVM_FN(print_r)(tvAsVariant(tv), true);
    debug_log << "  UnboxR a multiVal, before unbox: " << tv->pretty() << " : {{"
      << txt.toString().toCppString() << "}}\n";
#endif
    unboxMulti(tv);
    END;
  } else if (type == KindOfRef) {
    // original case
    vmStack().unbox();
  }
#ifdef CHENG_INS_DEBUG
  debug_log << "    unboxr: " << vmStack().topTV()->pretty() << "\n";
#endif
}

// Good to go
OPTBLD_INLINE void iopUnboxRNop(IOP_ARGS) {
  pc++;
  assert(cellIsPlausible(*vmStack().topTV()));
}

// Good to go
OPTBLD_INLINE void iopRGetCNop(IOP_ARGS) {
  pc++;
}

// Good to go
OPTBLD_INLINE void iopNull(IOP_ARGS) {
  pc++;
  vmStack().pushNull();
}

// Good to go
OPTBLD_INLINE void iopNullUninit(IOP_ARGS) {
  pc++;
  vmStack().pushNullUninit();
}

// Good to go
OPTBLD_INLINE void iopTrue(IOP_ARGS) {
  pc++;
  vmStack().pushTrue();
}

// Good to go
OPTBLD_INLINE void iopFalse(IOP_ARGS) {
  pc++;
  vmStack().pushFalse();
}

// Good to go
OPTBLD_INLINE void iopFile(IOP_ARGS) {
  pc++;
  const StringData* s = vmfp()->m_func->unit()->filepath();
  vmStack().pushStaticString(const_cast<StringData*>(s));
}

// Good to go
OPTBLD_INLINE void iopDir(IOP_ARGS) {
  pc++;
  const StringData* s = vmfp()->m_func->unit()->dirpath();
  vmStack().pushStaticString(const_cast<StringData*>(s));
}

// Good to go
OPTBLD_INLINE void iopNameA(IOP_ARGS) {
  pc++;
  auto const cls  = vmStack().topA();
  auto const name = cls->name();
  vmStack().popA();
  vmStack().pushStaticString(const_cast<StringData*>(name));
}

// Good to go
OPTBLD_INLINE void iopInt(IOP_ARGS) {
  pc++;
  auto i = decode<int64_t>(pc);
  vmStack().pushInt(i);
}

// Good to go
OPTBLD_INLINE void iopDouble(IOP_ARGS) {
  pc++;
  auto d = decode<double>(pc);
  vmStack().pushDouble(d);
}

// Good to go
OPTBLD_INLINE void iopString(IOP_ARGS) {
  pc++;
  auto s = decode_litstr(pc);
  vmStack().pushStaticString(s);
}

// Good to go
OPTBLD_INLINE void iopArray(IOP_ARGS) {
  AS_ARR;
  pc++;
  auto id = decode<Id>(pc);
  ArrayData* a = vmfp()->m_func->unit()->lookupArrayId(id);
  vmStack().pushStaticArray(a);
}

// Good to go
OPTBLD_INLINE void iopNewArray(IOP_ARGS) {
  AS_ARR;
  pc++;
  auto capacity = decode_iva(pc);
  if (capacity == 0) {
    vmStack().pushArrayNoRc(staticEmptyArray());
  } else {
    vmStack().pushArrayNoRc(MixedArray::MakeReserve(capacity));
  }
}

// Good to go
OPTBLD_INLINE void iopNewMixedArray(IOP_ARGS) {
  AS_ARR;
  pc++;
  auto capacity = decode_iva(pc);
  if (capacity == 0) {
    vmStack().pushArrayNoRc(staticEmptyArray());
  } else {
    vmStack().pushArrayNoRc(MixedArray::MakeReserveMixed(capacity));
  }
}

// Good to go
OPTBLD_INLINE void iopNewVArray(IOP_ARGS) {
  AS_ARR;
  pc++;
  auto capacity = decode_iva(pc);
  // TODO(t4757263) staticEmptyArray() for VArray
  vmStack().pushArrayNoRc(MixedArray::MakeReserveVArray(capacity));
}

// Good to go
OPTBLD_INLINE void iopNewMIArray(IOP_ARGS) {
  AS_ARR;
  pc++;
  auto capacity = decode_iva(pc);
  // TODO(t4757263) staticEmptyArray() for IntMap
  vmStack().pushArrayNoRc(MixedArray::MakeReserveIntMap(capacity));
}

// Good to go
OPTBLD_INLINE void iopNewMSArray(IOP_ARGS) {
  AS_ARR;
  pc++;
  auto capacity = decode_iva(pc);
  // TODO(t4757263) staticEmptyArray() for StrMap
  vmStack().pushArrayNoRc(MixedArray::MakeReserveStrMap(capacity));
}

// Not Impl
OPTBLD_INLINE void iopNewLikeArrayL(IOP_ARGS) {
  AS_ARR;
  pc++;
  auto local = decode_la(pc);
  auto capacity = decode_iva(pc);

  ArrayData* arr;
  TypedValue* fr = frame_local(vmfp(), local);

#ifdef CHENG_CHECK
  cheng_assert(fr->m_type != KindOfMulti);
#endif

  if (LIKELY(fr->m_type == KindOfArray)) {
    arr = MixedArray::MakeReserveLike(fr->m_data.parr, capacity);
  } else {
    capacity = (capacity ? capacity : MixedArray::SmallSize);
    arr = MixedArray::MakeReserve(capacity);
  }
  vmStack().pushArrayNoRc(arr);
}

// curtis:
OPTBLD_INLINE void iopNewPackedArray(IOP_ARGS) {
  AS_ARR;
  pc++;
  auto n = decode_iva(pc);
 
  TypedValue *values = vmStack().topC();
  bool multi_call = false;
  bool is_multi[n];
  memset(is_multi, 0, n*sizeof(bool));
  int multival_num = 0, call_num = 0;

  for (int i = 0; i < n; i++) {
    auto const& src = values[i];
    if (src.m_type == KindOfMulti) {
      multi_call = true;
      is_multi[i] = true;
      multival_num++;
      if (call_num == 0) call_num = src.m_data.pmulti->valSize();
    }
  } 

  if (UNLIKELY(multi_call)) {
    START;
    AS_MARR;
    TypedValue result = MultiVal::makeMultiVal();
    auto multi = result.m_data.pmulti;

    TypedValue orig_stack[n];
    memcpy(orig_stack, values, sizeof(struct TypedValue)*n);
    struct ActRec orig_ar;
    memcpy(&orig_ar, vmfp(), sizeof(struct ActRec));
    struct Stack orig_stack_ptr;
    orig_stack_ptr = vmStack();
 
    for (int call_counter = 0; call_counter < call_num; call_counter++) {
      vmStack() = orig_stack_ptr;
      memcpy(values, orig_stack, sizeof(struct TypedValue)*n);
      memcpy(vmfp(), &orig_ar, sizeof(struct ActRec));
      for (int i = 0; i < n; i++) {
        if (is_multi[i]) {
#ifdef CHENG_CHECK
          cheng_assert(values[i].m_type == KindOfMulti);
#endif
          TypedValue *tmp = values[i].m_data.pmulti->getByVal(call_counter);
          tvCopy(*tmp, values[i]);
        }
      }

      TypedValue ret_arr;
      ret_arr.m_type = KindOfArray;
      ret_arr.m_data.parr = MixedArray::MakePacked(n, values);
      // increase counter for all the elements
      for (int s_idx = 0; s_idx < n; s_idx++) {
        tvRefcountedIncRef(&values[s_idx]);
      }

      multi->addValueNoInc(ret_arr);
    }

    // change back to original stack, and decrease the refcount
    memcpy(values, orig_stack, sizeof(struct TypedValue)*n);
    for (int s_idx = 0; s_idx < n; s_idx++) {
      tvRefcountedDecRef(&values[s_idx]);
    }

    vmStack().ndiscard(n);
    vmStack().pushNull();
    tvCopy(result, *(vmStack().topTV()));

    END;
  } else {
    // This constructor moves values, no inc/decref is necessary.
    auto* a = MixedArray::MakePacked(n, values);
    vmStack().ndiscard(n);
    vmStack().pushArrayNoRc(a);
  }
}

// support 
OPTBLD_INLINE void iopNewStructArray(IOP_ARGS) {
  AS_ARR;
  pc++;
  auto n = decode<uint32_t>(pc); // number of keys and elements

  // cheng-hack:
  bool multi_call = false;
  std::vector<TypedValue*> stack_slot;
  std::vector<MultiVal*> multi_elem;

  for (int i = 0; i < n; i++) {
    if (UNLIKELY(vmStack().indTV(i)->m_type == KindOfMulti)) {
      multi_call = true;
      stack_slot.push_back(vmStack().indTV(i));
      multi_elem.push_back(vmStack().indTV(i)->m_data.pmulti);
    }
  }

  // if we have multi-val
  if (UNLIKELY(multi_call)) {
    START;
    AS_MARR;
    auto orig_pc = pc;
    auto values = vmStack().topC();
    ArrayData* a;

    int multi_num = multi_elem[0]->valSize();
    TypedValue multi_ret = MultiVal::makeMultiVal();
    TypedValue orig_stack[n];
    memcpy(orig_stack, values, sizeof(struct TypedValue)*n);

#ifdef CHENG_CHECK
    for (auto it : multi_elem) {
      cheng_assert(it->valSize() == multi_num);
    }
    cheng_assert(multi_num > 1);
#endif

    for (int i = 0; i < multi_num; i++) {
      pc = orig_pc;
      // replace the stack elements
      for (int j = 0; j < stack_slot.size(); j++) {
        TypedValue* single = multi_elem[j]->getByVal(i);
        tvCopy(*single, *stack_slot[j]);
      }

      assert(n > 0 && n <= StructArray::MaxMakeSize);
      StringData* names[n];
      for (size_t i = 0; i < n; i++) {
        names[i] = decode_litstr(pc);
      }
      // USED TO BE: This constructor moves values, no inc/decref is necessary.
      Shape* shape;
      if (!RuntimeOption::EvalDisableStructArray &&
          (shape = Shape::create(names, n))) {
        a = MixedArray::MakeStructArray(n, vmStack().topC(), shape);
      } else {
        a = MixedArray::MakeStruct(n, names, vmStack().topC())->asArrayData();
      }
      // cheng-hack: inc the refcount
      for (int s_idx = 0; s_idx < n; s_idx++) {
        tvRefcountedIncRef(&values[s_idx]);
      }

      // cheng-hack:
      TypedValue tmp;
      tmp.m_type = KindOfArray;
      tmp.m_data.parr = a;
      multi_ret.m_data.pmulti->addValueNoInc(tmp);
    }

    // cheng-hack: replace the stack and dec the refcount
    memcpy(values, orig_stack, sizeof(struct TypedValue)*n);
    for (int s_idx = 0; s_idx < n; s_idx++) {
      tvRefcountedDecRef(&values[s_idx]);
    }
    vmStack().ndiscard(n);
    vmStack().pushMultiObject(multi_ret);
    END;
  } else {
    // original case
    assert(n > 0 && n <= StructArray::MaxMakeSize);
    StringData* names[n];
    for (size_t i = 0; i < n; i++) {
      names[i] = decode_litstr(pc);
    }
    // USED TO BE: This constructor moves values, no inc/decref is necessary.
    ArrayData* a;
    Shape* shape;
    if (!RuntimeOption::EvalDisableStructArray &&
        (shape = Shape::create(names, n))) {
      a = MixedArray::MakeStructArray(n, vmStack().topC(), shape);
    } else {
      a = MixedArray::MakeStruct(n, names, vmStack().topC())->asArrayData();
    }
    vmStack().ndiscard(n);
    vmStack().pushArrayNoRc(a);
  }
}

// curtis:
OPTBLD_INLINE void iopAddElemC(IOP_ARGS) {
  AS_ARR;
  pc++;
  Cell* c1 = vmStack().topC();
  Cell* c2 = vmStack().indC(1);
  Cell* c3 = vmStack().indC(2);

  if (UNLIKELY(c1->m_type == KindOfMulti) ||
      UNLIKELY(c2->m_type == KindOfMulti) ||
      UNLIKELY(c3->m_type == KindOfMulti)) {
    START;
    AS_MARR;
    bool isFirstMulti = (c1->m_type == KindOfMulti);
    bool isSecondMulti = (c2->m_type == KindOfMulti);
    bool isThirdMulti = (c3->m_type == KindOfMulti);

    if (isThirdMulti) {
      // (M, *, *)
      // No need to split the array
      if (c3->m_data.pmulti->getType() != KindOfArray) {
        raise_error("AddElemC: $3 must be an array");
      }

      if (isFirstMulti && isSecondMulti) {
        // (M, M, M)
        auto m1 = c1->m_data.pmulti;
        auto m2 = c2->m_data.pmulti;
        auto m3 = c3->m_data.pmulti;

#ifdef CHENG_CHECK
        cheng_assert((m1->valSize() == m2->valSize()) && (m1->valSize() == m3->valSize()));
#endif

        for (int i = 0; i < m1->valSize(); i++) {
          TypedValue *cell1 = m1->getByVal(i);
          TypedValue *cell2 = m2->getByVal(i);
          TypedValue *cell3 = m3->getByVal(i);
          if (cell2->m_type == KindOfInt64) {
            tvAsVariant(cell3).asArrRef().set(cell2->m_data.num, tvAsCVarRef(cell1));
          } else {
            tvAsVariant(cell3).asArrRef().set(tvAsCVarRef(cell2), tvAsCVarRef(cell1));
          }
        }

      } else if (isFirstMulti) {
        // (M, S, M)
        auto m1 = c1->m_data.pmulti;
        auto m3 = c3->m_data.pmulti;

#ifdef CHENG_CHECK
        cheng_assert(m1->valSize() ==  m3->valSize());
#endif

        for (int i = 0; i < m1->valSize(); i++) {
          TypedValue *cell1 = m1->getByVal(i);
          TypedValue *cell3 = m3->getByVal(i);
          if (c2->m_type == KindOfInt64) {
            tvAsVariant(cell3).asArrRef().set(c2->m_data.num, tvAsCVarRef(cell1));
          } else {
            tvAsVariant(cell3).asArrRef().set(tvAsCVarRef(c2), tvAsCVarRef(cell1));
          }
        }
      } else if (isSecondMulti) {
        // (M, M, S)
        auto m2 = c2->m_data.pmulti;
        auto m3 = c3->m_data.pmulti;

#ifdef CHENG_CHECK
        cheng_assert(m2->valSize() ==  m3->valSize());
#endif

        for (int i = 0; i < m2->valSize(); i++) {
          TypedValue *cell2 = m2->getByVal(i);
          TypedValue *cell3 = m3->getByVal(i);
          if (cell2->m_type == KindOfInt64) {
            tvAsVariant(cell3).asArrRef().set(cell2->m_data.num, tvAsCVarRef(c1));
          } else {
            tvAsVariant(cell3).asArrRef().set(tvAsCVarRef(cell2), tvAsCVarRef(c1));
          }
        }
      } else {
        // (M, S, S)
        auto m3 = c3->m_data.pmulti;
        for (int i = 0; i < m3->valSize(); i++) {
          TypedValue *cell3 = m3->getByVal(i);
          if (c2->m_type == KindOfInt64) {
            tvAsVariant(cell3).asArrRef().set(c2->m_data.num, tvAsCVarRef(c1));
          } else {
            tvAsVariant(cell3).asArrRef().set(tvAsCVarRef(c2), tvAsCVarRef(c1));
          }
        }
      }
    } else {
      // (S, *, *)
      // Need to split array
      if (c3->m_type != KindOfArray) {
        raise_error("AddElemC: $3 must be an array");
      }
      if (isFirstMulti && isSecondMulti) {
        // (S, M, M)
        auto m1 = c1->m_data.pmulti;
        auto m2 = c2->m_data.pmulti;

#ifdef CHENG_CHECK
        cheng_assert(m1->valSize() == m2->valSize());
#endif

        TypedValue ret = MultiVal::splitArray(*c3, m1->valSize());
        auto ret_multi = ret.m_data.pmulti; 

        for (int i = 0; i < m1->valSize(); i++) {
          TypedValue *cell1 = m1->getByVal(i);
          TypedValue *cell2 = m2->getByVal(i);
          TypedValue *cell3 = ret_multi->getByVal(i);
          if (cell2->m_type == KindOfInt64) {
            tvAsVariant(cell3).asArrRef().set(cell2->m_data.num, tvAsCVarRef(cell1));
          } else {
            tvAsVariant(cell3).asArrRef().set(tvAsCVarRef(cell2), tvAsCVarRef(cell1));
          }
        }
        tvCopy(ret, *c3);
      } else if (isFirstMulti) {
        // (S, S, M)
        auto multi = c1->m_data.pmulti;

        TypedValue ret = MultiVal::splitArray(*c3, multi->valSize());
        auto ret_multi = ret.m_data.pmulti; 

        for (int i = 0; i < multi->valSize(); i++) {
          TypedValue *cell1 = multi->getByVal(i);
          TypedValue *cell3 = ret_multi->getByVal(i);
          if (c2->m_type == KindOfInt64) {
            tvAsVariant(cell3).asArrRef().set(c2->m_data.num, tvAsCVarRef(cell1));
          } else {
            tvAsVariant(cell3).asArrRef().set(tvAsCVarRef(c2), tvAsCVarRef(cell1));
          }
        }
        tvCopy(ret, *c3);
      } else {
        // (S, M, S)
        auto multi = c2->m_data.pmulti;

        TypedValue ret = MultiVal::splitArray(*c3, multi->valSize());
        auto ret_multi = ret.m_data.pmulti; 

        for (int i = 0; i < multi->valSize(); i++) {
          TypedValue *cell2 = multi->getByVal(i);
          TypedValue *cell3 = ret_multi->getByVal(i);
          if (cell2->m_type == KindOfInt64) {
            tvAsVariant(cell3).asArrRef().set(cell2->m_data.num, tvAsCVarRef(c1));
          } else {
            tvAsVariant(cell3).asArrRef().set(tvAsCVarRef(cell2), tvAsCVarRef(c1));
          }
        }
        tvCopy(ret, *c3);
      }
    }
    END;
  } else {
    // No multi-values
    if (c3->m_type != KindOfArray) {
      raise_error("AddElemC: $3 must be an array");
    }

    if (c2->m_type == KindOfInt64) {
      cellAsVariant(*c3).asArrRef().set(c2->m_data.num, tvAsCVarRef(c1));
    } else {
      cellAsVariant(*c3).asArrRef().set(tvAsCVarRef(c2), tvAsCVarRef(c1));
    }
  }
  vmStack().popC();
  vmStack().popC();
}

// Not Impl
OPTBLD_INLINE void iopAddElemV(IOP_ARGS) {
  AS_ARR;
  pc++;
  Ref* r1 = vmStack().topV();
  Cell* c2 = vmStack().indC(1);
  Cell* c3 = vmStack().indC(2);
#ifdef CHENG_CHECK
  cheng_assert(r1->m_type != KindOfMulti);
  cheng_assert(c2->m_type != KindOfMulti);
  cheng_assert(c3->m_type != KindOfMulti);
#endif
  if (c3->m_type != KindOfArray) {
    raise_error("AddElemV: $3 must be an array");
  }
  if (c2->m_type == KindOfInt64) {
    cellAsVariant(*c3).asArrRef().setRef(c2->m_data.num, tvAsVariant(r1));
  } else {
    cellAsVariant(*c3).asArrRef().setRef(tvAsCVarRef(c2), tvAsVariant(r1));
  }
  vmStack().popV();
  vmStack().popC();
}

// curtis:
OPTBLD_INLINE void iopAddNewElemC(IOP_ARGS) {
  AS_ARR;
  pc++;
  Cell* c1 = vmStack().topC();
  Cell* c2 = vmStack().indC(1);
  if(UNLIKELY(c1->m_type == KindOfMulti || c2->m_type == KindOfMulti)) {
    START;
    AS_MARR;
    bool isFirstMulti = (c1->m_type == KindOfMulti); 
    bool isSecondMulti = (c2->m_type == KindOfMulti);

    if (isFirstMulti && isSecondMulti) {
      // (M, M)
      // No need to split the array
      auto m1 = c1->m_data.pmulti;
      auto m2 = c2->m_data.pmulti;

      if (m2->getType() != KindOfArray) {
        raise_error("AddNewElemC: $2 must be an array");
      }

#ifdef CHENG_CHECK
      cheng_assert(m1->valSize() == m2->valSize());
#endif

      for (int i = 0; i < m1->valSize(); i++) {
        TypedValue *v1 = m1->getByVal(i);
        TypedValue *v2 = m2->getByVal(i);
        tvAsVariant(v2).asArrRef().append(tvAsCVarRef(v1));
      }

      vmStack().popC();

    } else if (isFirstMulti) {
      // (M, S)
      // Split the array
      auto multi = c1->m_data.pmulti;

      if (c2->m_type != KindOfArray) {
        raise_error("AddNewElemC: $2 must be an array");
      }

      TypedValue ret = MultiVal::splitArray(*c2, multi->valSize());
      auto ret_multi = ret.m_data.pmulti;

      for (int i = 0; i < multi->valSize(); i++) {
        TypedValue *v1 = multi->getByVal(i);
        TypedValue *v2 = ret_multi->getByVal(i);
        tvAsVariant(v2).asArrRef().append(tvAsCVarRef(v1));
      }

      tvCopy(ret, *c2);
      vmStack().popC();

    } else {
      // (S, M)
      // No need to split the array
      auto multi = c2->m_data.pmulti;

      if (multi->getType() != KindOfArray) {
        raise_error("AddNewElemC: $2 must be an array");
      }

      for (int i = 0; i < multi->valSize(); i++) {
        TypedValue *v = multi->getByVal(i);
        tvAsVariant(v).asArrRef().append(tvAsCVarRef(c1));
      }

      vmStack().popC();
    }

    END;
  } else {
    // (S, S)
    if (c2->m_type != KindOfArray) {
      raise_error("AddNewElemC: $2 must be an array");
    }
    cellAsVariant(*c2).asArrRef().append(tvAsCVarRef(c1));
    vmStack().popC();
  }
}

// cheng-hack: supported 
OPTBLD_INLINE void iopAddNewElemV(IOP_ARGS) {
  AS_ARR;
  pc++;
  Ref* r1 = vmStack().topV();
  Cell* c2 = vmStack().indC(1);

  // cheng-hack: for case "array($multi, &$result)"
  if (UNLIKELY(r1->m_type == KindOfMulti || c2->m_type == KindOfMulti)) {
    START;
    AS_MARR;
    bool ref_multi = (r1->m_type == KindOfMulti); 
    bool arr_multi = (c2->m_type == KindOfMulti);
    // check KindOfArray
    if (arr_multi) {
      cheng_assert(c2->m_data.pmulti->getType() == KindOfArray);
    } else {
      cheng_assert(c2->m_type == KindOfArray);
    }
    // check KindOfRef
    if (ref_multi) {
      cheng_assert(r1->m_data.pmulti->getType() == KindOfRef);
    } else {
      cheng_assert(r1->m_type == KindOfRef);
    }

    if (ref_multi && arr_multi) {
      cheng_assert(r1->m_data.pmulti->valSize() == c2->m_data.pmulti->valSize());
      int size = c2->m_data.pmulti->valSize();
      for (int i = 0; i < size; i++) {
        auto arr = c2->m_data.pmulti->getByVal(i);
        auto ref = r1->m_data.pmulti->getByVal(i);
        cellAsVariant(*arr).asArrRef().appendRef(tvAsVariant(ref));
      }
    } else if (arr_multi) {
      // split the ref
      int size = c2->m_data.pmulti->valSize();

      TypedValue *cell = r1->m_data.pref->tv();
      // if the ref is point to single element, split it!
      // And this will generate ref->multi 
      if (cell->m_type != KindOfMulti) {
        TypedValue tmp = splitElements(cell, size);
        // make the multi-val to ref
        tvBoxMulti(&tmp);
        tvCopy(tmp, *cell);
      }

      for (int i = 0; i < size; i++) {
        auto arr = c2->m_data.pmulti->getByVal(i);
        auto ref = cell->m_data.pmulti->getByVal(i);
        cellAsVariant(*arr).asArrRef().appendRef(tvAsVariant(ref));
      }
    } else { // ref_multi
      int size = r1->m_data.pmulti->valSize();
      TypedValue ret = MultiVal::splitArray(*c2, size);
      auto ret_multi = ret.m_data.pmulti;

      for (int i = 0; i < size; i++) {
        auto ref = r1->m_data.pmulti->getByVal(i);
        auto arr = ret_multi->getByVal(i);
        cellAsVariant(*arr).asArrRef().appendRef(tvAsVariant(ref));
      }
      tvCopy(ret, *c2);
    }
    vmStack().popV();
    END;
  } else {
  if (c2->m_type != KindOfArray) {
    raise_error("AddNewElemV: $2 must be an array");
  }
  cellAsVariant(*c2).asArrRef().appendRef(tvAsVariant(r1));
  vmStack().popV();
  }
}

// Good to go
OPTBLD_INLINE void iopNewCol(IOP_ARGS) {
  AS_ARR;
  pc++;
  auto cType = decode_iva(pc);
  auto nElms = decode_iva(pc);
  ObjectData* obj = newCollectionHelper(cType, nElms);
  vmStack().pushObject(obj);
}

// Not Impl
OPTBLD_INLINE void iopColAddNewElemC(IOP_ARGS) {
  AS_ARR;
  pc++;
  Cell* c1 = vmStack().topC();
  Cell* c2 = vmStack().indC(1);
#ifdef CHENG_CHECK
  cheng_assert(c1->m_type != KindOfMulti);
  cheng_assert(c2->m_type != KindOfMulti);
#endif
  if (c2->m_type == KindOfObject && c2->m_data.pobj->isCollection()) {
    collectionInitAppend(c2->m_data.pobj, c1);
  } else {
    raise_error("ColAddNewElemC: $2 must be a collection");
  }
  vmStack().popC();
}

// Not Impl
OPTBLD_INLINE void iopColAddElemC(IOP_ARGS) {
  AS_ARR;
  pc++;
  Cell* c1 = vmStack().topC();
  Cell* c2 = vmStack().indC(1);
  Cell* c3 = vmStack().indC(2);
#ifdef CHENG_CHECK
  cheng_assert(c1->m_type != KindOfMulti);
  cheng_assert(c2->m_type != KindOfMulti);
  cheng_assert(c3->m_type != KindOfMulti);
#endif
  if (c3->m_type == KindOfObject && c3->m_data.pobj->isCollection()) {
    collectionInitSet(c3->m_data.pobj, c2, c1);
  } else {
    raise_error("ColAddElemC: $3 must be a collection");
  }
  vmStack().popC();
  vmStack().popC();
}

// Good to go
OPTBLD_INLINE void iopCns(IOP_ARGS) {
  pc++;
  auto s = decode_litstr(pc);
  auto const cns = Unit::loadCns(s);
  if (cns == nullptr) {
    raise_notice(Strings::UNDEFINED_CONSTANT, s->data(), s->data());
    vmStack().pushStaticString(s);
    return;
  }
  auto const c1 = vmStack().allocC();
  cellDup(*cns, *c1);
}

// Good to go
OPTBLD_INLINE void iopCnsE(IOP_ARGS) {
  pc++;
  auto s = decode_litstr(pc);
  auto const cns = Unit::loadCns(s);
  if (cns == nullptr) {
    raise_error("Undefined constant '%s'", s->data());
  }
  auto const c1 = vmStack().allocC();
  cellDup(*cns, *c1);
}

// Good to go
OPTBLD_INLINE void iopCnsU(IOP_ARGS) {
  pc++;
  auto name = decode_litstr(pc);
  auto fallback = decode_litstr(pc);
  auto cns = Unit::loadCns(name);
  if (cns == nullptr) {
    cns = Unit::loadCns(fallback);
    if (cns == nullptr) {
      raise_notice(
        Strings::UNDEFINED_CONSTANT,
        fallback->data(),
        fallback->data()
      );
      vmStack().pushStaticString(fallback);
      return;
    }
  }
  auto const c1 = vmStack().allocC();
  cellDup(*cns, *c1);
}

// Good to go
// The value on stack can be MultiVal
OPTBLD_INLINE void iopDefCns(IOP_ARGS) {
  pc++;
  auto s = decode_litstr(pc);
  bool result = Unit::defCns(s, vmStack().topTV());
  vmStack().replaceTV<KindOfBoolean>(result);
}

// Good to go
OPTBLD_INLINE void iopClsCns(IOP_ARGS) {
  pc++;
  auto clsCnsName = decode_litstr(pc);

#ifdef CHENG_CHECK
  cheng_assert(vmStack().topTV()->m_type != KindOfMulti);
#endif

  auto const cls    = vmStack().topA();
  auto const clsCns = cls->clsCnsGet(clsCnsName);

  if (clsCns.m_type == KindOfUninit) {
    raise_error("Couldn't find constant %s::%s",
                cls->name()->data(), clsCnsName->data());
  }

  cellDup(clsCns, *vmStack().topTV());
}

// Good to go
OPTBLD_INLINE void iopClsCnsD(IOP_ARGS) {
  pc++;
  auto clsCnsName = decode_litstr(pc);
  auto classId = decode<Id>(pc);
  const NamedEntityPair& classNamedEntity =
    vmfp()->m_func->unit()->lookupNamedEntityPairId(classId);

  auto const clsCns = g_context->lookupClsCns(classNamedEntity.second,
                                       classNamedEntity.first, clsCnsName);
  auto const c1 = vmStack().allocC();
  cellDup(clsCns, *c1);
}

// Supported 
OPTBLD_INLINE void iopConcat(IOP_ARGS) {
  AS_ARITH;
  pc++;
  Cell* c1 = vmStack().topC();
  Cell* c2 = vmStack().indC(1);

  if (UNLIKELY(c1->m_type == KindOfMulti ||
               c2->m_type == KindOfMulti)) {
    START;
    AS_MARITH;
    bool isFirstMulti = (c1->m_type == KindOfMulti);  
    bool isSecondMulti = (c2->m_type == KindOfMulti);  
    int multi_size = isFirstMulti ? c1->m_data.pmulti->valSize() : c2->m_data.pmulti->valSize();

#ifdef CHENG_CHECK
    if (isFirstMulti && isSecondMulti) {
      cheng_assert(c1->m_data.pmulti->valSize() == c2->m_data.pmulti->valSize());
    }
#endif

    if (isFirstMulti && isSecondMulti) {
      // c1 and c2 are both multi-val
      //TypedValue ret = MultiVal::cloneMultiVal(*c2);
      TypedValue ret = in_makeMultiVal(multi_size, KindOfString);
      auto ret_multi = ret.m_data.pmulti;
      auto multi_1 = c1->m_data.pmulti;
      auto multi_2 = c2->m_data.pmulti;
      for(int i = 0; i < multi_size; i++) {
        TypedValue *m1 = multi_1->getByVal(i);
        TypedValue *m2 = multi_2->getByVal(i);
        TypedValue *loc = ret_multi->getByVal(i);
        cellAsVariant(*loc) = concat(cellAsVariant(*m2).toString(), cellAsCVarRef(*m1).toString());
      }
      vmStack().popC();
      tvRefcountedDecRef(c2);
      tvCopy(ret, *c2);

    } else if (isFirstMulti) {
      // c1 is multi-val, c2 is non multi-val
      //TypedValue ret = MultiVal::cloneMultiVal(*c1);
      TypedValue ret = in_makeMultiVal(multi_size, KindOfString); 
      auto ret_multi = ret.m_data.pmulti;
      auto multi = c1->m_data.pmulti;
      for (int i = 0; i < multi_size; i++) {
        TypedValue *c = multi->getByVal(i);
        TypedValue *loc = ret_multi->getByVal(i);
        cellAsVariant(*loc) = concat(cellAsVariant(*c2).toString(), cellAsCVarRef(*c).toString());
      }
      vmStack().popC();
      tvRefcountedDecRef(c2);
      tvCopy(ret, *c2);

    } else {
      // c1 is not multi-val, c2 is multi-val
      //TypedValue ret = MultiVal::cloneMultiVal(*c2);
      TypedValue ret = in_makeMultiVal(multi_size, KindOfString); 
      auto ret_multi = ret.m_data.pmulti;
      auto multi = c2->m_data.pmulti;
      for (int i = 0; i < multi_size; i++) {
        TypedValue *c = multi->getByVal(i);
        TypedValue *loc = ret_multi->getByVal(i);
        cellAsVariant(*loc) = concat(cellAsVariant(*c).toString(), cellAsCVarRef(*c1).toString());
      }
      vmStack().popC();
      tvRefcountedDecRef(c2);
      tvCopy(ret, *c2);
    }

    END;
  } else {
    // c1 and c2 are both not multi-val
    cellAsVariant(*c2) = concat(cellAsVariant(*c2).toString(),
                                cellAsCVarRef(*c1).toString());
    assert(check_refcount_nz(c2->m_data.pstr->getCount()));
    vmStack().popC();
  }
}

// Not Impl
OPTBLD_INLINE void iopConcatN(IOP_ARGS) {
  AS_ARITH;
  pc++;
  auto n = decode_iva(pc);

  Cell* c1 = vmStack().topC();
  Cell* c2 = vmStack().indC(1);

#ifdef CHENG_CHECK
  cheng_assert(c1->m_type != KindOfMulti);
  cheng_assert(c2->m_type != KindOfMulti);
#endif

  if (n == 2) {
    cellAsVariant(*c2) = concat(cellAsVariant(*c2).toString(),
                                cellAsCVarRef(*c1).toString());
    assert(check_refcount_nz(c2->m_data.pstr->getCount()));
  } else if (n == 3) {
    Cell* c3 = vmStack().indC(2);
#ifdef CHENG_CHECK
  cheng_assert(c3->m_type != KindOfMulti);
#endif
    cellAsVariant(*c3) = concat3(cellAsVariant(*c3).toString(),
                                 cellAsCVarRef(*c2).toString(),
                                 cellAsCVarRef(*c1).toString());
    assert(check_refcount_nz(c3->m_data.pstr->getCount()));
  } else /* n == 4 */ {
    Cell* c3 = vmStack().indC(2);
    Cell* c4 = vmStack().indC(3);
#ifdef CHENG_CHECK
  cheng_assert(c3->m_type != KindOfMulti);
  cheng_assert(c4->m_type != KindOfMulti);
#endif
    cellAsVariant(*c4) = concat4(cellAsVariant(*c4).toString(),
                                 cellAsCVarRef(*c3).toString(),
                                 cellAsCVarRef(*c2).toString(),
                                 cellAsCVarRef(*c1).toString());
    assert(check_refcount_nz(c4->m_data.pstr->getCount()));
  }

  for (int i = 1; i < n; ++i) {
    vmStack().popC();
  }
}

// cheng-hack:
OPTBLD_INLINE void iopNot(IOP_ARGS) {
  AS_ARITH;
  pc++;
  Cell* c1 = vmStack().topC();
  // cheng-hack:
  // for each value inside multi-value variable, calculate and collect the result
  if (UNLIKELY(c1->m_type == KindOfMulti)) {
    START;
    AS_MARITH;
    auto multi = c1->m_data.pmulti;
    TypedValue ret = MultiVal::makeMultiVal();
    auto ret_multi = ret.m_data.pmulti;
    // go through all the values 
    for (int i = 0; i < multi->valSize(); i++) {
      TypedValue *c = multi->getByVal(i);
      TypedValue *tmp_result = Variant(!cellAsVariant(*c).toBoolean()).asTypedValue();
      ret_multi->addValue(*tmp_result);
    }
    tvCopy(ret, *c1);
    END;
  } else {
    cellAsVariant(*c1) = !cellAsVariant(*c1).toBoolean();
  }
}

// cheng-hack:
template<class Op>
OPTBLD_INLINE void implCellBinOp(PC& pc, Op op) {
  pc++;
  auto const c1 = vmStack().topC();
  auto const c2 = vmStack().indC(1);
  if (UNLIKELY(c1->m_type == KindOfMulti ||
               c2->m_type == KindOfMulti)) {
    START;
    AS_MARITH;
    bool isFirstMulti = (c1->m_type == KindOfMulti);  
    bool isSecondMulti = (c2->m_type == KindOfMulti);  
    MultiVal* m1 = isFirstMulti ? c1->m_data.pmulti : nullptr;
    MultiVal* m2 = isSecondMulti ? c2->m_data.pmulti : nullptr;


#ifdef CHENG_CHECK
    if (isFirstMulti && isSecondMulti) {
      cheng_assert( m1->valSize() == m2->valSize() );
    }
#endif

    TypedValue ret_multi = MultiVal::makeMultiVal();
    if (isFirstMulti && isSecondMulti) {
      // (M, M) case
      for (int i = 0; i < m1->valSize(); i++) {
        auto const result = op(*m2->getByVal(i), *m1->getByVal(i));
        ret_multi.m_data.pmulti->addValue(result);
      }
    } else {
      // (S, M) and (M, S) case
      auto const multi = isFirstMulti ? m1 : m2;
      auto const other = isFirstMulti ? c2 : c1;
#ifdef CHENG_CHECK
      cheng_assert( multi != nullptr); 
#endif
      for (int i = 0; i < multi->valSize(); i++) {
        // should be : op c2, c1
        if (c2 == other) {
          auto const result = op(*other, *multi->getByVal(i));
          ret_multi.m_data.pmulti->addValue(result);
        } else {
          auto const result = op(*multi->getByVal(i), *other);
          ret_multi.m_data.pmulti->addValue(result);
        }
      }
    }

    tvRefcountedDecRef(c2);
    tvCopy(ret_multi, *c2);
    vmStack().popC();
    END;
  } else {
    // normal case
    auto const result = op(*c2, *c1);
    tvRefcountedDecRef(c2);
    *c2 = result;
    vmStack().popC();
  }
}

// cheng-hack:
template<class Op>
OPTBLD_INLINE void implCellBinOpBool(PC& pc, Op op) {
  pc++;
  auto const c1 = vmStack().topC();
  auto const c2 = vmStack().indC(1);

  // cheng-hack:
  if (UNLIKELY(c1->m_type == KindOfMulti ||
               c2->m_type == KindOfMulti) ) {
    START;
    AS_MARITH;

    bool isFirstMulti  = (c1->m_type == KindOfMulti);
    bool isSecondMulti = (c2->m_type == KindOfMulti);
    int reqNum = (isFirstMulti) ? c1->m_data.pmulti->valSize() :
                               c2->m_data.pmulti->valSize();
    TypedValue ret = in_makeMultiVal(reqNum, KindOfBoolean);

    if (isFirstMulti && isSecondMulti) {
#ifdef CHENG_CHECK
      cheng_assert(c1->m_data.pmulti->valSize()
                    == c2->m_data.pmulti->valSize());
#endif
      for (int i = 0; i < reqNum; i++) {
        auto const tmpc1 = c1->m_data.pmulti->getByVal(i);
        auto const tmpc2 = c2->m_data.pmulti->getByVal(i);
        auto result = op(*tmpc2, *tmpc1);
        tvAsVariant(ret.m_data.pmulti->getByVal(i)) = result;
      }
    } else {
      // only one multiVal
      auto const multi = isFirstMulti ? c1 : c2;
      auto const other = isFirstMulti ? c2 : c1;
      for (int i = 0; i < reqNum; i++) {
        auto it = multi->m_data.pmulti->getByVal(i);
        // should be: op c2, c1
        if (c2 == other) {
          auto result = op(*other, *it);
          tvAsVariant(ret.m_data.pmulti->getByVal(i)) = result;
        } else {
          auto result = op(*it, *other);
          tvAsVariant(ret.m_data.pmulti->getByVal(i)) = result;
        }
      }
    }
    tvRefcountedDecRef(c2);
    tvCopy(ret, *c2);
    vmStack().popC();
    END;
  } else {
    bool const result = op(*c2, *c1);
    tvRefcountedDecRef(c2);
    *c2 = make_tv<KindOfBoolean>(result);
    vmStack().popC();
  }

}

OPTBLD_INLINE void iopAdd(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellAdd);
}

OPTBLD_INLINE void iopSub(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellSub);
}

OPTBLD_INLINE void iopMul(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellMul);
}

OPTBLD_INLINE void iopAddO(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellAddO);
}

OPTBLD_INLINE void iopSubO(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellSubO);
}

OPTBLD_INLINE void iopMulO(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellMulO);
}

OPTBLD_INLINE void iopDiv(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellDiv);
}

OPTBLD_INLINE void iopPow(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellPow);
}

OPTBLD_INLINE void iopMod(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellMod);
}

OPTBLD_INLINE void iopBitAnd(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellBitAnd);
}

OPTBLD_INLINE void iopBitOr(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellBitOr);
}

OPTBLD_INLINE void iopBitXor(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellBitXor);
}

OPTBLD_INLINE void iopXor(IOP_ARGS) {
  AS_ARITH;
  implCellBinOpBool(pc, [&] (Cell c1, Cell c2) -> bool {
    return cellToBool(c1) ^ cellToBool(c2);
  });
}

OPTBLD_INLINE void iopSame(IOP_ARGS) {
  AS_ARITH;
  implCellBinOpBool(pc, cellSame);
}

OPTBLD_INLINE void iopNSame(IOP_ARGS) {
  AS_ARITH;
  implCellBinOpBool(pc, [&] (Cell c1, Cell c2) {
    return !cellSame(c1, c2);
  });
}

OPTBLD_INLINE void iopEq(IOP_ARGS) {
  AS_ARITH;
  implCellBinOpBool(pc, [&] (Cell c1, Cell c2) {
    return cellEqual(c1, c2);
  });
}

OPTBLD_INLINE void iopNeq(IOP_ARGS) {
  AS_ARITH;
  implCellBinOpBool(pc, [&] (Cell c1, Cell c2) {
    return !cellEqual(c1, c2);
  });
}

OPTBLD_INLINE void iopLt(IOP_ARGS) {
  AS_ARITH;
  implCellBinOpBool(pc, [&] (Cell c1, Cell c2) {
    return cellLess(c1, c2);
  });
}

OPTBLD_INLINE void iopLte(IOP_ARGS) {
  AS_ARITH;
  implCellBinOpBool(pc, cellLessOrEqual);
}

OPTBLD_INLINE void iopGt(IOP_ARGS) {
  AS_ARITH;
  implCellBinOpBool(pc, [&] (Cell c1, Cell c2) {
    return cellGreater(c1, c2);
  });
}

OPTBLD_INLINE void iopGte(IOP_ARGS) {
  AS_ARITH;
  implCellBinOpBool(pc, cellGreaterOrEqual);
}

OPTBLD_INLINE void iopShl(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellShl);
}

OPTBLD_INLINE void iopShr(IOP_ARGS) {
  AS_ARITH;
  implCellBinOp(pc, cellShr);
}

// curtis:
OPTBLD_INLINE void iopBitNot(IOP_ARGS) {
  AS_ARITH;
  pc++;
  Cell *c1 = vmStack().topC();
  if (UNLIKELY(c1->m_type == KindOfMulti)) {
    START;
    AS_MARITH;
    // multi-val
    //TypedValue ret = MultiVal::cloneMultiVal(c1);
    auto ret_multi = c1->m_data.pmulti;
    for (int i = 0; i < ret_multi->valSize(); i++) {
      TypedValue *c = ret_multi->getByVal(i);
      cellBitNot(*c);
    }
    END;
  } else {
    // non multi-val
    cellBitNot(*c1);
  }
}

// curtis:
OPTBLD_INLINE void iopCastBool(IOP_ARGS) {
  AS_ARITH;
  pc++;
  Cell* c1 = vmStack().topC();
  if (UNLIKELY(c1->m_type == KindOfMulti)) {
    START;
    AS_MARITH;
    // multi-val
    //TypedValue ret = MultiVal::cloneMultiVal(c1);
    auto ret_multi = c1->m_data.pmulti;
    for (int i = 0; i < ret_multi->valSize(); i++) {
      TypedValue *c = ret_multi->getByVal(i);
      tvCastToBooleanInPlace(c);
    }
    ret_multi->setType(KindOfBoolean);
    END;
  } else {
    // non multi-val
    tvCastToBooleanInPlace(c1);
  }
}

// curtis:
OPTBLD_INLINE void iopCastInt(IOP_ARGS) {
  AS_ARITH;
  pc++;
  Cell* c1 = vmStack().topC();
  if (UNLIKELY(c1->m_type == KindOfMulti)) {
    START;
    AS_MARITH;
    // multi-val
    //TypedValue ret = MultiVal::cloneMultiVal(c1);
    auto ret_multi = c1->m_data.pmulti;
    for (int i = 0; i < ret_multi->valSize(); i++) {
      TypedValue *c = ret_multi->getByVal(i);
      tvCastToInt64InPlace(c);
    }
    ret_multi->setType(KindOfInt64);
    END;
  } else { 
    // non multi-val
    tvCastToInt64InPlace(c1);
  }
}

// curtis:
OPTBLD_INLINE void iopCastDouble(IOP_ARGS) {
  AS_ARITH;
  pc++;
  Cell* c1 = vmStack().topC();
  if (UNLIKELY(c1->m_type == KindOfMulti)) {
    START;
    AS_MARITH;
    // multi-val
    //TypedValue ret = MultiVal::cloneMultiVal(c1);
    auto ret_multi = c1->m_data.pmulti;
    for (int i = 0; i < ret_multi->valSize(); i++) {
      TypedValue *c = ret_multi->getByVal(i);
      tvCastToDoubleInPlace(c);
    }
    ret_multi->setType(KindOfDouble);
    END;
  } else { 
    // non multi-val
    tvCastToDoubleInPlace(c1);
  }
}

// curtis:
OPTBLD_INLINE void iopCastString(IOP_ARGS) {
  AS_ARITH;
  pc++;
  Cell* c1 = vmStack().topC();
  if (UNLIKELY(c1->m_type == KindOfMulti)) {
    START;
    AS_MARITH;
    // multi-val
    //TypedValue ret = MultiVal::cloneMultiVal(c1);
    auto ret_multi = c1->m_data.pmulti;
    auto type = KindOfString;
    for (int i = 0; i < ret_multi->valSize(); i++) {
      TypedValue *c = ret_multi->getByVal(i);
      tvCastToStringInPlace(c);
      type = c->m_type;
    }
    ret_multi->setType(type); // can be String or staticString
    END;
  } else { 
    // non multi-val
    tvCastToStringInPlace(c1);
  }
}

// curtis:
OPTBLD_INLINE void iopCastArray(IOP_ARGS) {
  AS_ARITH;
  pc++;
  Cell* c1 = vmStack().topC();
  if (UNLIKELY(c1->m_type == KindOfMulti)) {
    START;
    AS_MARITH;
    // multi-val
    auto multi = c1->m_data.pmulti;
    for (int i = 0; i < multi->valSize(); i++) {
      TypedValue *c = multi->getByVal(i);
      tvCastToArrayInPlace(c);
    }
    multi->setType(KindOfArray);
    END;
  } else { 
    // non multi-val
    tvCastToArrayInPlace(c1);
  }
}

// curtis:
OPTBLD_INLINE void iopCastObject(IOP_ARGS) {
  AS_ARITH;
  pc++;
  Cell* c1 = vmStack().topC();
  if (UNLIKELY(c1->m_type == KindOfMulti)) {
    START;
    AS_MARITH;
    // multi-val
    //TypedValue ret = MultiVal::cloneMultiVal(c1);
    auto ret_multi = c1->m_data.pmulti;
    for (int i = 0; i < ret_multi->valSize(); i++) {
      TypedValue *c = ret_multi->getByVal(i);
      tvCastToObjectInPlace(c);
    }
    ret_multi->setType(KindOfObject);
    END;
  } else { 
    // non multi-val
    tvCastToObjectInPlace(c1);
  }
}

OPTBLD_INLINE bool cellInstanceOf(TypedValue* tv, const NamedEntity* ne) {
  assert(tv->m_type != KindOfRef);
  Class* cls = nullptr;
  switch (tv->m_type) {
    case KindOfUninit:
    case KindOfNull:
    case KindOfBoolean:
    case KindOfResource:
      return false;

    case KindOfInt64:
      cls = Unit::lookupClass(ne);
      return cls && interface_supports_int(cls->name());

    case KindOfDouble:
      cls = Unit::lookupClass(ne);
      return cls && interface_supports_double(cls->name());

    case KindOfStaticString:
    case KindOfString:
      cls = Unit::lookupClass(ne);
      return cls && interface_supports_string(cls->name());

    case KindOfArray:
      cls = Unit::lookupClass(ne);
      return cls && interface_supports_array(cls->name());

    case KindOfObject:
      cls = Unit::lookupClass(ne);
      return cls && tv->m_data.pobj->instanceof(cls);

    case KindOfRef:
    case KindOfMulti: // should split the multi before this stage
    case KindOfClass:
      break;
  }
  not_reached();
}

ALWAYS_INLINE
bool implInstanceOfHelper(const StringData* str1, Cell* c2) {
  const NamedEntity* rhs = NamedEntity::get(str1, false);
  // Because of other codepaths, an un-normalized name might enter the
  // table without a Class* so we need to check if it's there.
  if (LIKELY(rhs && rhs->getCachedClass() != nullptr)) {
    return cellInstanceOf(c2, rhs);
  }
  return false;
}

// cheng-hack: this is a function to check whether all the objs in one
// multi-value belong to one class
static ALWAYS_INLINE void
check_objs_with_same_class(Cell* cell) {
  cheng_assert(cell->m_type == KindOfMulti);

  Class* cls = nullptr;
  for (auto it : *cell->m_data.pmulti) {
    if (cls == nullptr) {
      cls = it->m_data.pobj->getVMClass();
    } else {
      cheng_assert(cls == it->m_data.pobj->getVMClass());
    }
  }
}

// cheng-hack:
OPTBLD_INLINE void iopInstanceOf(IOP_ARGS) {
  AS_ARITH;
  pc++;
  Cell* c1 = vmStack().topC();   // c2 instanceof c1
  Cell* c2 = vmStack().indC(1);

  // cheng-hack: c1 cannot be multiVal
  cheng_assert(c1->m_type != KindOfMulti);
  // this is a trick:
  if (c2->m_type == KindOfMulti) {
    START;
    AS_MARITH;
#ifdef CHENG_CHECK
    // check if all the elements belong to the same class
    if (c2->m_data.pmulti->getType() == KindOfObject) {
      check_objs_with_same_class(c2);
    }
#endif
    c2 = c2->m_data.pmulti->getByVal(0); // this is readonly, so we are fine
    END;
  }

  bool r = false;
  if (IS_STRING_TYPE(c1->m_type)) {
    r = implInstanceOfHelper(c1->m_data.pstr, c2);
  } else if (c1->m_type == KindOfObject) {
    if (c2->m_type == KindOfObject) {
      ObjectData* lhs = c2->m_data.pobj;
      ObjectData* rhs = c1->m_data.pobj;
      r = lhs->instanceof(rhs->getVMClass());
    }
  } else {
    raise_error("Class name must be a valid object or a string");
  }
  vmStack().popC();
  vmStack().replaceC<KindOfBoolean>(r);
}

// cheng-hack:
OPTBLD_INLINE void iopInstanceOfD(IOP_ARGS) {
  AS_ARITH;
  pc++;
  auto id = decode<Id>(pc);
  if (isProfileRequest()) {
    InstanceBits::profile(vmfp()->m_func->unit()->lookupLitstrId(id));
  }
  const NamedEntity* ne = vmfp()->m_func->unit()->lookupNamedEntityId(id);
  Cell* c1 = vmStack().topC();
  // cheng-hack:
  if (c1->m_type == KindOfMulti) {
    START;
    AS_MARITH;
#ifdef CHENG_CHECK
    // check if all the elements belong to the same class
    if (c1->m_data.pmulti->getType() == KindOfObject) {
      check_objs_with_same_class(c1);
    }
#endif
    c1 = c1->m_data.pmulti->getByVal(0); // this is reaqonly, so we are fine
   END;
  }
  bool r = cellInstanceOf(c1, ne);
  vmStack().replaceC<KindOfBoolean>(r);
}

OPTBLD_INLINE void iopPrint(IOP_ARGS) {
  AS_ARITH;
  pc++;
  Cell* c1 = vmStack().topC();
#ifdef CHENG_PRINT_N
  if (c1->m_type == KindOfMulti) {
    c1 = c1->m_data.pmulti->getByVal(CHENG_PRINT_N);
  }
#endif
  if (UNLIKELY(c1->m_type == KindOfMulti)) {
    START;
    AS_MARITH;
    // cases:
    // I:   not with output buffer OR batch_size==1
    // II:  ob_start has been used 
    MultiVal* multi= c1->m_data.pmulti;

    if (g_context->m_isMultiObs) {
      // case 1:
      g_context->write_multi(multi);
    } else {
      // case 2:
      g_context->write("[{");
      for (auto it : *multi) {
        g_context->write(cellAsVariant(*it).toString());
        g_context->write("|||");
      }
      g_context->write("}]");
    }

    END;
  } else {
    // normal case
    g_context->write(cellAsVariant(*c1).toString());
  }
  vmStack().replaceC<KindOfInt64>(1);
}

// curtis:
OPTBLD_INLINE void iopClone(IOP_ARGS) {
  AS_ARITH;
  pc++;
  TypedValue* tv = vmStack().topTV();
  if (tv->m_type == KindOfObject) {
    // not multi-val
    ObjectData* obj = tv->m_data.pobj;
    const Class* class_ UNUSED = obj->getVMClass();
    ObjectData* newobj = obj->clone();
    vmStack().popTV(); // dec refcount
    vmStack().pushNull();
    tv->m_type = KindOfObject;
    tv->m_data.pobj = newobj;
  } else if (tv->m_type == KindOfMulti) {
    START;
    AS_MARITH;
#ifdef CHENG_CHECK
    cheng_assert(tv->m_data.pmulti->getType() == KindOfObject);
#endif
    TypedValue ret = MultiVal::cloneMultiVal(tv);

    tvRefcountedDecRef(tv); // dec refcount
    tvCopy(ret, *tv);
    END;
  } else {
    raise_error("clone called on non-object");
  }
}

// Good to go
// Will exit anyway
OPTBLD_INLINE void iopExit(IOP_ARGS) {
  pc++;
  int exitCode = 0;
  Cell* c1 = vmStack().topC();
  if (c1->m_type == KindOfInt64) {
    exitCode = c1->m_data.num;
  } else {
    g_context->write(cellAsVariant(*c1).toString());
  }
  vmStack().popC();
  vmStack().pushNull();
  throw ExitException(exitCode);
}

// Good to go
// Fatal error anyway
OPTBLD_INLINE void iopFatal(IOP_ARGS) {
  pc++;
  TypedValue* top = vmStack().topTV();
  std::string msg;
  auto kind_char = decode_oa<FatalOp>(pc);
  if (IS_STRING_TYPE(top->m_type)) {
    msg = top->m_data.pstr->data();
  } else {
    msg = "Fatal error message not a string";
  }
  vmStack().popTV();

  switch (kind_char) {
  case FatalOp::RuntimeOmitFrame:
    raise_error_without_first_frame(msg);
    break;
  case FatalOp::Runtime:
  case FatalOp::Parse:
    raise_error(msg);
    break;
  }
}

OPTBLD_INLINE void jmpSurpriseCheck(Offset offset) {
  if (offset <= 0 && UNLIKELY(checkConditionFlags())) {
    EventHook::CheckSurprise();
  }
}

// Good to go
OPTBLD_INLINE void iopJmp(IOP_ARGS) {
  AS_CF;
  pc++;
  auto offset = peek<Offset>(pc);
  jmpSurpriseCheck(offset);
  pc += offset - 1;
}

// Good to go
OPTBLD_INLINE void iopJmpNS(IOP_ARGS) {
  AS_CF;
  pc++;
  auto offset = peek<Offset>(pc);
  pc += offset - 1;
}

// cheng-hack:
// If diverge, then assert false.
template<Op op>
OPTBLD_INLINE void jmpOpImpl(PC& pc) {
  static_assert(op == OpJmpZ || op == OpJmpNZ,
                "jmpOpImpl should only be used by JmpZ and JmpNZ");
  pc++;
  auto offset = peek<Offset>(pc);
  jmpSurpriseCheck(offset);

  Cell* c1 = vmStack().topC();

  // cheng-hack:
  Cell fst_cell;
  if (UNLIKELY(c1->m_type == KindOfMulti)) {
    START;
    AS_MCF;
    fst_cell.m_type = KindOfUninit;
    // check if consistent
    if (UNLIKELY(loop_capture_mode)) {
      bool jump_forward = (offset > 0);
      TypedValue *recent_exit_one = nullptr;
      // check exit, which is jump
      for (int i=0; i<c1->m_data.pmulti->valSize(); i++) {
        // check if this has already been exit
        if (loop_alive[i] == 0) continue;

        bool exit = is_loop_exit(c1, i, jump_forward, op);
        if (exit) {
          recent_exit_one = c1->m_data.pmulti->getByVal(i);
          // remember the output captured output 
          auto loopv = tvToCell(&origin_loop_var_ref);
          if (loopv->m_type == KindOfMulti) {
            loopv = loopv->m_data.pmulti->getByVal(i);
          }
          auto capturev = tvToCell(&origin_capture_var_ref);
          if (capturev->m_type == KindOfMulti) {
            capturev = capturev->m_data.pmulti->getByVal(i);
          }
          cheng_assert(finish_loop_var[i].m_type == KindOfUninit);
          cheng_assert(finish_capture_var[i].m_type == KindOfUninit);
          tvCopy(*loopv, finish_loop_var[i]);
          tvCopy(*capturev, finish_capture_var[i]);
          // delete from mapping
          loop_alive[i] = 0;

#ifdef CHENG_INS_DEBUG
          debug_log << "    loop exit var[" << i << "], cur_alive{ ";
          for (auto it : loop_alive) {
            debug_log << it << " ";
          }
          debug_log << "}\n";
#endif
        }
      }
      // construct c1
      // find the mapping 1 as the delegate, if none, choose the recent_exit_one
      for (int i=0; i<loop_alive.size(); i++) {
        if (loop_alive[i]) {
          fst_cell = *c1->m_data.pmulti->getByVal(i);
        }
      }
      if (fst_cell.m_type == KindOfUninit) {
        cheng_assert(recent_exit_one!=nullptr);
        fst_cell = *recent_exit_one;
      }
      c1 = &fst_cell;
      vmStack().popC(); // dec refcount
      vmStack().pushNull();
    } else {
      bool first = true;
      if (c1->m_data.pmulti->getType() == KindOfInt64 
          || c1->m_data.pmulti->getType() == KindOfBoolean) {
//int counter = 0;
        for (auto it : *c1->m_data.pmulti) {
          if (first) {
            fst_cell = *it;
            first = false;
          }
//std::cout << "[" << counter++ << "] fst_cell=" << fst_cell.pretty() << " vs. it=" << it->pretty() << "\n";
          cheng_assert( (fst_cell.m_data.num == 0) == (it->m_data.num == 0) );
        }
      } else {
        for (auto it : *c1->m_data.pmulti) {
          if (first) {
            fst_cell = *it;
            first = false;
          }
          cheng_assert( toBoolean(cellAsCVarRef(fst_cell)) ==
                        toBoolean(cellAsCVarRef(*it)) );
        }
      }

      // after checking, give one as representation to the following code
      c1 = &fst_cell;
      vmStack().popC(); // dec refcount
      vmStack().pushNull();
    }
    END;
  }


  if (c1->m_type == KindOfInt64 || c1->m_type == KindOfBoolean) {
    int64_t n = c1->m_data.num;
    if (op == OpJmpZ ? n == 0 : n != 0) {
      pc += offset - 1;
      vmStack().popX();
    } else {
      pc += sizeof(Offset);
      vmStack().popX();
    }
  } else {
    auto const condition = toBoolean(cellAsCVarRef(*c1));
    if (op == OpJmpZ ? !condition : condition) {
      pc += offset - 1;
      vmStack().popC();
    } else {
      pc += sizeof(Offset);
      vmStack().popC();
    }
  }
}

// cheng-hack: support by jmpOpImpl
OPTBLD_INLINE void iopJmpZ(IOP_ARGS) {
  AS_CF;
  jmpOpImpl<OpJmpZ>(pc);
}

// cheng-hack: support by jmpOpImpl
OPTBLD_INLINE void iopJmpNZ(IOP_ARGS) {
  AS_CF;
  jmpOpImpl<OpJmpNZ>(pc);
}

// cheng-hack: based on prev iter instructions
OPTBLD_INLINE void iopIterBreak(IOP_ARGS) {
  AS_CF;
  PC savedPc = pc;
  pc++;
  auto veclen = decode<int32_t>(pc);
  assert(veclen > 0);
  Id* iterTypeList = (Id*)pc;
  Id* iterIdList   = (Id*)pc + 1;
  pc += 2 * veclen * sizeof(Id);
  auto offset = peek<Offset>(pc);
  for (auto i = 0; i < 2 * veclen; i += 2) {
    Id iterType = iterTypeList[i];
    Id iterId   = iterIdList[i];
    Iter *iter = frame_iter(vmfp(), iterId);
    // cheng-hack: iter can be a multi-iter
    if (UNLIKELY(iter->isMulti())) {
      // We will free the iter when next time 
      // during Iterinit, see code in Iterinit's
      // "used BUG" comment
    } else {
      // normal case
    switch (iterType) {
      case KindOfIter:  iter->free();  break;
      case KindOfMIter: iter->mfree(); break;
      case KindOfCIter: iter->cfree(); break;
    }
    }
  }
  pc = savedPc + offset;
}

enum class SwitchMatch {
  NORMAL,  // value was converted to an int: match normally
  NONZERO, // can't be converted to an int: match first nonzero case
  DEFAULT, // can't be converted to an int: match default case
};

static SwitchMatch doubleCheck(double d, int64_t& out) {
  if (int64_t(d) == d) {
    out = d;
    return SwitchMatch::NORMAL;
  } else {
    return SwitchMatch::DEFAULT;
  }
}

// Not Impl
OPTBLD_INLINE void iopSwitch(IOP_ARGS) {
  AS_CF;
  PC origPC = pc;
  pc++;
  auto veclen = decode<int32_t>(pc);
  assert(veclen > 0);
  Offset* jmptab = (Offset*)pc;
  pc += veclen * sizeof(*jmptab);
  auto base = decode<int64_t>(pc);
  auto bounded = decode_iva(pc);

  TypedValue* val = vmStack().topTV();
#ifdef CHENG_CHECK
  cheng_assert(val->m_type != KindOfMulti);
#endif
  if (!bounded) {
    assert(val->m_type == KindOfInt64);
    // Continuation switch: no bounds checking needed
    int64_t label = val->m_data.num;
    vmStack().popX();
    assert(label >= 0 && label < veclen);
    pc = origPC + jmptab[label];
  } else {
    // Generic integer switch
    int64_t intval;
    SwitchMatch match = SwitchMatch::NORMAL;

    [&] {
      switch (val->m_type) {
        case KindOfUninit:
        case KindOfNull:
          intval = 0;
          return;

        case KindOfBoolean:
          // bool(true) is equal to any non-zero int, bool(false) == 0
          if (val->m_data.num) {
            match = SwitchMatch::NONZERO;
          } else {
            intval = 0;
          }
          return;

        case KindOfInt64:
          intval = val->m_data.num;
          return;

        case KindOfDouble:
          match = doubleCheck(val->m_data.dbl, intval);
          return;

        case KindOfStaticString:
        case KindOfString: {
          double dval = 0.0;
          DataType t = val->m_data.pstr->isNumericWithVal(intval, dval, 1);
          switch (t) {
            case KindOfNull:
              intval = 0;
              break;
            case KindOfInt64:
              // do nothing
              break;
            case KindOfDouble:
              match = doubleCheck(dval, intval);
              break;
            case KindOfUninit:
            case KindOfBoolean:
            case KindOfStaticString:
            case KindOfString:
            case KindOfArray:
            case KindOfObject:
            case KindOfResource:
            case KindOfRef:
            case KindOfMulti:
            case KindOfClass:
              not_reached();
          }
          tvRefcountedDecRef(val);
          return;
        }

        case KindOfArray:
          match = SwitchMatch::DEFAULT;
          tvDecRef(val);
          return;

        case KindOfObject:
          intval = val->m_data.pobj->toInt64();
          tvDecRef(val);
          return;

        case KindOfResource:
          intval = val->m_data.pres->o_toInt64();
          tvDecRef(val);
          return;

        case KindOfRef:
        case KindOfMulti:
        case KindOfClass:
          break;
      }
      not_reached();
    }();
    vmStack().discard();

    if (match != SwitchMatch::NORMAL ||
        intval < base || intval >= (base + veclen - 2)) {
      switch (match) {
        case SwitchMatch::NORMAL:
        case SwitchMatch::DEFAULT:
          pc = origPC + jmptab[veclen - 1];
          break;

        case SwitchMatch::NONZERO:
          pc = origPC + jmptab[veclen - 2];
          break;
      }
    } else {
      pc = origPC + jmptab[intval - base];
    }
  }
}

// Not Impl
OPTBLD_INLINE void iopSSwitch(IOP_ARGS) {
  AS_CF;
  PC origPC = pc;
  pc++;
  auto veclen = decode<int32_t>(pc);
  assert(veclen > 1);
  unsigned cases = veclen - 1; // the last vector item is the default case
  StrVecItem* jmptab = (StrVecItem*)pc;
  pc += veclen * sizeof(*jmptab);

  Cell* val = tvToCell(vmStack().topTV());
#ifdef CHENG_CHECK
  cheng_assert(val->m_type != KindOfMulti);
#endif
  Unit* u = vmfp()->m_func->unit();
  unsigned i;
  for (i = 0; i < cases; ++i) {
    auto& item = jmptab[i];
    const StringData* str = u->lookupLitstrId(item.str);
    if (cellEqual(*val, str)) {
      pc = origPC + item.dest;
      break;
    }
  }
  if (i == cases) {
    // default case
    pc = origPC + jmptab[veclen-1].dest;
  }
  vmStack().popC();
}

OPTBLD_INLINE void ret(PC& pc) {
  // Get the return value.
  TypedValue retval = *vmStack().topTV();

#ifdef CHENG_INS_DEBUG
  debug_log << "    ret value: " << retval.pretty() << "\n";
#endif

  // Free $this and local variables. Calls FunctionReturn hook. The return value
  // is kept on the stack so that the unwinder would free it if the hook fails.
  frame_free_locals_inl(vmfp(), vmfp()->func()->numLocals(), &retval);
  vmStack().discard();

  // If in an eagerly executed async function, wrap the return value
  // into succeeded StaticWaitHandle.
  if (UNLIKELY(!vmfp()->resumed() && vmfp()->func()->isAsyncFunction())) {
    auto const& retvalCell = *tvAssertCell(&retval);
    auto const waitHandle = c_StaticWaitHandle::CreateSucceeded(retvalCell);
    cellCopy(make_tv<KindOfObject>(waitHandle), retval);
  }

  if (isProfileRequest()) {
    profileIncrementFuncCounter(vmfp()->func());
  }

  // Grab caller info from ActRec.
  ActRec* sfp = vmfp()->sfp();
  Offset soff = vmfp()->m_soff;

  if (LIKELY(!vmfp()->resumed())) {
    // Free ActRec and store the return value.
    vmStack().ndiscard(vmfp()->func()->numSlotsInFrame());
    vmStack().ret();
    *vmStack().topTV() = retval;
    assert(vmStack().topTV() == &vmfp()->m_r);
  } else if (vmfp()->func()->isAsyncFunction()) {
    // Mark the async function as succeeded and store the return value.
    assert(!sfp);
    frame_afwh(vmfp())->ret(retval);
  } else if (vmfp()->func()->isAsyncGenerator()) {
    // Mark the async generator as finished.
    assert(IS_NULL_TYPE(retval.m_type));
    auto const gen = frame_async_generator(vmfp());
    auto const eagerResult = gen->ret();
    if (eagerResult) {
      // Eager execution => return StaticWaitHandle.
      assert(sfp);
      vmStack().pushObjectNoRc(eagerResult);
    } else {
      // Resumed execution => return control to the scheduler.
      assert(!sfp);
    }
  } else if (vmfp()->func()->isNonAsyncGenerator()) {
    // Mark the generator as finished and store the return value.
    assert(IS_NULL_TYPE(retval.m_type));
    frame_generator(vmfp())->ret();

    // Push return value of next()/send()/raise().
    vmStack().pushNull();
  } else {
    not_reached();
  }

  // Return control to the caller.
  vmfp() = sfp;
  pc = LIKELY(vmfp() != nullptr) ? vmfp()->func()->getEntry() + soff : nullptr;
}

// Good to go
OPTBLD_INLINE void iopRetC(IOP_ARGS) {
  AS_CF;
  pc++;
  ret(pc);
}

// Good to go
OPTBLD_INLINE void iopRetV(IOP_ARGS) {
  AS_CF;
  pc++;
  assert(!vmfp()->resumed());
  assert(!vmfp()->func()->isResumable());
  ret(pc);
}

// Good to go
OPTBLD_INLINE void iopUnwind(IOP_ARGS) {
  AS_CF;
  assert(!g_context->m_faults.empty());
  assert(g_context->m_faults.back().m_raiseOffset != kInvalidOffset);
  throw VMPrepareUnwind();
}

// Good to go
OPTBLD_INLINE void iopThrow(IOP_ARGS) {
  AS_CF;
  Cell* c1 = vmStack().topC();
#ifdef CHENG_CHECK
  cheng_assert(c1->m_type != KindOfMulti);
#endif
  if (c1->m_type != KindOfObject ||
      !c1->m_data.pobj->instanceof(SystemLib::s_ExceptionClass)) {
    raise_error("Exceptions must be valid objects derived from the "
                "Exception base class");
  }

  Object obj(c1->m_data.pobj);
  vmStack().popC();
  DEBUGGER_ATTACHED_ONLY(phpDebuggerExceptionThrownHook(obj.get()));
  throw obj;
}

// Good to go
OPTBLD_INLINE void iopAGetC(IOP_ARGS) {
  AS_GET;
  pc++;
  TypedValue* tv = vmStack().topTV();
#ifdef CHENG_CHECK
  cheng_assert(LIKELY(tv->m_type != KindOfMulti));
#endif
  lookupClsRef(tv, tv, true);
}

// Good to go
OPTBLD_INLINE void iopAGetL(IOP_ARGS) {
  AS_GET;
  pc++;
  auto local = decode_la(pc);
  vmStack().pushUninit();
  TypedValue* fr = frame_local_inner(vmfp(), local);
#ifdef CHENG_CHECK
  cheng_assert(fr->m_type != KindOfMulti);
#endif
  lookupClsRef(fr, vmStack().top());
}

static void raise_undefined_local(ActRec* fp, Id pind) {
  assert(pind < fp->m_func->numNamedLocals());
  raise_notice(Strings::UNDEFINED_VARIABLE,
               fp->m_func->localVarName(pind)->data());
}

// cheng-hack:
// Try to deref multiRef here
// 
// used by CGetL/CGetL2/CGetL3/FPassL (by cgetl_body)
//         CGetN/CGetG
static inline void cgetl_inner_body(TypedValue* src_fr, TypedValue* to) {
  assert(src_fr->m_type != KindOfUninit);
  auto fr = tvToCell(src_fr);
  if (UNLIKELY(fr->m_type == KindOfMulti
               && fr->m_data.pmulti->getType() == KindOfRef)) {
    START;
    AS_MGET;
#ifdef CHENG_INS_ONLY_DEBUG
    if (should_count) debug_log << "    cgetl_inner: deref the multi-ref to multi-val\n";
#endif
    // create new multiVal
    TypedValue ret = MultiVal::makeMultiVal();
    for (auto it : *fr->m_data.pmulti) {
      // deref multiRef
      ret.m_data.pmulti->addValue(*tvToCell(it));
    }
    tvCopy(ret, *to);
    END;
  } else {
#ifdef CHENG_INS_DEBUG
    debug_log << "    cgetl_inner: deref the ref as normal, " << fr->pretty() << "\n";
    if (tvToCell(fr)->m_type == KindOfMulti) {
      debug_log << "       {{ " << tvToCell(fr)->m_data.pmulti->dump("    ") << "}}\n";
    }
#endif
    // normal case
    cellDup(*fr, *to);
  }
}

// cheng-hack: used by CGetL/CGetL2/CGetL3/FPassL
static inline void cgetl_body(ActRec* fp,
                              TypedValue* fr,
                              TypedValue* to,
                              Id pind) {
  if (fr->m_type == KindOfUninit) {
    // `to' is uninitialized here, so we need to tvWriteNull before
    // possibly causing stack unwinding.
    tvWriteNull(to);
    raise_undefined_local(fp, pind);
  } else {
    cgetl_inner_body(fr, to);
  }
}

// cheng-hack: support in cgetl_inner_body
OPTBLD_INLINE void iopCGetL(IOP_ARGS) {
  AS_GET;
  pc++;
  auto local = decode_la(pc);
  Cell* to = vmStack().allocC();
  TypedValue* fr = frame_local(vmfp(), local);
#ifdef CHENG_INS_DEBUG
  auto txt = HHVM_FN(print_r)(tvAsVariant(fr), true);
  debug_log << "  Local: " << fr->pretty() << " : {{"
    << txt.toString().toCppString() << "}}\n";
#endif
#ifdef CHENG_INS_ONLY_DEBUG
  if(should_count) debug_log << "    cgetl: " << fr->pretty() << "\n";
#endif
  cgetl_body(vmfp(), fr, to, local);
}

// cheng-hack: support in cgetl_inner_body
OPTBLD_INLINE void iopCGetL2(IOP_ARGS) {
  AS_GET;
  pc++;
  auto local = decode_la(pc);
  TypedValue* oldTop = vmStack().topTV();
  TypedValue* newTop = vmStack().allocTV();
  memcpy(newTop, oldTop, sizeof *newTop);
  Cell* to = oldTop;
  TypedValue* fr = frame_local(vmfp(), local);
#ifdef CHENG_INS_DEBUG
  auto txt = HHVM_FN(print_r)(tvAsVariant(fr), true);
  debug_log << "  Local: " << fr->pretty() << " : {{"
    << txt.toString().toCppString() << "}}\n";
#endif
  cgetl_body(vmfp(), fr, to, local);
}

// cheng-hack: support in cgetl_inner_body
OPTBLD_INLINE void iopCGetL3(IOP_ARGS) {
  AS_GET;
  pc++;
  auto local = decode_la(pc);
  TypedValue* oldTop = vmStack().topTV();
  TypedValue* oldSubTop = vmStack().indTV(1);
  TypedValue* newTop = vmStack().allocTV();
  memmove(newTop, oldTop, sizeof *oldTop * 2);
  Cell* to = oldSubTop;
  TypedValue* fr = frame_local(vmfp(), local);
  cgetl_body(vmfp(), fr, to, local);
}

// Good to go
OPTBLD_INLINE void iopPushL(IOP_ARGS) {
  pc++;
  auto local = decode_la(pc);
  TypedValue* locVal = frame_local(vmfp(), local);
  assert(locVal->m_type != KindOfUninit);
  assert(locVal->m_type != KindOfRef);

  TypedValue* dest = vmStack().allocTV();
  *dest = *locVal;
  locVal->m_type = KindOfUninit;
}

// Good to go
OPTBLD_INLINE void iopCGetN(IOP_ARGS) {
  AS_GET;
  pc++;
  StringData* name;
  TypedValue* to = vmStack().topTV();
#ifdef CHENG_CHECK
  cheng_assert(to->m_type != KindOfMulti);
#endif
  TypedValue* fr = nullptr;
  lookup_var(vmfp(), name, to, fr);
  if (fr == nullptr || fr->m_type == KindOfUninit) {
    raise_notice(Strings::UNDEFINED_VARIABLE, name->data());
    tvRefcountedDecRef(to);
    tvWriteNull(to);
  } else {
    tvRefcountedDecRef(to);
    cgetl_inner_body(fr, to);
  }
  decRefStr(name); // TODO(#1146727): leaks during exceptions
}

// Good to go
// FIXME: check the single_mode!
OPTBLD_INLINE void iopCGetG(IOP_ARGS) {
  AS_GET;
  pc++;
  StringData* name;
  TypedValue* to = vmStack().topTV();
  
  // cheng-hack: "to" is used as key here
#ifdef CHENG_CHECK
  cheng_assert(to->m_type != KindOfMulti);
#endif

  TypedValue* fr = nullptr;
  lookup_gbl(vmfp(), name, to, fr);
  if (fr == nullptr) {
    if (MoreWarnings) {
      raise_notice(Strings::UNDEFINED_VARIABLE, name->data());
    }
    tvRefcountedDecRef(to);
    tvWriteNull(to);
  } else if (fr->m_type == KindOfUninit) {
    raise_notice(Strings::UNDEFINED_VARIABLE, name->data());
    tvRefcountedDecRef(to);
    tvWriteNull(to);
  } else {
    tvRefcountedDecRef(to);
    cgetl_inner_body(fr, to); // suppored by inner
  }
  decRefStr(name); // TODO(#1146727): leaks during exceptions
}

struct SpropState {
  StringData* name;
  TypedValue* clsref;
  TypedValue* nameCell;
  TypedValue* output;
  TypedValue* val;
  bool visible;
  bool accessible;
};

// cheng-hack: Not Impl
// Used by IssetS/IsEmptyS/IncDecS
//         CGetS/VGetS (through getS())
static void spropInit(SpropState& ss) {
  ss.clsref = vmStack().topTV();
  ss.nameCell = vmStack().indTV(1);
#ifdef CHENG_CHECK
  cheng_assert(ss.clsref->m_type != KindOfMulti);
  cheng_assert(ss.nameCell->m_type != KindOfMulti);
#endif
  ss.output = ss.nameCell;
  lookup_sprop(vmfp(), ss.clsref, ss.name, ss.nameCell, ss.val, ss.visible,
               ss.accessible);
}

static void spropFinish(SpropState& ss) {
  decRefStr(ss.name);
}


// cheng-hack:
// This is static class variables, can be multi-value
template<bool box> void getS(PC& pc) {
  //cheng-hack: for CGetS/VGetS
#ifdef CHENG_CHECK
  cheng_assert(vmStack().topTV()->m_type != KindOfMulti);
  cheng_assert(vmStack().indTV(1)->m_type != KindOfMulti);
#endif

  pc++;
  SpropState ss;
  spropInit(ss);
  if (!(ss.visible && ss.accessible)) {
    raise_error("Invalid static property access: %s::%s",
                ss.clsref->m_data.pcls->name()->data(),
                ss.name->data());
  }

  if (box) {
    if (ss.val->m_type != KindOfRef) {
      tvBox(ss.val); // ss.val can be multi, then ref-to-multi
    }
    refDup(*ss.val, *ss.output);
  } else {
    cellDup(*tvToCell(ss.val), *ss.output);
  }
  vmStack().popA();
  spropFinish(ss);
}

// Not Impl, see getS()
OPTBLD_INLINE void iopCGetS(IOP_ARGS) {
  AS_GET;
  getS<false>(pc);
}

// curtis:
// cheng-hack: supported by memberHelperPre
OPTBLD_INLINE void iopCGetM(IOP_ARGS) {
  AS_MEMBER;
  pc++;
  MemberState mstate;
  // NOTE: for ins_counter to avoid __get()
#ifdef CHENG_COUNT_INS
  nested_ins_level_inc(); 
#endif
  // NOTE: multiVal has already been handled here
  auto tvRet = getHelper(pc, mstate);
  if (tvRet->m_type == KindOfRef) {
    tvUnbox(tvRet);
  }
#ifdef CHENG_COUNT_INS
  nested_ins_level_dec();
#endif
}

// cheng-hack:
//   used by VGetL/VGetN/VGetG/FPassL
static inline void vgetl_body(TypedValue* fr, TypedValue* to) {
  // cheng-hack: 
  if (UNLIKELY(fr->m_type == KindOfMulti)) {
    START;
    AS_MGET;
    // If fr is multi-ref, just copy; otherwise, make a ref-to-multi
    if (fr->m_data.pmulti->getType() != KindOfRef) {
      tvBox(fr);
    }
    // NOTE: see NOTE(1)
    tvDup(*fr, *to);
    END;
  } else {
    // normal case
    if (fr->m_type != KindOfRef) {
      tvBox(fr);
    }
    refDup(*fr, *to);
  }
}

// cheng-hack: supported by vgetl_body()
OPTBLD_INLINE void iopVGetL(IOP_ARGS) {
  AS_GET;
  pc++;
  auto local = decode_la(pc);
  Ref* to = vmStack().allocV();
  TypedValue* fr = frame_local(vmfp(), local);
  vgetl_body(fr, to);
}

// cheng-hack: supported by vgetl_body()
OPTBLD_INLINE void iopVGetN(IOP_ARGS) {
  AS_GET;
  pc++;
  StringData* name;
  TypedValue* to = vmStack().topTV();
#ifdef CHENG_CHECK
  cheng_assert(to->m_type != KindOfMulti);
#endif
  TypedValue* fr = nullptr;
  lookupd_var(vmfp(), name, to, fr);
  assert(fr != nullptr);
  tvRefcountedDecRef(to);
  vgetl_body(fr, to);
  decRefStr(name);
}

// cheng-hack: supported by vgetl_body()
// FIXME: single-mode support needed
OPTBLD_INLINE void iopVGetG(IOP_ARGS) {
  AS_GET;
  pc++;
  StringData* name;
  TypedValue* to = vmStack().topTV();
  TypedValue* fr = nullptr;

  // cheng-hack:
#ifdef CHENG_CHECK
  cheng_assert(to->m_type != KindOfMulti);
#endif

  lookupd_gbl(vmfp(), name, to, fr);
  assert(fr != nullptr);
  tvRefcountedDecRef(to);
  vgetl_body(fr, to); // supported inside
  decRefStr(name);
}

// Supported, see getS()
OPTBLD_INLINE void iopVGetS(IOP_ARGS) {
  AS_GET;
  getS<true>(pc);
}

// cheng-hack:
OPTBLD_INLINE void iopVGetM(IOP_ARGS) {
  AS_MEMBER;
  pc++;
  MemberState mstate;
  // cheng-hack:
  mstate.isMultiBase = false;
  mstate.isVGetM = true;
#ifdef CHENG_COUNT_INS
  nested_ins_level_inc();
#endif

  TypedValue* tv1 = vmStack().allocTV();
  tvWriteUninit(tv1);
  if (!setHelperPre<false, true, false, true, 1,
      VectorLeaveCode::ConsumeAll>(pc, mstate)) {
    // cheng-hack:
    if (UNLIKELY(mstate.isMultiBase)) {
      // (1) Init 
      TypedValue result = MultiVal::makeMultiVal();
      // (2) fetch each val from base_list
      for (auto it : *mstate.base_list) {
#ifdef CHENG_INS_DEBUG
        debug_log << "  This is VGetM element: " << it->pretty() << "\n";
#endif
        // (3) do the job
        TypedValue tmpTV;
        if (it->m_type != KindOfRef) {
          tvBox(it);
        }
        refDup(*it, tmpTV); // increase the ref count
        result.m_data.pmulti->addValueNoInc(tmpTV); // no need to increase
      }
      // do shrink
      auto single = result.m_data.pmulti->shrinkToSingle();
      if (single == nullptr) {
        // copy the result to the right place
        // result is a multi-ref
        tvCopy(result, *tv1);
#ifdef CHENG_INS_DEBUG
      debug_log << "  The return value is:\n" << tv1->m_data.pmulti->dump("  ");
#endif
      } else {
        refDup(*single, *tv1);
        tvDecRef(&result);
      }
    } else {
      // original case
      if (mstate.base->m_type != KindOfRef) {
        tvBox(mstate.base);
      }
      refDup(*mstate.base, *tv1);
    }
  } else {
    tvWriteNull(tv1);
    tvBox(tv1);
  }
  setHelperPost<1>(mstate.ndiscard);
#ifdef CHENG_COUNT_INS
  nested_ins_level_dec();
#endif
}

// cheng-hack:
OPTBLD_INLINE void iopIssetN(IOP_ARGS) {
  AS_ISSET;
  pc++;
  StringData* name;
  TypedValue* tv1 = vmStack().topTV(); // this is name
  // cheng-hack:
#ifdef CHENG_CHECK
  cheng_assert(tv1->m_type != KindOfMulti);
#endif
  TypedValue* tv = nullptr;
  bool e;
  lookup_var(vmfp(), name, tv1, tv);
  // cheng-hack:
  if (UNLIKELY(tv!=nullptr && tv->m_type == KindOfMulti)) {
    START;
    AS_MISSET;
    TypedValue ret = MultiVal::makeMultiVal();
    for (auto it : *tv->m_data.pmulti) {
      e = !cellIsNull(tvToCell(it));
      TypedValue tmp;
      tmp.m_type = KindOfBoolean;
      tmp.m_data.num = e;
      ret.m_data.pmulti->addValue(tmp);
    }
    // copy ret to the right place
    tvCopy(ret, *vmStack().topTV());
    decRefStr(name);
    END;
  } else {
    // normal case
  if (tv == nullptr) {
    e = false;
  } else {
    e = !cellIsNull(tvToCell(tv));
    }
  vmStack().replaceC<KindOfBoolean>(e);
  decRefStr(name);
  }
}

// cheng-hack:
OPTBLD_INLINE void iopIssetG(IOP_ARGS) {
  AS_ISSET;
  pc++;
  StringData* name;
  TypedValue* tv1 = vmStack().topTV(); // this is name
  // cheng-hack:
#ifdef CHENG_CHECK
  cheng_assert(tv1->m_type != KindOfMulti);
#endif
  TypedValue* tv = nullptr;
  bool e;
  lookup_gbl(vmfp(), name, tv1, tv);
  // cheng-hack:
  // TODO: don't know how to construct IssetG (later: what does this mean?)
  if (UNLIKELY(tv!=nullptr && tv->m_type == KindOfMulti)) {
    START;
    AS_MISSET;
    TypedValue ret = MultiVal::makeMultiVal();
    for (auto it : *tv->m_data.pmulti) {
      e = !cellIsNull(tvToCell(it));
      TypedValue tmp;
      tmp.m_type = KindOfBoolean;
      tmp.m_data.num = e;
      ret.m_data.pmulti->addValue(tmp);
    }
    // copy ret to the right place
    tvCopy(ret, *vmStack().topTV());
    decRefStr(name);
    END;
  } else {
    // normal case
  if (tv == nullptr) {
    e = false;
  } else {
    e = !cellIsNull(tvToCell(tv));
  }
  vmStack().replaceC<KindOfBoolean>(e);
  decRefStr(name);
  }
}

// Not Impl, see spropInit()
OPTBLD_INLINE void iopIssetS(IOP_ARGS) {
  AS_ISSET;
  pc++;
  SpropState ss;
  spropInit(ss);
  bool e;
  if (!(ss.visible && ss.accessible)) {
    e = false;
  } else {
    e = !cellIsNull(tvToCell(ss.val));
  }
  vmStack().popA();
  ss.output->m_data.num = e;
  ss.output->m_type = KindOfBoolean;
  spropFinish(ss);
}

// cheng-hack: used by IssetM/EmptyM
template <bool isEmpty>
OPTBLD_INLINE void isSetEmptyM(PC& pc) {
  pc++;
  MemberState mstate;
  // cheng-hack:
  mstate.isMultiBase = false;
  mstate.isVGetM = false;

  getHelperPre<false,false,VectorLeaveCode::LeaveLast>(pc, mstate);
  // Process last member specially, in order to employ the IssetElem/IssetProp
  // operations.
  bool isSetEmptyResult = false;

#ifdef CHENG_COUNT_INS
  nested_ins_level_inc();
#endif
  // cheng-hack:
  bool multi_base = false, multi_index = false;
  int multi_num = 1;
  TypedValue* base = mstate.base;
  TypedValue* curMember = mstate.curMember;
  TypedValue multi_ret;
  TypedValue tmp_args[mstate.ndiscard];

  if (UNLIKELY(mstate.isMultiBase)) {
    multi_base = true;
    multi_num = mstate.base_list->size();
  }
  if (UNLIKELY(mstate.curMember->m_type == KindOfMulti)) {
    multi_index = true;
    multi_num = mstate.curMember->m_data.pmulti->valSize();
  }
  if (UNLIKELY(multi_base || multi_index)) {
    multi_ret = MultiVal::makeMultiVal(); 
    memcpy(tmp_args, vmStack().topTV(), sizeof(TypedValue)*mstate.ndiscard);
  }

#ifdef CHENG_CHECK
  if (multi_base) cheng_assert(mstate.base_list->size() == multi_num);
  if (multi_index) cheng_assert(mstate.curMember->m_data.pmulti->valSize() == multi_num);
#endif

#ifdef CHENG_INS_ONLY_DEBUG
  debug_log << "  multi_base(" << multi_base << "), multi_index(" << multi_index << ") \n";
  if (!multi_base) {
    debug_log << "   single base => " << mstate.base->pretty() << "\n";
  }
#endif

  if (UNLIKELY(multi_base || multi_index )) {START; AS_MMEMBER;}

  for (int i = 0; i < multi_num; i++) {
    if (UNLIKELY(multi_base || multi_index)) {
      if (multi_base) base = (*mstate.base_list)[i];
      if (multi_index) curMember = mstate.curMember->m_data.pmulti->getByVal(i);
    }
    // cheng-hack: NOTE: I assume that the following snippet will not affecte mstate

  switch (mstate.mcode) {
    case MEL:
    case MEC:
    case MET:
    case MEI: {
      isSetEmptyResult = IssetEmptyElem<isEmpty>(
        mstate.scratch, *mstate.ref.asTypedValue(), base,
        *curMember
      );
      break;
    }
    case MPL:
    case MPC:
    case MPT: {
      Class* ctx = arGetContextClass(vmfp());
      isSetEmptyResult = IssetEmptyProp<isEmpty>(
        ctx, base, *curMember
      );
      break;
    }
    case MW:
    case InvalidMemberCode:
      assert(false);
  }

  // cheng-hack: collect the result
  if (UNLIKELY(multi_base || multi_index)) {
    TypedValue tmp;
    tmp.m_type = KindOfBoolean;
    tmp.m_data.num = isSetEmptyResult;
    multi_ret.m_data.pmulti->addValue(tmp);
  }
  }

  // cheng-hack: copy to stack
  if (UNLIKELY(multi_base || multi_index)) {
    memcpy(vmStack().topTV(), tmp_args, sizeof(TypedValue)*mstate.ndiscard);
    auto tvRet = getHelperPost(mstate.ndiscard);
#ifdef CHENG_INS_DEBUG
    auto txt = HHVM_FN(print_r)(tvAsVariant(&multi_ret), true);
    debug_log << "    IssetM MultiVal Result: {{" 
      << txt.toString().toCppString() << "}}\n";
#endif
    tvCopy(multi_ret, *tvRet);
    END;
  } else {
    // normal case
  auto tvRet = getHelperPost(mstate.ndiscard);
  tvRet->m_data.num = isSetEmptyResult;
  tvRet->m_type = KindOfBoolean;
  }
#ifdef CHENG_COUNT_INS
  nested_ins_level_dec();
#endif
}

// Supported, see isSetEmptyM()
OPTBLD_INLINE void iopIssetM(IOP_ARGS) {
  AS_MEMBER;
  isSetEmptyM<false>(pc);
}

// Supported
OPTBLD_INLINE void iopIssetL(IOP_ARGS) {
  AS_ISSET;
  pc++;
  auto local = decode_la(pc);
  TypedValue* tv = frame_local(vmfp(), local);
  // cheng-hack:
  if (UNLIKELY(tv->m_type == KindOfMulti)) {
    START;
    AS_MISSET;
    TypedValue ret = MultiVal::makeMultiVal();
    for (auto it : *tv->m_data.pmulti) {
      TypedValue tmp;
      tmp.m_type = KindOfBoolean;
      tmp.m_data.num = is_not_null(tvAsCVarRef(it));
      ret.m_data.pmulti->addValue(tmp);
    }

    TypedValue* topTv = vmStack().allocTV();
    // usually should be the same
    auto single = ret.m_data.pmulti->shrinkToSingle();
    if (single == nullptr) {
      tvCopy(ret, *topTv);
    } else {
      //topTv->m_data.num = single->m_data.num;
      //topTv->m_type = KindOfBoolean;
      tvDup(*single, *topTv);
      // FIXME: for performance reason, we may just let it go
      // free the multivalue
      tvDecRef(&ret);
    }
    END;
  } else {
    // normal case
  bool ret = is_not_null(tvAsCVarRef(tv));
  TypedValue* topTv = vmStack().allocTV();
  topTv->m_data.num = ret;
  topTv->m_type = KindOfBoolean;
  }
}

OPTBLD_INLINE static bool isTypeHelper(TypedValue* tv, IsTypeOp op) {
  switch (op) {
  case IsTypeOp::Null:   return is_null(tvAsCVarRef(tv));
  case IsTypeOp::Bool:   return is_bool(tvAsCVarRef(tv));
  case IsTypeOp::Int:    return is_int(tvAsCVarRef(tv));
  case IsTypeOp::Dbl:    return is_double(tvAsCVarRef(tv));
  case IsTypeOp::Arr:    return is_array(tvAsCVarRef(tv));
  case IsTypeOp::Obj:    return is_object(tvAsCVarRef(tv));
  case IsTypeOp::Str:    return is_string(tvAsCVarRef(tv));
  case IsTypeOp::Scalar: return HHVM_FN(is_scalar)(tvAsCVarRef(tv));
  }
  not_reached();
}

// cheng-hack:
//  One MultiVal may have NULL
OPTBLD_INLINE void iopIsTypeL(IOP_ARGS) {
  AS_ISSET;
  pc++;
  auto local = decode_la(pc);
  auto op = decode_oa<IsTypeOp>(pc);
  TypedValue* tv = frame_local(vmfp(), local);
  if (tv->m_type == KindOfUninit) {
    raise_undefined_local(vmfp(), local);
  }

  // cheng-hack:
  // MultiVal should have same type or NULL
  // If tv is a multivalue or it is a ref to the multivalue
  if (UNLIKELY(tv->m_type == KindOfMulti ||
               (tv->m_type == KindOfRef && tv->m_data.pref->tv()->m_type == KindOfMulti)
               )) {
    START;
    AS_MISSET;

    if (tv->m_type == KindOfRef) {
      tv = tv->m_data.pref->tv();
    }

    TypedValue ret = MultiVal::makeMultiVal(); 
    for (auto it : *tv->m_data.pmulti) {
      TypedValue tmp;
      tmp.m_data.num = isTypeHelper(it, op);
      tmp.m_type = KindOfBoolean;
      ret.m_data.pmulti->addValue(tmp);
    }
    // Optimization, shrink, not sure if good for performance or bad
    TypedValue *shrink = ret.m_data.pmulti->shrinkToSingle();
    TypedValue* topTv = vmStack().allocTV();

    if (shrink == nullptr) {
      tvCopy(ret, *topTv); 
    } else {
#ifdef CHENG_INS_DEBUG
      debug_log << "    Shrink the result to single: " << shrink->pretty() << "\n";
#endif
      tvDup(*shrink, *topTv); 
      tvRefcountedDecRef(&ret);
    }
    END;
  } else {
  // original case
  TypedValue* topTv = vmStack().allocTV();
  topTv->m_data.num = isTypeHelper(tv, op);
  topTv->m_type = KindOfBoolean;
  }
}

// cheng-hack:
//  One MultiVal may have NULL
OPTBLD_INLINE void iopIsTypeC(IOP_ARGS) {
  AS_ISSET;
  pc++;
  auto op = decode_oa<IsTypeOp>(pc);
  TypedValue* topTv = vmStack().topTV();
  assert(topTv->m_type != KindOfRef);

  bool ret = false;
  // cheng-hack:
  // MultiVal should have same type
  if (UNLIKELY(topTv->m_type == KindOfMulti)) {
    START;
    AS_MISSET;
    TypedValue ret = MultiVal::makeMultiVal(); 
    for (auto it : *topTv->m_data.pmulti) {
      TypedValue tmp;
      tmp.m_data.num = isTypeHelper(it, op);
      tmp.m_type = KindOfBoolean;
      ret.m_data.pmulti->addValue(tmp);
    }
    // Optimization, shrink, not sure if good for performance or bad
    TypedValue *shrink = ret.m_data.pmulti->shrinkToSingle();
    if (shrink == nullptr) {
      tvCopy(ret, *topTv); 
    } else {
#ifdef CHENG_INS_DEBUG
      debug_log << "    Shrink the result to single: " << shrink->pretty() << "\n";
#endif
      tvDup(*shrink, *topTv); 
      tvRefcountedDecRef(&ret);
    }
    END;
  } else {
    // original case
    ret = isTypeHelper(topTv, op);
    tvRefcountedDecRef(topTv);
    topTv->m_data.num = ret;
    topTv->m_type = KindOfBoolean;
  }
}

// Good to go
OPTBLD_INLINE void iopAssertRATL(IOP_ARGS) {
  pc++;
  auto localId = decode_la(pc);
  if (debug) {
    auto const rat = decodeRAT(vmfp()->m_func->unit(), pc);
    auto const tv = *frame_local(vmfp(), localId);
    auto const func = vmfp()->func();
    auto vm = &*g_context;
    always_assert_flog(
      tvMatchesRepoAuthType(tv, rat),
      "failed assert RATL on local {}: ${} in {}:{}, expected {}, got {}",
      localId,
      localId < func->numNamedLocals() ? func->localNames()[localId]->data()
                                       : "<unnamed>",
      vm->getContainingFileName()->data(),
      vm->getLine(),
      show(rat),
      tv.pretty()
    );
    return;
  }
  pc += encodedRATSize(pc);
}

// Good to go
OPTBLD_INLINE void iopAssertRATStk(IOP_ARGS) {
  pc++;
  auto stkSlot = decode_iva(pc);
  if (debug) {
    auto const rat = decodeRAT(vmfp()->m_func->unit(), pc);
    auto const tv = *vmStack().indTV(stkSlot);
    auto vm = &*g_context;
    always_assert_flog(
      tvMatchesRepoAuthType(tv, rat),
      "failed assert RATStk {} in {}:{}, expected {}, got {}",
      stkSlot,
      vm->getContainingFileName()->data(),
      vm->getLine(),
      show(rat),
      tv.pretty()
    );
    return;
  }
  pc += encodedRATSize(pc);
}

// Good to go
OPTBLD_INLINE void iopBreakTraceHint(IOP_ARGS) {
  pc++;
}

// Support
OPTBLD_INLINE void iopEmptyL(IOP_ARGS) {
  AS_ISSET;
  pc++;
  auto local = decode_la(pc);
  TypedValue* loc = frame_local(vmfp(), local);
  // cheng-hack:
  if (UNLIKELY(loc->m_type == KindOfMulti)) {
    START;
    AS_MISSET;
    TypedValue ret = MultiVal::makeMultiVal();
    for (auto it : *loc->m_data.pmulti) {
      bool e = !cellToBool(*tvToCell(it));
      TypedValue tmp;
      tmp.m_type = KindOfBoolean;
      tmp.m_data.num = e;
      ret.m_data.pmulti->addValue(tmp);
    }
    // usually should be the same
    TypedValue *shrink = ret.m_data.pmulti->shrinkToSingle();
    if (shrink == nullptr) {
      vmStack().pushMultiObject(ret);
    } else {
      vmStack().pushBool(shrink->m_data.num);
      tvDecRef(&ret);
    }
    END;
  } else {
    // normal case
  bool e = !cellToBool(*tvToCell(loc));
  vmStack().pushBool(e);
  }
}

// Support
OPTBLD_INLINE void iopEmptyN(IOP_ARGS) {
  AS_ISSET;
  pc++;
  StringData* name;
  TypedValue* tv1 = vmStack().topTV();
  // cheng-hack:
  cheng_assert(tv1->m_type != KindOfMulti);
  TypedValue* tv = nullptr;
  bool e;
  lookup_var(vmfp(), name, tv1, tv);
  if (tv == nullptr) {
    e = true;
    vmStack().replaceC<KindOfBoolean>(e);
  } else {
    // cheng-hack:
    if (UNLIKELY(tv->m_type == KindOfMulti)) {
      START;
      AS_MISSET;
      TypedValue ret = MultiVal::makeMultiVal();
      for (auto it : *tv->m_data.pmulti) {
        bool e = !cellToBool(*tvToCell(it));
        TypedValue tmp;
        tmp.m_type = KindOfBoolean;
        tmp.m_data.num = e;
        ret.m_data.pmulti->addValue(tmp);
      }
      vmStack().discard();
      // usually should be the same
      TypedValue *shrink = ret.m_data.pmulti->shrinkToSingle();
      if (shrink == nullptr) {
        vmStack().pushMultiObject(ret);
      } else {
        vmStack().pushBool(shrink->m_data.num);
        tvDecRef(&ret);
      }
      END;
    } else {
      // normal case
      e = !cellToBool(*tvToCell(tv));
      vmStack().replaceC<KindOfBoolean>(e);
    }
  }
  decRefStr(name);
}

// Support
OPTBLD_INLINE void iopEmptyG(IOP_ARGS) {
  AS_ISSET;
  pc++;
  StringData* name;
  TypedValue* tv1 = vmStack().topTV();
  // cheng-hack:
  cheng_assert(tv1->m_type != KindOfMulti);
  TypedValue* tv = nullptr;
  bool e;
  lookup_gbl(vmfp(), name, tv1, tv);
  if (tv == nullptr) {
    e = true;
    vmStack().replaceC<KindOfBoolean>(e);
  } else {
    // cheng-hack:
    if (UNLIKELY(tv->m_type == KindOfMulti)) {
      START;
      AS_MISSET;
      TypedValue ret = MultiVal::makeMultiVal();
      for (auto it : *tv->m_data.pmulti) {
        bool e = !cellToBool(*tvToCell(it));
        TypedValue tmp;
        tmp.m_type = KindOfBoolean;
        tmp.m_data.num = e;
        ret.m_data.pmulti->addValue(tmp);
      }
      vmStack().discard();
      // usually should be the same
      TypedValue *shrink = ret.m_data.pmulti->shrinkToSingle();
      if (shrink == nullptr) {
        vmStack().pushMultiObject(ret);
      } else {
        vmStack().pushBool(shrink->m_data.num);
        tvDecRef(&ret);
      }
      END;
    } else {
      // normal case
      e = !cellToBool(*tvToCell(tv));
      vmStack().replaceC<KindOfBoolean>(e);
    }
  }
  decRefStr(name);
}

// Not Impl, see spropInit()
OPTBLD_INLINE void iopEmptyS(IOP_ARGS) {
  AS_ISSET;
  pc++;
  SpropState ss;
  spropInit(ss);
  bool e;
  if (!(ss.visible && ss.accessible)) {
    e = true;
  } else {
    e = !cellToBool(*tvToCell(ss.val));
  }
  vmStack().popA();
  ss.output->m_data.num = e;
  ss.output->m_type = KindOfBoolean;
  spropFinish(ss);
}

// Supported, see isSetEmptyM()
OPTBLD_INLINE void iopEmptyM(IOP_ARGS) {
  AS_MEMBER;
  isSetEmptyM<true>(pc);
}

// curtis:
OPTBLD_INLINE void iopAKExists(IOP_ARGS) {
  pc++;
  TypedValue* arr = vmStack().topTV();
  TypedValue* key = arr + 1;

  if (UNLIKELY(arr->m_type == KindOfMulti)) {
    START;
    AS_MISSET;
    if (UNLIKELY(key->m_type == KindOfMulti)) {
      // Arr and key are multi
      TypedValue ret = MultiVal::makeMultiVal();
      auto ret_multi = ret.m_data.pmulti;
      auto key_multi = key->m_data.pmulti;
      auto arr_multi = arr->m_data.pmulti;
#ifdef CHENG_CHECK
      cheng_assert(key_multi->valSize() == arr_multi->valSize());
#endif
      for (int i = 0; i < key_multi->valSize(); i++) {
        TypedValue *cKey = key_multi->getByVal(i);
        TypedValue *cArr = arr_multi->getByVal(i);
        bool result = HHVM_FN(array_key_exists)(tvAsCVarRef(cKey), tvAsCVarRef(cArr));
        Variant tmp(result);
        TypedValue *tmp_result = tmp.asTypedValue();
        ret_multi->addValue(*tmp_result);
      }
      vmStack().popTV();
      tvCopy(ret, *key);
    } else {
      // Arr is multi, key is non-multi
      auto multi = arr->m_data.pmulti;
      TypedValue ret = MultiVal::makeMultiVal();
      auto ret_multi = ret.m_data.pmulti;
      for (int i = 0; i < multi->valSize(); i++) {
         TypedValue *c = multi->getByVal(i);
         bool result = HHVM_FN(array_key_exists)(tvAsCVarRef(key), tvAsCVarRef(c));
         Variant tmp(result);
         TypedValue *tmp_result = tmp.asTypedValue();
         ret_multi->addValue(*tmp_result);
      }
      vmStack().popTV();
      tvCopy(ret, *key);
    }
    END;
  } else {
    if (UNLIKELY(key->m_type == KindOfMulti)) {
      START;
      AS_MISSET;
      // Arr is non-multi, key is multi
      auto multi = key->m_data.pmulti;
      TypedValue ret = MultiVal::makeMultiVal();
      auto ret_multi = ret.m_data.pmulti;
      for (int i = 0; i < multi->valSize(); i++) {
        TypedValue *c = multi->getByVal(i);
        bool result = HHVM_FN(array_key_exists)(tvAsCVarRef(c), tvAsCVarRef(arr));
        Variant tmp(result);
        TypedValue *tmp_result = tmp.asTypedValue();
        ret_multi->addValue(*tmp_result);
      }
      vmStack().popTV();
      tvCopy(ret, *key);
      END;
    } else {
      // Arr and key are non-multi
      bool result = HHVM_FN(array_key_exists)(tvAsCVarRef(key), tvAsCVarRef(arr));
      vmStack().popTV();
      vmStack().replaceTV<KindOfBoolean>(result);
    }
  }
}

// Not Impl
OPTBLD_INLINE void iopGetMemoKey(IOP_ARGS) {
  pc++;
  auto obj = vmStack().topTV();
#ifdef CHENG_CHECK
  cheng_assert(obj->m_type != KindOfMulti);
#endif
  auto var = HHVM_FN(serialize_memoize_param)(tvAsCVarRef(obj));
  auto res = var.asTypedValue();
  tvRefcountedIncRef(res);
  vmStack().replaceTV(*res);
}

// Not Impl
OPTBLD_INLINE void iopIdx(IOP_ARGS) {
  pc++;
  TypedValue* def = vmStack().topTV();
  TypedValue* key = vmStack().indTV(1);
  TypedValue* arr = vmStack().indTV(2);
#ifdef CHENG_CHECK
  cheng_assert(def->m_type != KindOfMulti);
  cheng_assert(key->m_type != KindOfMulti);
  cheng_assert(arr->m_type != KindOfMulti);
#endif

  TypedValue result = jit::genericIdx(*arr, *key, *def);
  vmStack().popTV();
  vmStack().popTV();
  tvRefcountedDecRef(arr);
  *arr = result;
}

// Not Impl
OPTBLD_INLINE void iopArrayIdx(IOP_ARGS) {
  pc++;
  TypedValue* def = vmStack().topTV();
  TypedValue* key = vmStack().indTV(1);
  TypedValue* arr = vmStack().indTV(2);
#ifdef CHENG_CHECK
  cheng_assert(def->m_type != KindOfMulti);
  cheng_assert(key->m_type != KindOfMulti);
  cheng_assert(arr->m_type != KindOfMulti);
#endif

  Variant result = HHVM_FN(hphp_array_idx)(tvAsCVarRef(arr),
                                  tvAsCVarRef(key),
                                  tvAsCVarRef(def));
  vmStack().popTV();
  vmStack().popTV();
  tvAsVariant(arr) = result;
}

/* cheng-hack:
 * $fr -> $to
 * No matter $fr/$to is a multiVal or multiRef, we will follow the link.
 *
 * NOTE: the $to MUST be a stand-alone varible, a variable which either
 * is local variable or global variable. Cannot be a element in either array
 * or object.
 */
static inline void
tvSetHelper(const Cell fr, TypedValue& inTo) {
  assert(cellIsPlausible(fr));
#ifdef CHENG_CHECK
    // the fr cannot be multi-ref
    cheng_assert(!(fr.m_type == KindOfMulti && fr.m_data.pmulti->getType() == KindOfRef));
    cheng_assert(fr.m_type != KindOfRef);
#endif
  Cell* to = tvToCell(&inTo);

  // if "to" is multi-Ref, it need sepcial care
  if (UNLIKELY(to->m_type == KindOfMulti && to->m_data.pmulti->getType() == KindOfRef)) {
    START;
    AS_MSET;
    // If we have (M, M):
    if (fr.m_type == KindOfMulti) {
      // if this is add_multi(), we will skip
      if (to->m_data.num != fr.m_data.num) {
#ifdef CHENG_INS_DEBUG
    debug_log << "  SetX: \"to\" is multi-ref, as :\n" << to->m_data.pmulti->dump("    ");
    debug_log << "  SetX: \"from\" is multi-val, as :\n" << fr.m_data.pmulti->dump("    ");
#endif
#ifdef CHENG_CHECK
        cheng_assert(fr.m_data.pmulti->valSize() == to->m_data.pmulti->valSize());
#endif
        for (int i = 0; i < fr.m_data.pmulti->valSize(); i++) {
          Cell *tmp_fr = fr.m_data.pmulti->getByVal(i);
          Cell *tmp_to = to->m_data.pmulti->getByVal(i);
          // tvSet will follow the link
          tvSet(*tmp_fr, *tmp_to);
        }
      } else {
        // do nothing, this might be add_multi
      }
    } else {
#ifdef CHENG_INS_DEBUG
      debug_log << "  SetX: \"to\" is multi-ref, as :\n" << to->m_data.pmulti->dump("    ");
      debug_log << "  SetX: \"fr\" is single value, as : {{" << fr.pretty() << "}}\n";
#endif
      // we have (fr, to) = (S, M):
      // FIXME: Not Supported! what if the into is a container-related value??
      cheng_assert(to->m_type != KindOfArray && to->m_type != KindOfObject);
      for (auto it : *to->m_data.pmulti) { tvSet(fr, *it); }
    }
    END;
  } else {
    tvSet(fr, inTo);
  }
  // cheng-hack: interesting old days, keep as a history mark.
  //      // $single-ref = $multi-val
  //      // change the fr to multi-ref
  //      // assign to all the $single-ref
  //      TypedValue multi_ref = MultiVal::cloneMultiVal(fr);
  //      auto orig_ref = inTo.m_data.pref;
  //      tvBoxMulti(&multi_ref);
  //      auto f = [multi_ref, orig_ref] (TypedValue* tv) {
  //        if (tv->m_type == KindOfRef &&
  //            tv->m_data.pref == orig_ref) {
  //#ifdef CHENG_INS_DEBUG
  //          debug_log << "    replace ref {" << tv->pretty() << "} at location "
  //            << tv << " into multi-ref\n";
  //#endif
  //          tvRefcountedDecRef(tv);
  //          tvDup(multi_ref, *tv); 
  //        }
  //      };
  //      // FIXME: there are three more: class static/array/object
  //      iterGlobalVar(f);
  //      iterLocalVar(f);
}


// Support, for performance, expand tvSetHelper() within
OPTBLD_INLINE void iopSetL(IOP_ARGS) {
  AS_SET;
  pc++;
  auto local = decode_la(pc);
  assert(local < vmfp()->m_func->numLocals());
  Cell* fr = vmStack().topC();
  TypedValue* into = frame_local(vmfp(), local);
  // cheng-hack: used to be tvSet(*fr, *to);
  //  Now, check out "fr" and "to" to see if multi-ref exists
  Cell* to = tvToCell(into);
  // if "to" is multi-Ref, it need sepcial care
  if (UNLIKELY(to->m_type == KindOfMulti && to->m_data.pmulti->getType() == KindOfRef)) {
    START;
    AS_MSET;
#ifdef CHENG_INS_ONLY_DEBUG
    if (should_count) debug_log << "    meet multi-ref\n";
#endif
    // If we have (M, M):
    if (fr->m_type == KindOfMulti) {
#ifdef CHENG_INS_ONLY_DEBUG
      if (should_count) debug_log << "    fr is also multi\n";
#endif
      // if this is add_multi(), we will skip
      if (to->m_data.num != fr->m_data.num) {
        for (int i = 0; i < fr->m_data.pmulti->valSize(); i++) {
          Cell *tmp_fr = fr->m_data.pmulti->getByVal(i);
          Cell *tmp_to = to->m_data.pmulti->getByVal(i);
          // tvSet will follow the link
          tvSet(*tmp_fr, *tmp_to);
        }
      } else {
        // do nothing, this might be add_multi
      }
    } else {
#ifdef CHENG_INS_ONLY_DEBUG
      if (should_count) debug_log << "    fr is not multi\n"; 
#endif
      // we have (fr, to) = (S, M):
      // FIXME: Not Supported! what if the into is a container-related value??
      cheng_assert(to->m_type != KindOfArray && to->m_type != KindOfObject);
      for (auto it : *to->m_data.pmulti) { tvSet(*fr, *it); }
    }
    END;
  } else {
    // normal case 
    // tvSet(*fr, *to);
    // cheng-hack: since we've called tvToCell for "to",
    // expand the tvSet(...) below to save several cycles
    assert(cellIsPlausible(fr));
    //Cell* to = tvToCell(&inTo); <--- save this line
    auto const oldType = to->m_type;
    auto const oldDatum = to->m_data.num;
    cellDup(*fr, *to);
    tvRefcountedDecRefHelper(oldType, oldDatum);
  }
}

// Support, see tvSetHelper()
OPTBLD_INLINE void iopSetN(IOP_ARGS) {
  AS_SET;
  pc++;
  StringData* name;
  Cell* fr = vmStack().topC();
  TypedValue* tv2 = vmStack().indTV(1);
#ifdef CHENG_CHECK
  cheng_assert(tv2->m_type != KindOfMulti);
#endif
  TypedValue* to = nullptr;
  lookupd_var(vmfp(), name, tv2, to);
  assert(to != nullptr);
  tvSetHelper(*fr, *to);
  memcpy((void*)tv2, (void*)fr, sizeof(TypedValue));
  vmStack().discard();
  decRefStr(name);
}

// Support, see tvSetHelper()
OPTBLD_INLINE void iopSetG(IOP_ARGS) {
  AS_SET;
  pc++;
  StringData* name;
  Cell* fr = vmStack().topC();
  TypedValue* tv2 = vmStack().indTV(1);
#ifdef CHENG_CHECK
  cheng_assert(tv2->m_type != KindOfMulti);
#endif
  TypedValue* to = nullptr;
  lookupd_gbl(vmfp(), name, tv2, to);
  assert(to != nullptr);

  // cheng-hack: tmp, assert false for a second
  cheng_assert(!single_mode_on);
  // cheng-hack: when in single_mode, expand the global variables.
  if (single_mode_on) {
    if (to->m_type != KindOfMulti) {
      auto multiv = MultiVal::makeMultiVal();
      for (int i=0; i<single_mode_size; i++) {
        multiv.m_data.pmulti->addValue(*to);
      }
      // dec ref to original var
      tvRefcountedDecRef(to);
      // copy the multi to its place
      tvCopy(multiv, *to);
    }

    tvSetHelper(*fr, *(to->m_data.pmulti->getByVal(single_mode_cur_iter)));
    memcpy((void*)tv2, (void*)fr, sizeof(TypedValue));
    vmStack().discard();
    decRefStr(name);
  } else {
    // normal case
  tvSetHelper(*fr, *to);
  memcpy((void*)tv2, (void*)fr, sizeof(TypedValue));
  vmStack().discard();
  decRefStr(name);
  }
}

// Partly not Impl
// Supported in tvSetHelper(...)
OPTBLD_INLINE void iopSetS(IOP_ARGS) {
  AS_SET;
  pc++;
  TypedValue* tv1 = vmStack().topTV();
  TypedValue* classref = vmStack().indTV(1);
  TypedValue* propn = vmStack().indTV(2);

  // cheng-hack:
#ifdef CHENG_CHECK
  cheng_assert(classref->m_type != KindOfMulti);
  cheng_assert(propn->m_type != KindOfMulti);
#endif

  TypedValue* output = propn;
  StringData* name;
  TypedValue* val;
  bool visible, accessible;
  lookup_sprop(vmfp(), classref, name, propn, val, visible, accessible);
  if (!(visible && accessible)) {
    raise_error("Invalid static property access: %s::%s",
                classref->m_data.pcls->name()->data(),
                name->data());
  }
  tvSetHelper(*tv1, *val); // supported inside
  tvRefcountedDecRef(propn);
  memcpy(output, tv1, sizeof(TypedValue));
  vmStack().ndiscard(2);
  decRefStr(name);
}

// support:
//   base is multi 
//   value is multi
//   index is multi
OPTBLD_INLINE void iopSetM(IOP_ARGS) {
  AS_MEMBER;
  PC old_pc = pc;
#ifdef CHENG_COUNT_INS
  nested_ins_level_inc();
#endif
setm_start:
  pc++;
  MemberState mstate;
  mstate.isMultiBase = false;
  mstate.isVGetM = false;
  if (!setHelperPre<false, true, false, false, 1,
      VectorLeaveCode::LeaveLast>(pc, mstate)) {
    Cell* c1 = vmStack().topC(); // this is the value we should assign

    // cheng-hack: mstate.base_list is a pointer to a vector
    // which contains the slots should be set in the following snippet.
    int multi_num = 0;
    bool multi_base = false, multi_value = false, multi_curMember = false;

    if (UNLIKELY(mstate.isMultiBase)) {
      multi_num = mstate.base_list->size();
      multi_base = true;
    }
    if (UNLIKELY(c1->m_type == KindOfMulti)) {
      multi_num = c1->m_data.pmulti->valSize();
      multi_value = true;
    }
    // Used to be a BUG: if the mstate.mcode is MW, curMember might be nullptr
    if (UNLIKELY(mstate.mcode != MW && mstate.curMember->m_type == KindOfMulti)) {
      multi_num = mstate.curMember->m_data.pmulti->valSize();
      multi_curMember = true;
    }

    // NOTE: we should open a hole for the system array here
    // like: $_SERVER["abc"] = $multi
    // but not for: $_SERVER['multi']['innner'] = 10
    if (UNLIKELY(isSystemArr(mstate.orig_base) && !multi_base)) {
#ifdef CHENG_INS_ONLY_DEBUG
      debug_log << "    SetM, trying to set the system array.\n";
#endif
#ifdef CHENG_CHECK
      cheng_assert(!multi_curMember);
#endif
      multi_value = false;
    }

    // If the base is single, but the index/value is multi, we need to split
    // Only for array, not for object
    if (UNLIKELY(!multi_base && (multi_value || multi_curMember) 
                 && mstate.orig_base->m_type == KindOfArray)) {
#ifdef CHENG_INS_ONLY_DEBUG
      debug_log << "    Have to split the single-base...\n";
#endif
      // (S, M)
      TypedValue *orig_base = mstate.orig_base;
      TypedValue split_multi = MultiVal::splitArray(*orig_base, multi_num);
      tvCopy(split_multi, *mstate.orig_base);
      pc = old_pc;
      goto setm_start;
    }

    // used to be a BUG: $obj->ref->array[$multi_indx] = $multi_val;
    // solution: deref first
    if (!multi_base) {
      mstate.base = tvToCell(mstate.base);
    }

    // For obj-array-set-multi problem:
    // e.g. $obj->arr[] = $multi;
    if (UNLIKELY(!multi_base && (multi_curMember || multi_value) &&
                 mstate.base->m_type == KindOfArray)) {
#ifdef CHENG_INS_ONLY_DEBUG
      debug_log << "   Split the last level array...\n";
#endif
      // we met a last level array which need to be splited
      auto arr = mstate.base;

      TypedValue split_multi = MultiVal::splitArray(*arr, multi_num);
      tvCopy(split_multi, *arr); // copy back to original place
      multi_base = true;
      // construct base_list
      mstate.base_list = std::make_shared< std::vector<TypedValue*> >();
      for (auto arr_it : *split_multi.m_data.pmulti) {
        mstate.base_list->push_back(arr_it);
      }
    }

    // For multi-ref-one-obj problem:
    // memberHelperPre might return multi_base with refs pointing to one obj.
    // The ref will deref later within the set function.
    // However, we need to detect this ahead
    if (UNLIKELY(multi_base && (*mstate.base_list)[0]->m_type == KindOfRef)
        && !checkStaticEmptyArray((*mstate.base_list)[0])) {
      // check whether all refs point to one slot
      Cell* first_elem = tvToCell((*mstate.base_list)[0]);
      bool point_to_same_slot = true;
      for (int i=1; i<mstate.base_list->size(); i++) {
        if (first_elem->m_data.num !=
            tvToCell((*mstate.base_list)[i])->m_data.num)
        {
          point_to_same_slot = false;
          break;
        }
      }
      // if point to the same slot, do it once
      if (point_to_same_slot) {
        multi_base = false;
        // we deref here. Is it OK? seems so.
        mstate.base = first_elem;
      }
    }

    // If multi_base, do the set seperately
    // If not, but has
    //  -- multi_curMember: we do not support this yet (should to split)
    //  -- multi_value: do as normal 
    //       e.g. $multi_array[$s_obj]->val = $multival;
    //       e.g. $multi_ref_to_one_obj->val = $multival;
    if (UNLIKELY(multi_base)) {
      TypedValue* base = mstate.base;
      TypedValue* value = c1;
      TypedValue* curMember = mstate.curMember;

#ifdef CHENG_CHECK
      if(multi_base) cheng_assert(mstate.base_list->size() == multi_num);
      if(multi_value) cheng_assert(c1->m_data.pmulti->valSize() == multi_num);
      if(multi_curMember) cheng_assert(mstate.curMember->m_data.pmulti->valSize() == multi_num);
#endif

#ifdef CHENG_INS_DEBUG
      debug_log << "    SetM [" << multi_num <<"]  is_base:" << multi_base 
        << ", is_value: " << multi_value << ", is_member:" << multi_curMember << "\n";
      auto base_txt = HHVM_FN(print_r)(tvAsVariant(base), true);
      auto value_txt = HHVM_FN(print_r)(tvAsVariant(value), true);
      debug_log << "        cur_base: " << base->pretty() << " base content: "<< 
        base_txt.toString().toCppString() << ", cur_value:"
        << value_txt.toString().toCppString() << "\n"; 
#endif

      switch (mstate.mcode) {
      case MW:
        for (int i = 0; i < multi_num; i++) {
          if (multi_base) base = (*mstate.base_list)[i];
          if (multi_value) value = c1->m_data.pmulti->getByVal(i); 
          // normal behavior 
          SetNewElem<true>(base, value);
        }
        break;
      case MEL:
      case MEC:
      case MET:
      case MEI: {
                  for (int i = 0; i < multi_num; i++) {
                    if (multi_base) base = (*mstate.base_list)[i];
                    if (multi_value) value = c1->m_data.pmulti->getByVal(i); 
                    if (multi_curMember) curMember = mstate.curMember->m_data.pmulti->getByVal(i);

                    StringData* result = SetElem<true>(base, *curMember, value);
                    if (result) {
                      tvRefcountedDecRef(value);
                      value->m_type = KindOfString;
                      value->m_data.pstr = result;
                    }
                  }
                  break;
                }
      case MPL:
      case MPC:
      case MPT: {
                  for (int i = 0; i < multi_num; i++) {
                    if (multi_base) base = (*mstate.base_list)[i];
                    if (multi_value) value = c1->m_data.pmulti->getByVal(i); 
                    if (multi_curMember) curMember = mstate.curMember->m_data.pmulti->getByVal(i);

                    Class* ctx = arGetContextClass(vmfp());
                    // cheng: base can be reference, it will deref below
                    SetProp<true>(ctx, base, *curMember, value);
                  }
                  break;
                }
      case InvalidMemberCode:
                assert(false);
                break;
      }
    } else {
      // Do not support single_base but multi_curMember
      cheng_assert(!multi_curMember);
    // original
    switch (mstate.mcode) {
        case MW:
          SetNewElem<true>(mstate.base, c1);
          break;
        case MEL:
        case MEC:
        case MET:
        case MEI: {
          StringData* result = SetElem<true>(mstate.base, *mstate.curMember, c1);
          if (result) {
            tvRefcountedDecRef(c1);
            c1->m_type = KindOfString;
            c1->m_data.pstr = result;
          }
          break;
        }
        case MPL:
        case MPC:
        case MPT: {
          Class* ctx = arGetContextClass(vmfp());
          SetProp<true>(ctx, mstate.base, *mstate.curMember, c1);
          break;
        }
        case InvalidMemberCode:
          assert(false); break;
      }
  }
  }
  setHelperPost<1>(mstate.ndiscard);
#ifdef CHENG_COUNT_INS
  nested_ins_level_dec();
#endif
}

// Not Impl
OPTBLD_INLINE void iopSetWithRefLM(IOP_ARGS) {
  pc++;
  MemberState mstate;
  // cheng-hack: TODO not impl yet
  mstate.isMultiBase = false;
  mstate.isVGetM = false;
  bool skip = setHelperPre<false, true, false, false, 0,
                       VectorLeaveCode::ConsumeAll>(pc, mstate);
  cheng_assert(mstate.isMultiBase == false); // cheng-hack
  auto local = decode_la(pc);
  if (!skip) {
    TypedValue* from = frame_local(vmfp(), local);
    tvAsVariant(mstate.base).setWithRef(tvAsVariant(from));
  }
  setHelperPost<0>(mstate.ndiscard);
}

// Not Impl
OPTBLD_INLINE void iopSetWithRefRM(IOP_ARGS) {
  pc++;
  MemberState mstate;
  // cheng-hack: TODO not impl yet
  mstate.isMultiBase = false;
  mstate.isVGetM = false;
  bool skip = setHelperPre<false, true, false, false, 1,
                       VectorLeaveCode::ConsumeAll>(pc, mstate);
  cheng_assert(mstate.isMultiBase == false); // cheng-hack
  if (!skip) {
    TypedValue* from = vmStack().top();
    tvAsVariant(mstate.base).setWithRef(tvAsVariant(from));
  }
  setHelperPost<0>(mstate.ndiscard);
  vmStack().popTV();
}

// curtis:
OPTBLD_INLINE void iopSetOpL(IOP_ARGS) {
  AS_SET;
  pc++;
  auto local = decode_la(pc);
  auto op = decode_oa<SetOpOp>(pc);
  Cell* fr = vmStack().topC();
  Cell* to = tvToCell(frame_local(vmfp(), local));

#ifdef CHENG_INS_DEBUG
  auto txt_fr = HHVM_FN(print_r)(tvAsVariant(fr), true);
  auto txt_to = HHVM_FN(print_r)(tvAsVariant(to), true);
  debug_log << "    SetOpL from: {{" << txt_fr.toString().toCppString() << "}}\n"
    << "      to: {{" << txt_to.toString().toCppString() << "}}\n";
#endif

  bool isFrMulti = (fr->m_type == KindOfMulti);
  bool isToMulti = (to->m_type == KindOfMulti);
  
  // Used to be a BUG, since all the multi-value is call-by-ref,
  // in one function "$multi += 1" may change the value outside the function scope
  // do deep-copy before "+="
  if (isToMulti) {
    auto new_to = to->m_data.pmulti->copy();
    tvCopy(new_to, *to);
  }

  if (UNLIKELY(isFrMulti || isToMulti)) {
    START;
    AS_MSET;
    auto fr_multi = isFrMulti ? fr->m_data.pmulti: nullptr;
    auto to_multi = isToMulti ? to->m_data.pmulti: nullptr;

    if (isFrMulti && isToMulti) {
      // (M, M)
#ifdef CHENG_CHECK
      cheng_assert(fr_multi->valSize() == to_multi->valSize());
#endif
      for (int i = 0; i < fr_multi->valSize(); i++) {
        TypedValue *fr_c = fr_multi->getByVal(i);
        TypedValue *to_c = to_multi->getByVal(i);
        SETOP_BODY_CELL(to_c, op, fr_c);
        tvRefcountedDecRef(fr_c);
        cellDup(*to_c, *fr_c);
      }

    } else if (isFrMulti) {
      // (S, M), $str .= $multi
      TypedValue ret = MultiVal::makeMultiVal();
      auto ret_multi = ret.m_data.pmulti;
      for (int i = 0; i < fr_multi->valSize(); i++) {
        TypedValue *fr_c = fr_multi->getByVal(i);
        TypedValue to_c;
        // Once a BUG: the TypedValue will be translated into Variant 
        // which will decrease the ref when it is destructed, so use tvDup instead of tvCopy
        tvDup(*to, to_c); 
        SETOP_BODY_CELL(&to_c, op, fr_c);
        ret_multi->addValue(to_c);
      }
      tvCopy(ret, *to);
      tvRefcountedDecRef(fr);
      cellDup(*to, *fr);
    } else {
      // (M, S), $multi .= $str
      for (int i = 0; i < to_multi->valSize(); i++) {
        TypedValue *to_c = to_multi->getByVal(i);
        SETOP_BODY_CELL(to_c, op, fr);
      }
      tvRefcountedDecRef(fr);
      cellDup(*to, *fr);
    }
    END;
  } else {
    // (S, S)
    SETOP_BODY_CELL(to, op, fr);
    tvRefcountedDecRef(fr);
    cellDup(*to, *fr);
  }
}

// Not Imple
OPTBLD_INLINE void iopSetOpN(IOP_ARGS) {
  AS_SET;
  pc++;
  auto op = decode_oa<SetOpOp>(pc);
  StringData* name;
  Cell* fr = vmStack().topC();
  TypedValue* tv2 = vmStack().indTV(1);
#ifdef CHENG_CHECK
  cheng_assert(fr->m_type != KindOfMulti);
  cheng_assert(tv2->m_type != KindOfMulti);
#endif
  TypedValue* to = nullptr;
  // XXX We're probably not getting warnings totally correct here
  lookupd_var(vmfp(), name, tv2, to);
  assert(to != nullptr);
#ifdef CHENG_CHECK
  cheng_assert(to->m_type != KindOfMulti);
#endif
  SETOP_BODY(to, op, fr);
  tvRefcountedDecRef(fr);
  tvRefcountedDecRef(tv2);
  cellDup(*tvToCell(to), *tv2);
  vmStack().discard();
  decRefStr(name);
}

// Not Impl
OPTBLD_INLINE void iopSetOpG(IOP_ARGS) {
  AS_SET;
  pc++;
  auto op = decode_oa<SetOpOp>(pc);
  StringData* name;
  Cell* fr = vmStack().topC();
  TypedValue* tv2 = vmStack().indTV(1);
#ifdef CHENG_CHECK
  cheng_assert(fr->m_type != KindOfMulti);
  cheng_assert(tv2->m_type != KindOfMulti);
#endif
  TypedValue* to = nullptr;
  // XXX We're probably not getting warnings totally correct here
  lookupd_gbl(vmfp(), name, tv2, to);
  assert(to != nullptr);
#ifdef CHENG_CHECK
  cheng_assert(to->m_type != KindOfMulti);
#endif
  SETOP_BODY(to, op, fr);
  tvRefcountedDecRef(fr);
  tvRefcountedDecRef(tv2);
  cellDup(*tvToCell(to), *tv2);
  vmStack().discard();
  decRefStr(name);
}

// cheng-hack: 
OPTBLD_INLINE void iopSetOpS(IOP_ARGS) {
  AS_SET;
  pc++;
  auto op = decode_oa<SetOpOp>(pc);
  Cell* fr = vmStack().topC();
  TypedValue* classref = vmStack().indTV(1);
  TypedValue* propn = vmStack().indTV(2);
#ifdef CHENG_CHECK
  always_assert(classref->m_type != KindOfMulti);
  always_assert(propn->m_type != KindOfMulti);
#endif
  TypedValue* output = propn;
  StringData* name;
  TypedValue* val;
  bool visible, accessible;
  lookup_sprop(vmfp(), classref, name, propn, val, visible, accessible);
  if (!(visible && accessible)) {
    raise_error("Invalid static property access: %s::%s",
                classref->m_data.pcls->name()->data(),
                name->data());
  }
  // cheng-hack:
  if (UNLIKELY(val->m_type == KindOfMulti || fr->m_type == KindOfMulti)) {
    START;
    AS_MSET;
    TypedValue multi_ret = MultiVal::makeMultiVal();
    bool val_multi = val->m_type == KindOfMulti;
    bool fr_multi = fr->m_type == KindOfMulti;
    int times = val_multi ? val->m_data.pmulti->valSize() : fr->m_data.pmulti->valSize();

#ifdef CHENG_INS_DEBUG
    debug_log << "    val_multi: {" << val_multi << "}, fr_multi: {" << fr_multi << "}\n";
    auto val_txt = HHVM_FN(print_r)(tvAsVariant(val), true);
    auto fr_txt = HHVM_FN(print_r)(tvAsVariant(fr), true);
    debug_log << "    val: {{ " << val_txt.toString().toCppString() << "}}\n"
              << "    fr: {{ " << fr_txt.toString().toCppString() << "}}\n";
#endif

    for (int i = 0; i < times; i++) {
      TypedValue tmp_val, tmp_fr;
      if (val_multi) {
        tvDup(*val->m_data.pmulti->getByVal(i), tmp_val);
      } else {
        tvDup(*val, tmp_val);
      }
      if (fr_multi) {
        tvCopy(*fr->m_data.pmulti->getByVal(i), tmp_fr);
      } else {
        tvCopy(*fr, tmp_fr);
      }
      // Assumption: the following operation wll decref on tmp_val
      SETOP_BODY(&tmp_val, op, &tmp_fr);
      // collect the result
#ifdef CHENG_INS_DEBUG
      auto tmp_val_txt = HHVM_FN(print_r)(tvAsVariant(&tmp_val), true);
      debug_log << "    round[" << i << "/" << times << "] result: " << tmp_val.pretty()
        << "  {{" << tmp_val_txt.toString().toCppString() << "}}\n";
#endif
      multi_ret.m_data.pmulti->addValueNoInc(tmp_val); // no one will decref to tmp_val
    }
    tvRefcountedDecRef(val);
    tvCopy(multi_ret, *val);
    END;
  } else {
  SETOP_BODY(val, op, fr);
  }
  tvRefcountedDecRef(propn);
  tvRefcountedDecRef(fr);
  cellDup(*tvToCell(val), *output);
  vmStack().ndiscard(2);
  decRefStr(name);
}

// Support, same thing as SetM 
// The base->index <op>= value:
//  base  index  value
//   T     -      -     do separately
//   F     T      -     split the array, fail on the obj
//   F     F      T     split the array, assign for the obj 
//   F     F      F     normal
OPTBLD_INLINE void iopSetOpM(IOP_ARGS) {
  AS_MEMBER;
  PC old_pc = pc;
start:
  pc++;
  auto op = decode_oa<SetOpOp>(pc);
  MemberState mstate;
  mstate.isMultiBase = false;
  mstate.isVGetM = false;
  if (!setHelperPre<MoreWarnings, true, false, false, 1,
      VectorLeaveCode::LeaveLast>(pc, mstate)) {

#ifdef CHENG_COUNT_INS
  nested_ins_level_inc();
#endif

    TypedValue* result;
    Cell* rhs = vmStack().topC();

    // cheng-hack: prepare the tmp variables
    TypedValue* base = mstate.base;
    TypedValue* value = rhs;
    TypedValue* curMember = mstate.curMember;
    TypedValue multi_result;
    int multi_num = 1;
    bool multi_base = false, multi_value = false, multi_curMember = false;
    if (UNLIKELY(mstate.isMultiBase)) {
      multi_base = true;
      multi_num = mstate.base_list->size();
    }
    if (UNLIKELY(rhs->m_type == KindOfMulti)) {
      multi_value = true;
      multi_num = rhs->m_data.pmulti->valSize();
    }
    if (UNLIKELY(mstate.mcode != MW && curMember->m_type == KindOfMulti)) {
      multi_curMember = true;
      multi_num = curMember->m_data.pmulti->valSize();
    }
    if (UNLIKELY(multi_base || multi_value || multi_curMember)) {
      multi_result = MultiVal::makeMultiVal();
    }

#ifdef CHENG_CHECK
    if(multi_base) cheng_assert(mstate.base_list->size() == multi_num);
    if(multi_value) cheng_assert(rhs->m_data.pmulti->valSize() == multi_num);
    if(multi_curMember) cheng_assert(mstate.curMember->m_data.pmulti->valSize() == multi_num);
#endif

    if (UNLIKELY(multi_base || multi_value || multi_curMember)) {START; AS_MMEMBER;}

    // FIXME:NOTE: the below snippets are quite similar to SetM, should consider to merge.
    // For the performance reason, leave it like this for now.

    // If the base is single, but the index/value is multi, we need to split
    // Only for array, not for object
    if (UNLIKELY((multi_value || multi_curMember) && !multi_base && 
                 mstate.orig_base->m_type == KindOfArray)) {
      // (S, M)
      TypedValue arr = *mstate.orig_base;
      arr = MultiVal::splitArray(arr, multi_num);
      tvCopy(arr, *mstate.orig_base);
      pc = old_pc;
#ifdef CHENG_INS_DEBUG
      debug_log << "    SetOpM: Single base, and MultiVal: ";
      if (multi_value) debug_log << "      Value: " << rhs->m_data.pmulti->dump("      ");
      if (multi_curMember) {
        //debug_log << "      " << mstate.curMember->pretty() << "\n";
        debug_log << "      Index: " << mstate.curMember->m_data.pmulti->dump("      ");
      }
#endif
      END;
      goto start;
    }

    // For obj-array-set-multi problem:
    // e.g. $obj->arr[0] .= $multi;
    if (UNLIKELY((multi_curMember || multi_value) && !multi_base && 
                 mstate.base->m_type == KindOfArray)) {
#ifdef CHENG_INS_ONLY_DEBUG
      debug_log << "   SetOpM: Split the last level array...\n";
#endif
      // we met a last level array which need to be splited
      auto arr = mstate.base;

      TypedValue split_multi = MultiVal::splitArray(*arr, multi_num);
      tvCopy(split_multi, *arr); // copy back to original place
      multi_base = true;
      // construct base_list
      mstate.base_list = std::make_shared< std::vector<TypedValue*> >();
      for (auto arr_it : *split_multi.m_data.pmulti) {
        mstate.base_list->push_back(arr_it);
      }
    }

    // NOTE: if come here, means:
    //  -- if orig_base/last_level container is array, has been split (multi_base==true)
    //  -- if multi_curMember, must with multi_base
    //  -- if multi_value ONLY, SetOpProp will handle the case
    //  -- normal case: !multi_base && !multi_curMember && !multi_value

    // For multi-ref-one-obj problem:
    // memberHelperPre might return multi_base with refs pointing to one obj.
    // The ref will deref later within the set function.
    // However, we need to detect this ahead
    if (UNLIKELY(multi_base && (*mstate.base_list)[0]->m_type == KindOfRef)
        && !checkStaticEmptyArray((*mstate.base_list)[0])) {
      // check whether all refs point to one slot
      Cell* first_elem = tvToCell((*mstate.base_list)[0]);
      bool point_to_same_slot = true;
      for (int i=1; i<mstate.base_list->size(); i++) {
        if (first_elem->m_data.num !=
            tvToCell((*mstate.base_list)[i])->m_data.num)
        {
          point_to_same_slot = false;
          break;
        }
      }
      // if point to the same slot, do it once
      if (point_to_same_slot) {
        multi_base = false;
        mstate.base = first_elem; // we deref here. Is it OK? seems so.
        cheng_assert(!multi_curMember); // NOTE: do not support multi_curMember here
      }
    }

    // FIXME: do not support single obj and multi_curMember
    if (UNLIKELY(multi_curMember && !multi_base)) {
      cheng_assert(false);
    }

    // The SetOpProp will handle multi_value, so if ONLY multi_value, we do not care
    if (UNLIKELY(multi_value && !multi_base && !multi_curMember)) {
      // only multi_value, !multi_base, !multi_curMember
      // obj->index <op>= multi_value
      // can be run directly which should handled by SetOpProp
      multi_value = false;
      multi_num = 1;
#ifdef CHENG_INS_ONLY_DEBUG 
      debug_log << "    SetOpM set multi_vale=false, and multi_num=1\n"; 
#endif
    }

    for (int i = 0; i < multi_num; i++) {
      if (multi_base) base = (*mstate.base_list)[i];
      if (multi_curMember) curMember = mstate.curMember->m_data.pmulti->getByVal(i);
      if (multi_value) {
        value = rhs->m_data.pmulti->getByVal(i);
        // Used to be a BUG: the ref_multi_array_array_pop_problem 
        tvRefcountedIncRef(value);
      } else {
        // Used to be a BUG: the string might be freed after appending
        tvRefcountedIncRef(value);
      }

#ifdef CHENG_INS_DEBUG
      debug_log << "    SetOpM [" << i << "/" << multi_num <<"]  multi_base:" << multi_base 
        << ", multi_value: " << multi_value << ", multi_member:" << multi_curMember << "\n";
      auto base_txt = HHVM_FN(print_r)(tvAsVariant(base), true);
      auto value_txt = HHVM_FN(print_r)(tvAsVariant(value), true);
      debug_log << "        cur_base: " << base_txt.toString().toCppString() << ", cur_value:"
        << value_txt.toString().toCppString() << "\n";
#endif

      // ASSUMPTION: NOTE: I assume the following will not use scratch/ref
    switch (mstate.mcode) {
      case MW:
        result = SetOpNewElem(mstate.scratch, *mstate.ref.asTypedValue(),
                              op, base, value);
        break;
      case MEL:
      case MEC:
      case MET:
      case MEI:
        result = SetOpElem(mstate.scratch, *mstate.ref.asTypedValue(),
                           op, base, *curMember, value);
        break;
      case MPL:
      case MPC:
      case MPT: {
                  // for object, it is possible that single-obj->multi_value += multi_value;
                  // should be support in SetOpProp()
        Class *ctx = arGetContextClass(vmfp());
        result = SetOpProp(mstate.scratch, *mstate.ref.asTypedValue(),
                           ctx, op, base, *curMember, value);
        break;
      }

      case InvalidMemberCode:
        assert(false);
        result = nullptr; // Silence compiler warning.
        break;
    }

    tvRefcountedDecRef(value);
    // cheng-hack: if this is multivalue, we should make the result multiVal
    if (UNLIKELY(multi_base || multi_value || multi_curMember)) {
      multi_result.m_data.pmulti->addValue(*tvToCell(result));
    }
    }

    if (UNLIKELY(multi_base || multi_value || multi_curMember)) {
      tvCopy(multi_result, *rhs);
      END;
    } else {
      // normal case
      cellDup(*tvToCell(result), *rhs);
    }

#ifdef CHENG_COUNT_INS
    nested_ins_level_dec();
#endif
  }
  setHelperPost<1>(mstate.ndiscard);
}

// Support
OPTBLD_INLINE void iopIncDecL(IOP_ARGS) {
  AS_SET;
  pc++;
  auto local = decode_la(pc);
  auto op = decode_oa<IncDecOp>(pc);
  TypedValue* to = vmStack().allocTV();
  tvWriteUninit(to);
  TypedValue* fr = frame_local(vmfp(), local);
  if (UNLIKELY(fr->m_type == KindOfUninit)) {
    raise_undefined_local(vmfp(), local);
    tvWriteNull(fr);
  } else {
    fr = tvToCell(fr);
  }
  if (UNLIKELY(fr->m_type == KindOfMulti)) {
    START;
    AS_MSET;
    TypedValue multi_ret = MultiVal::makeMultiVal();
    int size = fr->m_data.pmulti->valSize();
    TypedValue tmp;
    tvWriteUninit(&tmp);

    for (int i=0; i<size; i++) {
      IncDecBody<true>(op, fr->m_data.pmulti->getByVal(i), &tmp);
      multi_ret.m_data.pmulti->addValue(tmp);
    }

    tvCopy(multi_ret, *to);
    END;
  } else {
    // normal case
    IncDecBody<true>(op, fr, to);
  }
}

// Support
OPTBLD_INLINE void iopIncDecN(IOP_ARGS) {
  AS_SET;
  pc++;
  auto op = decode_oa<IncDecOp>(pc);
  StringData* name;
  TypedValue* nameCell = vmStack().topTV();
#ifdef CHENG_CHECK
  cheng_assert(nameCell->m_type != KindOfMulti);
#endif
  TypedValue* local = nullptr;
  lookupd_var(vmfp(), name, nameCell, local);
  assert(local != nullptr);

  if (UNLIKELY(tvToCell(local)->m_type == KindOfMulti)) {
    START;
    AS_MSET;
    auto fr = tvToCell(local);
    TypedValue multi_ret = MultiVal::makeMultiVal();
    int size = fr->m_data.pmulti->valSize();
    TypedValue tmp;
    tvWriteUninit(&tmp);

    for (int i=0; i<size; i++) {
      IncDecBody<true>(op, fr->m_data.pmulti->getByVal(i), &tmp);
      multi_ret.m_data.pmulti->addValue(tmp);
    }

    tvCopy(multi_ret, *nameCell);
    END;
  } else {
    IncDecBody<true>(op, tvToCell(local), nameCell);
  }

  decRefStr(name);
}

// Support
OPTBLD_INLINE void iopIncDecG(IOP_ARGS) {
  AS_SET;
  pc++;
  auto op = decode_oa<IncDecOp>(pc);
  StringData* name;
  TypedValue* nameCell = vmStack().topTV();
#ifdef CHENG_CHECK
  cheng_assert(nameCell->m_type != KindOfMulti);
#endif
  TypedValue* gbl = nullptr;
  lookupd_gbl(vmfp(), name, nameCell, gbl);
  assert(gbl != nullptr);
  if (UNLIKELY(tvToCell(gbl)->m_type == KindOfMulti)) {
    START;
    AS_MSET;
    auto fr = tvToCell(gbl);
    TypedValue multi_ret = MultiVal::makeMultiVal();
    int size = fr->m_data.pmulti->valSize();
    TypedValue tmp;
    tvWriteUninit(&tmp);

    for (int i=0; i<size; i++) {
      IncDecBody<true>(op, fr->m_data.pmulti->getByVal(i), &tmp);
      multi_ret.m_data.pmulti->addValue(tmp);
    }

    tvCopy(multi_ret, *nameCell);
    END;
  } else {
    IncDecBody<true>(op, tvToCell(gbl), nameCell);
  }
  decRefStr(name);
}

// Support by IncDecBody 
OPTBLD_INLINE void iopIncDecS(IOP_ARGS) {
  AS_SET;
  pc++;
  SpropState ss;
  spropInit(ss);
  auto op = decode_oa<IncDecOp>(pc);
  if (!(ss.visible && ss.accessible)) {
    raise_error("Invalid static property access: %s::%s",
                ss.clsref->m_data.pcls->name()->data(),
                ss.name->data());
  }
  tvRefcountedDecRef(ss.nameCell);
  if (UNLIKELY(tvToCell(ss.val)->m_type == KindOfMulti)) {
    START;
    AS_MSET;
    auto fr = tvToCell(ss.val);
    TypedValue multi_ret = MultiVal::makeMultiVal();
    int size = fr->m_data.pmulti->valSize();
    TypedValue tmp;
    tvWriteUninit(&tmp);

    for (int i=0; i<size; i++) {
      IncDecBody<true>(op, fr->m_data.pmulti->getByVal(i), &tmp);
      multi_ret.m_data.pmulti->addValue(tmp);
    }

    tvCopy(multi_ret, *ss.output);
    END;
  } else {
    IncDecBody<true>(op, tvToCell(ss.val), ss.output);
  }
  vmStack().discard();
  spropFinish(ss);
}

// Support
OPTBLD_INLINE void iopIncDecM(IOP_ARGS) {
  AS_MEMBER;
  pc++;
  auto op = decode_oa<IncDecOp>(pc);
  MemberState mstate;
  TypedValue multi_result; bool is_multi = false; // cheng-hack 
  TypedValue to = make_tv<KindOfUninit>();
  mstate.isMultiBase = false;
  mstate.isVGetM = false;
  if (!setHelperPre<MoreWarnings, true, false, false, 0,
      VectorLeaveCode::LeaveLast>(pc, mstate)) {
#ifdef CHENG_COUNT_INS
    nested_ins_level_inc();
#endif

    // cheng-hack:
    TypedValue *base = mstate.base;
    TypedValue *curMember = mstate.curMember;
    int multi_num = 1;
    bool multi_base = false, multi_curMember = false;
    if (UNLIKELY(mstate.isMultiBase)) {
      multi_num = mstate.base_list->size();
      multi_base = true;
    }
    if (UNLIKELY(mstate.mcode != MW && mstate.curMember->m_type == KindOfMulti)) {
      multi_num = mstate.curMember->m_data.pmulti->valSize();
      multi_curMember = true;
    }
    if (multi_base || multi_curMember) {
      is_multi = true;
      multi_result = MultiVal::makeMultiVal();
    }

#ifdef CHENG_CHECK
    if(multi_base) cheng_assert(mstate.base_list->size() == multi_num);
    if(multi_curMember) cheng_assert(mstate.curMember->m_data.pmulti->valSize() == multi_num);
#endif

    if (UNLIKELY(multi_base || multi_curMember)) {START; AS_MMEMBER;}

    for (int i = 0; i < multi_num; i++) {
      if (multi_base) base = (*mstate.base_list)[i];
      if (multi_curMember) curMember = mstate.curMember->m_data.pmulti->getByVal(i);

    switch (mstate.mcode) {
      case MW:
        IncDecNewElem<true>(*mstate.ref.asTypedValue(), op, base, to);
        break;
      case MEL:
      case MEC:
      case MET:
      case MEI:
        IncDecElem<true>(*mstate.ref.asTypedValue(), op, base,
                         *curMember, to);
        break;
      case MPL:
      case MPC:
      case MPT: {
        Class* ctx = arGetContextClass(vmfp());
        IncDecProp<true>(ctx, op, base, *curMember, to);
        break;
      }
      case InvalidMemberCode:
        assert(false);
        break;
    }
    // cheng-hack: if multival, collect the result
    if (UNLIKELY(multi_base || multi_curMember)) {
      multi_result.m_data.pmulti->addValue(to);
      END;
    }
    }

#ifdef CHENG_COUNT_INS
    nested_ins_level_dec();
#endif
  }
  setHelperPost<0>(mstate.ndiscard);
  Cell* c1 = vmStack().allocC();
  // cheng-hack: push the correct result to stack
  if (UNLIKELY(is_multi)) {
    memcpy(c1, &multi_result, sizeof(TypedValue));
  } else {
    memcpy(c1, &to, sizeof(TypedValue));
  }
}

// cheng-hack:
static inline
void tvBindMulti(const TypedValue* fr, TypedValue* to) {
  if (UNLIKELY(fr->m_type == KindOfMulti)) {
    START;
    AS_MSET;
    // if the fr is multi-value, it must be multi-ref!
#ifdef CHENG_CHECK
    cheng_assert(fr->m_data.pmulti->getType() == KindOfRef);
#endif
    /* NOTE(1): we have different behavior here compared with tvBind().
     * For tvBind(), it will create a new Ref and increase the 
     * target slot's counter.
     * For us, we share the same multi-ref structure. In that case,
     * no new Refs are created. So far, it seems OK. But not sure
     * if this is a universal truth.
     */
#ifdef CHENG_INS_DEBUG
    debug_log << "  Before BindX:\n    " << to->pretty() << "\n";
#endif
    DataType oldType = to->m_type;
    uint64_t oldDatum = to->m_data.num;
    tvCopy(*fr, *to);
    tvRefcountedDecRefHelper(oldType, oldDatum);
#ifdef CHENG_INS_DEBUG
    debug_log << "  After BindX:\n" << to->m_data.pmulti->dump("    ");
#endif
    END;
  } else {
    tvBind(fr, to);
  }
}

// Support by tvBindMulti()
OPTBLD_INLINE void iopBindL(IOP_ARGS) {
  AS_SET;
  pc++;
  auto local = decode_la(pc);
  Ref* fr = vmStack().topV();
  TypedValue* to = frame_local(vmfp(), local);
  // cheng-hack: used to be tvBind(...)
  //tvBind(fr, to);
  tvBindMulti(fr, to);
}

// Not Impl 
OPTBLD_INLINE void iopBindN(IOP_ARGS) {
  AS_SET;
  pc++;
  StringData* name;
  TypedValue* fr = vmStack().topTV();
  TypedValue* nameTV = vmStack().indTV(1);
#ifdef CHENG_CHECK
  cheng_assert(fr->m_type != KindOfMulti);
  cheng_assert(nameTV->m_type != KindOfMulti);
#endif
  TypedValue* to = nullptr;
  lookupd_var(vmfp(), name, nameTV, to);
  assert(to != nullptr);
#ifdef CHENG_CHECK
  cheng_assert(to->m_type != KindOfMulti);
#endif
  tvBind(fr, to);
  memcpy((void*)nameTV, (void*)fr, sizeof(TypedValue));
  vmStack().discard();
  decRefStr(name);
}

// Not Impl
OPTBLD_INLINE void iopBindG(IOP_ARGS) {
  AS_SET;
  pc++;
  StringData* name;
  TypedValue* fr = vmStack().topTV();
  TypedValue* nameTV = vmStack().indTV(1);
#ifdef CHENG_CHECK
  cheng_assert(fr->m_type != KindOfMulti);
  cheng_assert(nameTV->m_type != KindOfMulti);
#endif
  TypedValue* to = nullptr;
  lookupd_gbl(vmfp(), name, nameTV, to);
  assert(to != nullptr);
#ifdef CHENG_CHECK
  cheng_assert(to->m_type != KindOfMulti);
#endif
  tvBind(fr, to);
  memcpy((void*)nameTV, (void*)fr, sizeof(TypedValue));
  vmStack().discard();
  decRefStr(name);
}

// Not Impl
OPTBLD_INLINE void iopBindS(IOP_ARGS) {
  AS_SET;
  pc++;
  TypedValue* fr = vmStack().topTV();
  TypedValue* classref = vmStack().indTV(1);
  TypedValue* propn = vmStack().indTV(2);
#ifdef CHENG_CHECK
  cheng_assert(fr->m_type != KindOfMulti);
  cheng_assert(classref->m_type != KindOfMulti);
  cheng_assert(propn->m_type != KindOfMulti);
#endif
  TypedValue* output = propn;
  StringData* name;
  TypedValue* val;
  bool visible, accessible;
  lookup_sprop(vmfp(), classref, name, propn, val, visible, accessible);
  if (!(visible && accessible)) {
    raise_error("Invalid static property access: %s::%s",
                classref->m_data.pcls->name()->data(),
                name->data());
  }
  tvBind(fr, val);
  tvRefcountedDecRef(propn);
  memcpy(output, fr, sizeof(TypedValue));
  vmStack().ndiscard(2);
  decRefStr(name);
}

// Not Impl, FIXME: it seems a tricky task:
//      (1) What if you want bind a multi-ref to a single array's element?
//      (2) What if one Ref bind to a multi array? all of the array share one ref? 
OPTBLD_INLINE void iopBindM(IOP_ARGS) {
  AS_MEMBER;
  pc++;
  MemberState mstate;
  // cheng-hack: TODO not impl yet
  // This is a little bit tricky.
  mstate.isMultiBase = false;
  mstate.isVGetM = false;
  TypedValue* tv1 = vmStack().topTV();
  if (!setHelperPre<false, true, false, true, 1,
      VectorLeaveCode::ConsumeAll>(pc, mstate)) {
#ifdef CHENG_COUNT_INS
    nested_ins_level_inc();
#endif
    // Bind the element/property with the var on the top of the stack
    // cheng-hack:
    if (UNLIKELY(mstate.isMultiBase)) {
      START;
      AS_MMEMBER;
      // multi-mulit, no fr(tv1) single; to(mstate.base_list) multi
      // (1) bind $container-multi, $multi-ref
      // (2) bind $container-multi, $ref-multi
      // (3) bind $container-multi, $ref
      if (tv1->m_type == KindOfMulti && tv1->m_data.pmulti->getType() == KindOfRef) {
        cheng_assert(tv1->m_data.pmulti->valSize() == mstate.base_list->size());
        for (int i=0; i<mstate.base_list->size(); i++) {
          tvBind(tv1->m_data.pmulti->getByVal(i), (*mstate.base_list)[i]);
        }
      } else {
        cheng_assert(tv1->m_type == KindOfRef);
        auto fr = tvToCell(tv1);
        if (fr->m_type == KindOfMulti) {
          // case (2)
          if (fr->m_data.pmulti->getType() != KindOfRef) {
            cheng_assert(fr->m_data.pmulti->valSize() == mstate.base_list->size());
            // make it a multi-ref
            tvBoxMulti(fr);
          } // else, fr is already a multi-ref
          // assign to $container-multi
          for (int i=0; i<mstate.base_list->size(); i++) {
            tvBind(fr->m_data.pmulti->getByVal(i), (*mstate.base_list)[i]);
          }
        } else {
          if (/*fr->m_type != KindOfObject &&*/ fr->m_type == KindOfArray) {
            // if it is an array, split it to multi-ref and assign each ref to each element
            int size = mstate.base_list->size();
            auto ret = MultiVal::splitArray(*fr, size);
            tvCopy(ret, *fr); // recover original array
            // make a multi-ref
            tvBoxMulti(fr);
            for (int i=0; i<size; i++) {
              auto ref = fr->m_data.pmulti->getByVal(i);
              tvBind(ref, (*mstate.base_list)[i]);
            }
          } else {
            // it's ok to assign primitive ref to a multi
            // it's also ok to assign the obj to a multi, since obj has multivalue inside. 
            for (int i=0; i<mstate.base_list->size(); i++) {
              tvBind(tv1, (*mstate.base_list)[i]);
            }
          }
        }
      }
      END;
    } else {
      // single, no fr(tv1) multi; to(mstate.base) single
      // FIXME: do not support multi-ref/ref-multi bind to a single base
      // KNOWN-BUG: no guarantee, what if I allow this?
      //cheng_assert(tvToCell(tv1)->m_type != KindOfMulti); // cheng-hack
      tvBind(tv1, mstate.base);
    }
#ifdef CHENG_COUNT_INS
    nested_ins_level_dec();
#endif
  }
  setHelperPost<1>(mstate.ndiscard);
}

// Good to go
OPTBLD_INLINE void iopUnsetL(IOP_ARGS) {
  AS_SET;
  pc++;
  auto local = decode_la(pc);
  assert(local < vmfp()->m_func->numLocals());
  TypedValue* tv = frame_local(vmfp(), local);
  tvRefcountedDecRef(tv);
  // FIXME: should decref inside the multi-val here
  tvWriteUninit(tv);
}

// Good to go
OPTBLD_INLINE void iopUnsetN(IOP_ARGS) {
  AS_SET;
  pc++;
  StringData* name;
  TypedValue* tv1 = vmStack().topTV();
#ifdef CHENG_CHECK
  cheng_assert(tv1->m_type != KindOfMulti);
#endif
  TypedValue* tv = nullptr;
  lookup_var(vmfp(), name, tv1, tv);
  assert(!vmfp()->hasInvName());
  if (tv != nullptr) {
    tvRefcountedDecRef(tv);
    tvWriteUninit(tv);
  }
  vmStack().popC();
  decRefStr(name);
}

// Good to go
OPTBLD_INLINE void iopUnsetG(IOP_ARGS) {
  AS_SET;
  pc++;
  TypedValue* tv1 = vmStack().topTV();
#ifdef CHENG_CHECK
  cheng_assert(tv1->m_type != KindOfMulti);
#endif
  StringData* name = lookup_name(tv1);
  VarEnv* varEnv = g_context->m_globalVarEnv;
  assert(varEnv != nullptr);
  varEnv->unset(name);
  vmStack().popC();
  decRefStr(name);
}

// Support
OPTBLD_INLINE void iopUnsetM(IOP_ARGS) {
  AS_MEMBER;
  pc++;
  MemberState mstate;
  mstate.isMultiBase = false;
  mstate.isVGetM = false;
  if (!setHelperPre<false, false, true, false, 0,
      VectorLeaveCode::LeaveLast>(pc, mstate)) {
#ifdef CHENG_COUNT_INS
    nested_ins_level_inc();
#endif

    // cheng-hack:
    TypedValue *base = mstate.base;
    TypedValue *curMember = mstate.curMember;
    bool multi_base = false, multi_curMember = false;
    int multi_num = 1;
    if (UNLIKELY(mstate.isMultiBase)) {
      multi_num = mstate.base_list->size();
      multi_base = true;
    }
    if (UNLIKELY(mstate.mcode != MW && mstate.curMember->m_type == KindOfMulti)) {
      multi_num = mstate.curMember->m_data.pmulti->valSize();
      multi_curMember = true;
    }

#ifdef CHENG_CHECK
    if(multi_base) cheng_assert(mstate.base_list->size() == multi_num);
    if(multi_curMember) cheng_assert(mstate.curMember->m_data.pmulti->valSize() == multi_num);
#endif

    if (multi_num > 1) {START; AS_MMEMBER;}
    for (int i = 0; i < multi_num; i++) {
      if (multi_base) base = (*mstate.base_list)[i];
      if (multi_curMember) curMember = mstate.curMember->m_data.pmulti->getByVal(i);

    switch (mstate.mcode) {
      case MEL:
      case MEC:
      case MET:
      case MEI:
        UnsetElem(base, *curMember);
        break;
      case MPL:
      case MPC:
      case MPT: {
        Class* ctx = arGetContextClass(vmfp());
        UnsetProp(ctx, base, *curMember);
        break;
      }
      case MW:
      case InvalidMemberCode:
        assert(false);
        break;
    }
    }
    if (multi_num > 1) END;

#ifdef CHENG_COUNT_INS
    nested_ins_level_dec();
#endif
  }
  setHelperPost<0>(mstate.ndiscard);
}

OPTBLD_INLINE ActRec* fPushFuncImpl(const Func* func, int numArgs) {
  DEBUGGER_IF(phpBreakpointEnabled(func->name()->data()));
  ActRec* ar = vmStack().allocA();
  ar->m_func = func;
  ar->initNumArgs(numArgs);
  ar->setVarEnv(nullptr);
  return ar;
}

// Good to go
OPTBLD_INLINE void iopFPushFunc(IOP_ARGS) {
  AS_CALL;
  pc++;
  auto numArgs = decode_iva(pc);
  Cell* c1 = vmStack().topC();
  const Func* func = nullptr;

  // Throughout this function, we save obj/string/array and defer
  // refcounting them until after the stack has been discarded.

  // cheng-hack: may see the multi-lambda, do not support, just fail
  cheng_assert(c1->m_type != KindOfMulti);

  if (IS_STRING_TYPE(c1->m_type)) {
    StringData* origSd = c1->m_data.pstr;
    func = Unit::loadFunc(origSd);
    if (func == nullptr) {
      raise_error("Call to undefined function %s()", c1->m_data.pstr->data());
    }

    vmStack().discard();
    ActRec* ar = fPushFuncImpl(func, numArgs);
    ar->setThisSingle(nullptr);
    decRefStr(origSd);
    return;
  }

  if (c1->m_type == KindOfObject) {
    // this covers both closures and functors
    static StringData* invokeName = makeStaticString("__invoke");
    ObjectData* origObj = c1->m_data.pobj;
    const Class* cls = origObj->getVMClass();
    func = cls->lookupMethod(invokeName);
    if (func == nullptr) {
      raise_error(Strings::FUNCTION_NAME_MUST_BE_STRING);
    }

    vmStack().discard();
    ActRec* ar = fPushFuncImpl(func, numArgs);
    if (func->attrs() & AttrStatic && !func->isClosureBody()) {
      ar->setClass(origObj->getVMClass());
      decRefObj(origObj);
    } else {
      ar->setThisSingle(origObj);
      // Teleport the reference from the destroyed stack cell to the
      // ActRec. Don't try this at home.
    }
    return;
  }

  if (c1->m_type == KindOfArray) {
    // support: array($instance, 'method') and array('Class', 'method')
    // which are both valid callables
    ArrayData* origArr = c1->m_data.parr;
    ObjectData* arrThis = nullptr;
    HPHP::Class* arrCls = nullptr;
    StringData* invName = nullptr;

    func = vm_decode_function(
      tvAsCVarRef(c1),
      vmfp(),
      /* forwarding */ false,
      arrThis,
      arrCls,
      invName,
      /* warn */ false
    );
    if (func == nullptr) {
      raise_error("Invalid callable (array)");
    }
    assert(arrCls != nullptr);

    vmStack().discard();
    ActRec* ar = fPushFuncImpl(func, numArgs);
    if (arrThis) {
      arrThis->incRefCount();
      ar->setThisSingle(arrThis);
    } else {
      ar->setClass(arrCls);
    }
    if (UNLIKELY(invName != nullptr)) {
      ar->setInvName(invName);
    }
    decRefArr(origArr);
    return;
  }

  raise_error(Strings::FUNCTION_NAME_MUST_BE_STRING);
}

// Good to go
OPTBLD_INLINE void iopFPushFuncD(IOP_ARGS) {
  AS_CALL;
  pc++;
  auto numArgs = decode_iva(pc);
  auto id = decode<Id>(pc);
  const NamedEntityPair nep =
    vmfp()->m_func->unit()->lookupNamedEntityPairId(id);
  Func* func = Unit::loadFunc(nep.second, nep.first);
  if (func == nullptr) {
    raise_error("Call to undefined function %s()",
                vmfp()->m_func->unit()->lookupLitstrId(id)->data());
  }
  ActRec* ar = fPushFuncImpl(func, numArgs);
  ar->setThisSingle(nullptr);
}

// Good to go
OPTBLD_INLINE void iopFPushFuncU(IOP_ARGS) {
  AS_CALL;
  pc++;
  auto numArgs = decode_iva(pc);
  auto nsFunc = decode<Id>(pc);
  auto globalFunc = decode<Id>(pc);
  Unit* unit = vmfp()->m_func->unit();
  const NamedEntityPair nep = unit->lookupNamedEntityPairId(nsFunc);
  Func* func = Unit::loadFunc(nep.second, nep.first);
  if (func == nullptr) {
    const NamedEntityPair nep2 = unit->lookupNamedEntityPairId(globalFunc);
    func = Unit::loadFunc(nep2.second, nep2.first);
    if (func == nullptr) {
      const char *funcName = unit->lookupLitstrId(nsFunc)->data();
      raise_error("Call to undefined function %s()", funcName);
    }
  }
  ActRec* ar = fPushFuncImpl(func, numArgs);
  ar->setThisSingle(nullptr);
}

// cheng-hack: 
// used by FPushObjMethod/FPushObjMethodD
void fPushObjMethodImpl(Class* cls, StringData* name, ObjectData* obj,
                        int numArgs,
                        sptr< std::vector<ObjectData*> > multi_obj = nullptr) {
  const Func* f;
  LookupResult res = g_context->lookupObjMethod(f, cls, name,
                                         arGetContextClass(vmfp()), true);
  assert(f);
  ActRec* ar = vmStack().allocA();
  ar->m_func = f;
  if (res == LookupResult::MethodFoundNoThis) {
    // cheng-hack: 
    if (UNLIKELY(obj == nullptr)) {
      // we are in multi mode
      cheng_assert(multi_obj != nullptr);
      for (auto it : *multi_obj) { decRefObj(it); }
    } else {
      // normal case
    decRefObj(obj);
    }
    ar->setClass(cls);
  } else {
    assert(res == LookupResult::MethodFoundWithThis ||
           res == LookupResult::MagicCallFound);
    /* Transfer ownership of obj to the ActRec*/
    // cheng-hack: decide whether is multi-this mode
    if (UNLIKELY(obj == nullptr)) {
      ar->setThisMulti(multi_obj);
    } else {
      // normal case
    ar->setThisSingle(obj);
    }
  }
  // chneg-hack:
  // NOTE: take care here, the initNumArgs will flush the multiThis bit
  // Here is the ONLY point, we push a multi-this ActRec!!
  if (UNLIKELY(obj==nullptr)) {
    ar->initNumArgsFromMultiThis(numArgs);
  } else {
    // normal case
  ar->initNumArgs(numArgs);
  }
  if (res == LookupResult::MagicCallFound) {
    ar->setInvName(name);
  } else {
    ar->setVarEnv(nullptr);
    decRefStr(name);
  }
}

void fPushNullObjMethod(int numArgs) {
  assert(SystemLib::s_nullFunc);
  ActRec* ar = vmStack().allocA();
  ar->m_func = SystemLib::s_nullFunc;
  ar->setThisSingle(nullptr);
  ar->initNumArgs(numArgs);
  ar->setVarEnv(nullptr);
}

static void throw_call_non_object(const char* methodName,
                                  const char* typeName = nullptr) {
  std::string msg;
  folly::format(&msg, "Call to a member function {}() on a non-object ({})",
    methodName, typeName);

  if (RuntimeOption::ThrowExceptionOnBadMethodCall) {
    Object e(SystemLib::AllocBadMethodCallExceptionObject(String(msg)));
    throw e;
  }
  throw FatalErrorException(msg.c_str());
}

// Support by fPushObjMethodImpl()
//   Basically, we should check if this is multi-this
OPTBLD_INLINE void iopFPushObjMethod(IOP_ARGS) {
  AS_CALL;
  pc++;
  auto numArgs = decode_iva(pc);
  auto op = decode_oa<ObjMethodOp>(pc);
  Cell* c1 = vmStack().topC(); // Method name.
  if (!IS_STRING_TYPE(c1->m_type)) {
    raise_error(Strings::METHOD_NAME_MUST_BE_STRING);
  }
  Cell* c2 = vmStack().indC(1); // Object.

  // cheng-hack:
  // It doesn't make sense that method name is a multiVal
  cheng_assert(c1->m_type != KindOfMulti);
  if (UNLIKELY(c2->m_type != KindOfObject && c2->m_type != KindOfMulti)) {
    if (UNLIKELY(op == ObjMethodOp::NullThrows || !IS_NULL_TYPE(c2->m_type))) {
      throw_call_non_object(c1->m_data.pstr->data(),
                            getDataTypeString(c2->m_type).get()->data());
    }
    vmStack().popC();
    vmStack().popC();
    fPushNullObjMethod(numArgs);
    return;
  }

  // cheng-hack: check if the value is obj and blong to one class
  if (UNLIKELY(c2->m_type == KindOfMulti)) {
    START;
    AS_MCALL;
    cheng_assert(c2->m_data.pmulti->getType() == KindOfObject);

    // check if the same obj
    auto single = c2->m_data.pmulti->shrinkToSingle();
    if (single != nullptr) {
      ObjectData* obj = single->m_data.pobj;
      Class* cls = obj->getVMClass();
      StringData* name = c1->m_data.pstr;
      // We handle decReffing obj and name in fPushObjMethodImpl
      vmStack().ndiscard(2);
      // safety check
      cheng_assert(cls != nullptr && name != nullptr);
      fPushObjMethodImpl(cls, name, obj, numArgs);
    } else {
      Class* cls = nullptr;
      for (auto it : *c2->m_data.pmulti) {
        if (cls == nullptr) {
          cls = it->m_data.pobj->getVMClass();
        } else {
          cheng_assert(it->m_data.pobj->getVMClass() == cls);
        }
      }
      // construct multi $this
      sptr< std::vector<ObjectData*> > multi_obj = genMultiObj(c2->m_data.pmulti);
      // do real work
      vmStack().ndiscard(2);
      StringData* name = c1->m_data.pstr;
      // safety check
      cheng_assert(cls != nullptr && name != nullptr);
      fPushObjMethodImpl(cls, name, nullptr, numArgs, multi_obj);
    }
    END;
  } else {
    // normal case
  ObjectData* obj = c2->m_data.pobj;
  Class* cls = obj->getVMClass();
  StringData* name = c1->m_data.pstr;
  // We handle decReffing obj and name in fPushObjMethodImpl
  vmStack().ndiscard(2);
  fPushObjMethodImpl(cls, name, obj, numArgs);
  }
}

// Support by fPushObjMethodImpl()
//   Basically, we should check if this is multi-this
OPTBLD_INLINE void iopFPushObjMethodD(IOP_ARGS) {
  AS_CALL;
  pc++;
  auto numArgs = decode_iva(pc);
  auto name = decode_litstr(pc); // function name
  auto op = decode_oa<ObjMethodOp>(pc);
  Cell* c1 = vmStack().topC(); // object
  // cheng-hack:
  if (c1->m_type != KindOfObject && c1->m_type != KindOfMulti) {
    if (UNLIKELY(op == ObjMethodOp::NullThrows || !IS_NULL_TYPE(c1->m_type))) {
      throw_call_non_object(name->data(),
                            getDataTypeString(c1->m_type).get()->data());
    }
    vmStack().popC();
    fPushNullObjMethod(numArgs);
    return;
  }

  // cheng-hack:
  if (UNLIKELY(c1->m_type == KindOfMulti)) {
    START;
    AS_MCALL;
    // FIXME: this should be fix by other iops
    if (c1->m_data.pmulti->getType() == KindOfRef) {
      *c1 = tvMayMultiToCell(c1);
    }

    cheng_assert(c1->m_data.pmulti->getType() == KindOfObject);

    // check if the same obj
    // cheng-hack: used to be a BUG. Since the RetC will decref the obj (the incref happen
    // during CGetL, but multi-ref/multi-val will not incref), there will be segfault
    // incref here.
    auto single = c1->m_data.pmulti->shrinkToSingle();
    if (single != nullptr) {
      // normal case
      ObjectData* obj = single->m_data.pobj;
      // cheng-hack: incref here, to compensate the decref in RetC 
      obj->incRefCount();
      Class* cls = obj->getVMClass();
      // We handle decReffing obj in fPushObjMethodImpl
      vmStack().popC();
      fPushObjMethodImpl(cls, name, obj, numArgs);
    } else {
      // check all the objs belongs to one class
      Class* cls = nullptr;
      for (auto it : *c1->m_data.pmulti) {
        if (cls == nullptr) {
          cls = it->m_data.pobj->getVMClass();
        } else {
          cheng_assert(it->m_data.pobj->getVMClass() == cls);
        }
      }
      // construct multi $this, this **increase** the counter for the object
      sptr< std::vector<ObjectData*> > multi_obj = genMultiObj(c1->m_data.pmulti);
      // [We handle decReffing obj in fPushObjMethodImpl]:
      // this is for ref of obj which is increased in genMultiObj()
      // Here we decrease the ref for multi-value:
      vmStack().popC();
      // safety check
      cheng_assert(cls != nullptr && name != nullptr);
      fPushObjMethodImpl(cls, name, nullptr, numArgs, multi_obj);
    }
    END;
  } else {
    // normal case
  ObjectData* obj = c1->m_data.pobj;
  Class* cls = obj->getVMClass();
  // We handle decReffing obj in fPushObjMethodImpl
  vmStack().discard();
  fPushObjMethodImpl(cls, name, obj, numArgs);
  }
}

template<bool forwarding>
void pushClsMethodImpl(Class* cls, StringData* name, ObjectData* obj,
                       int numArgs) {
  const Func* f;
  LookupResult res = g_context->lookupClsMethod(f, cls, name, obj,
                                     arGetContextClass(vmfp()), true);
  if (res == LookupResult::MethodFoundNoThis ||
      res == LookupResult::MagicCallStaticFound) {
    obj = nullptr;
  } else {
    assert(obj);
    assert(res == LookupResult::MethodFoundWithThis ||
           res == LookupResult::MagicCallFound);
    obj->incRefCount();
  }
  assert(f);
  ActRec* ar = vmStack().allocA();
  ar->m_func = f;
  if (obj) {
    ar->setThisSingle(obj);
  } else {
    if (!forwarding) {
      ar->setClass(cls);
    } else {
      /* Propagate the current late bound class if there is one, */
      /* otherwise use the class given by this instruction's input */
      if (vmfp()->hasThis()) {
        // cheng-hack:
        cls = vmfp()->getThisDefault()->getVMClass();
      } else if (vmfp()->hasClass()) {
        cls = vmfp()->getClass();
      }
      ar->setClass(cls);
    }
  }
  ar->initNumArgs(numArgs);
  if (res == LookupResult::MagicCallFound ||
      res == LookupResult::MagicCallStaticFound) {
    ar->setInvName(name);
  } else {
    ar->setVarEnv(nullptr);
    decRefStr(const_cast<StringData*>(name));
  }
}

// Good to go
OPTBLD_INLINE void iopFPushClsMethod(IOP_ARGS) {
  AS_CALL;
  pc++;
  auto numArgs = decode_iva(pc);
  Cell* c1 = vmStack().indC(1); // Method name.
  if (!IS_STRING_TYPE(c1->m_type)) {
    raise_error(Strings::FUNCTION_NAME_MUST_BE_STRING);
  }
  // cheng-hack: multiVal doesn't make sense
  cheng_assert(c1->m_type != KindOfMulti);
  TypedValue* tv = vmStack().top();
  assert(tv->m_type == KindOfClass);
  Class* cls = tv->m_data.pcls;
  StringData* name = c1->m_data.pstr;
  // pushClsMethodImpl will take care of decReffing name
  vmStack().ndiscard(2);
  assert(cls && name);
#ifdef CHENG_CHECK
  if (vmfp()->hasThis() && vmfp()->isMultiThis()) {
    START;END; // just for counting the #multi_ins
    AS_MCALL;
  }
#endif
  // cheng-hack: so far, it seems that just give a nullptr is OK
  ObjectData* obj = (vmfp()->hasThis() && !vmfp()->isMultiThis()) ?
    vmfp()->getThisSingle() : nullptr;
  pushClsMethodImpl<false>(cls, name, obj, numArgs);
}

// Good to go
OPTBLD_INLINE void iopFPushClsMethodD(IOP_ARGS) {
  AS_CALL;
  pc++;
  auto numArgs = decode_iva(pc);
  auto name = decode_litstr(pc);
  auto classId = decode<Id>(pc);
  const NamedEntityPair &nep =
    vmfp()->m_func->unit()->lookupNamedEntityPairId(classId);
  Class* cls = Unit::loadClass(nep.second, nep.first);
  if (cls == nullptr) {
    raise_error(Strings::UNKNOWN_CLASS, nep.first->data());
  }
#ifdef CHENG_CHECK
  if (vmfp()->hasThis() && vmfp()->isMultiThis()) {
    START;END; // just for counting the #multi_ins
    AS_MCALL;
  }
#endif
  // cheng-hack: so far, it seems that just give a nullptr is OK
  ObjectData* obj = (vmfp()->hasThis() && !vmfp()->isMultiThis()) ?
    vmfp()->getThisSingle() : nullptr;
  pushClsMethodImpl<false>(cls, name, obj, numArgs);
}

// Good to go
OPTBLD_INLINE void iopFPushClsMethodF(IOP_ARGS) {
  AS_CALL;
  pc++;
  auto numArgs = decode_iva(pc);
  Cell* c1 = vmStack().indC(1); // Method name.
  if (!IS_STRING_TYPE(c1->m_type)) {
    raise_error(Strings::FUNCTION_NAME_MUST_BE_STRING);
  }
  TypedValue* tv = vmStack().top();
  assert(tv->m_type == KindOfClass);
  Class* cls = tv->m_data.pcls;
  assert(cls);
  StringData* name = c1->m_data.pstr;
  // pushClsMethodImpl will take care of decReffing name
  vmStack().ndiscard(2);
#ifdef CHENG_CHECK
  if (vmfp()->hasThis() && vmfp()->isMultiThis()) {
    START;END; // just for counting the #multi_ins
    AS_MCALL;
  }
#endif
  // cheng-hack: so far, it seems that just give a nullptr is OK
  ObjectData* obj = (vmfp()->hasThis() && !vmfp()->isMultiThis()) ?
    vmfp()->getThisSingle() : nullptr;
  pushClsMethodImpl<true>(cls, name, obj, numArgs);
}

// Good to go
OPTBLD_INLINE void iopFPushCtor(IOP_ARGS) {
  AS_CALL;
  pc++;
  auto numArgs = decode_iva(pc);
  TypedValue* tv = vmStack().topTV();
  cheng_assert(tv->m_type == KindOfClass);
  Class* cls = tv->m_data.pcls;
  assert(cls != nullptr);
#ifdef CHENG_INS_DEBUG
  debug_log << "    new class[" << cls->name()->toCppString() << "]\n";
#endif
  if (UNLIKELY(isBuiltinClass(cls->name()->toCppString()))) {
    builtin_class_new = true; 
  }
  // Lookup the ctor
  const Func* f;
  LookupResult res UNUSED = g_context->lookupCtorMethod(f, cls, true);
  assert(res == LookupResult::MethodFoundWithThis);
  // Replace input with uninitialized instance.
  ObjectData* this_ = newInstance(cls);
  TRACE(2, "FPushCtor: just new'ed an instance of class %s: %p\n",
        cls->name()->data(), this_);
  this_->incRefCount();
  this_->incRefCount();
  tv->m_type = KindOfObject;
  tv->m_data.pobj = this_;
  // Push new activation record.
  ActRec* ar = vmStack().allocA();
  ar->m_func = f;
  ar->setThisSingle(this_);
  ar->initNumArgsFromFPushCtor(numArgs);
  ar->setVarEnv(nullptr);
}

// Good to go
OPTBLD_INLINE void iopFPushCtorD(IOP_ARGS) {
  AS_CALL;
  pc++;
  auto numArgs = decode_iva(pc);
  auto id = decode<Id>(pc);
  const NamedEntityPair &nep =
    vmfp()->m_func->unit()->lookupNamedEntityPairId(id);
  Class* cls = Unit::loadClass(nep.second, nep.first);
  if (cls == nullptr) {
    raise_error(Strings::UNKNOWN_CLASS,
                vmfp()->m_func->unit()->lookupLitstrId(id)->data());
  }
#ifdef CHENG_INS_DEBUG
  debug_log << "    new class[" << cls->name()->toCppString() << "]\n";
#endif
  if (UNLIKELY(isBuiltinClass(cls->name()->toCppString()))) {
    builtin_class_new = true; 
  }
  // Lookup the ctor
  const Func* f;
  LookupResult res UNUSED = g_context->lookupCtorMethod(f, cls, true);
  assert(res == LookupResult::MethodFoundWithThis);
  // Push uninitialized instance.
  ObjectData* this_ = newInstance(cls);
  TRACE(2, "FPushCtorD: new'ed an instance of class %s: %p\n",
        cls->name()->data(), this_);
  this_->incRefCount();
  vmStack().pushObject(this_);
  // Push new activation record.
  ActRec* ar = vmStack().allocA();
  ar->m_func = f;
  ar->setThisSingle(this_);
  ar->initNumArgsFromFPushCtor(numArgs);
  ar->setVarEnv(nullptr);
}

// Good to go
OPTBLD_INLINE void iopDecodeCufIter(IOP_ARGS) {
  AS_CALL;
  PC origPc = pc;
  pc++;
  auto itId = decode_ia(pc);
  auto offset = decode<Offset>(pc);

  Iter* it = frame_iter(vmfp(), itId);
  CufIter &cit = it->cuf();

  ObjectData* obj = nullptr;
  HPHP::Class* cls = nullptr;
  StringData* invName = nullptr;
  TypedValue *func = vmStack().topTV();

#ifdef CHENG_CHECK
  cheng_assert(func->m_type != KindOfMulti);
#endif

  ActRec* ar = vmfp();
  if (vmfp()->m_func->isBuiltin()) {
    ar = g_context->getOuterVMFrame(ar);
  }
  const Func* f = vm_decode_function(tvAsVariant(func),
                                     ar, false,
                                     obj, cls, invName,
                                     false);

  if (f == nullptr) {
    pc = origPc + offset;
  } else {
    cit.setFunc(f);
    if (obj) {
      cit.setCtx(obj);
      obj->incRefCount();
    } else {
      cit.setCtx(cls);
    }
    cit.setName(invName);
  }
  vmStack().popC();
}

// Good to go
OPTBLD_INLINE void iopFPushCufIter(IOP_ARGS) {
  AS_CALL;
  pc++;
  auto numArgs = decode_iva(pc);
  auto itId = decode_ia(pc);

  Iter* it = frame_iter(vmfp(), itId);

  auto f = it->cuf().func();
  auto o = it->cuf().ctx();
  auto n = it->cuf().name();

  ActRec* ar = vmStack().allocA();
  ar->m_func = f;
  ar->m_this = (ObjectData*)o;
  if (o && !(uintptr_t(o) & 1)) ar->m_this->incRefCount();
  if (n) {
    ar->setInvName(n);
    n->incRefCount();
  } else {
    ar->setVarEnv(nullptr);
  }
  ar->initNumArgs(numArgs);
}

// Used by FPushCuf/FPushCufF/FpushCufSafe
OPTBLD_INLINE void doFPushCuf(PC& pc, bool forward, bool safe) {
  pc++;
  auto numArgs = decode_iva(pc);

  TypedValue func = vmStack().topTV()[safe];

  ObjectData* obj = nullptr;
  HPHP::Class* cls = nullptr;
  StringData* invName = nullptr;

  const Func* f;

  // cheng-hack: support multi-callback
  bool no_obj = false;
  sptr< std::vector<ObjectData*> >  multi_obj =
               std::make_shared< std::vector<ObjectData*> >();
  if (UNLIKELY(func.m_type == KindOfMulti)) {
    START;
    AS_MCALL;
    ObjectData* t_obj = nullptr;
    HPHP::Class* t_cls = nullptr;
    StringData* t_invName = nullptr;

    for (auto fit : *func.m_data.pmulti) {

      const Func* tmp_f = vm_decode_function(tvAsVariant(fit), vmfp(),
                             forward, t_obj, t_cls, t_invName, !safe);
      if (cls == nullptr) {
        cls = t_cls;
        f = tmp_f;
        invName = t_invName; // TODO: I don't know what is this!
        no_obj = t_obj == nullptr ? true : false;
      }
      cheng_assert(cls == t_cls);
      cheng_assert(f == tmp_f);
      cheng_assert(invName == t_invName);
      if (no_obj) { 
        cheng_assert(t_obj == nullptr);
      } else {
        cheng_assert(t_obj != nullptr);
        multi_obj->push_back(t_obj);
        t_obj->incRefCount();
        obj = t_obj; // make the latter condition happy
      }
    }
    END;
  } else {

  f = vm_decode_function(tvAsVariant(&func), vmfp(),
                                     forward,
                                     obj, cls, invName,
                                     !safe);
  }

  if (safe) vmStack().topTV()[1] = vmStack().topTV()[0];
  vmStack().ndiscard(1);
  if (f == nullptr) {
    f = SystemLib::s_nullFunc;
    if (safe) {
      vmStack().pushFalse();
    }
  } else if (safe) {
    vmStack().pushTrue();
  }

  ActRec* ar = vmStack().allocA();
  ar->m_func = f;
  if (obj) {
    // cheng-hack:
    if (UNLIKELY(func.m_type == KindOfMulti)) {
      ar->setThisMulti(multi_obj);
#ifdef CHENG_INS_DEBUG
      debug_log << "    FPushCuf setThisMulti\n";
#endif
    } else {
    ar->setThisSingle(obj);
    obj->incRefCount();
    }
  } else if (cls) {
    ar->setClass(cls);
  } else {
    ar->setThisSingle(nullptr);
  }
  // cheng-hack:
  if (UNLIKELY(func.m_type == KindOfMulti)) {
    ar->initNumArgsFromMultiThis(numArgs);
  } else {
    ar->initNumArgs(numArgs);
  }
  if (invName) {
    ar->setInvName(invName);
  } else {
    ar->setVarEnv(nullptr);
  }
  tvRefcountedDecRef(&func);
}

// Good to go
OPTBLD_INLINE void iopFPushCuf(IOP_ARGS) {
  AS_CALL;
  doFPushCuf(pc, false, false);
}

// Good to go
OPTBLD_INLINE void iopFPushCufF(IOP_ARGS) {
  AS_CALL;
  doFPushCuf(pc, true, false);
}

// Good to go
OPTBLD_INLINE void iopFPushCufSafe(IOP_ARGS) {
  AS_CALL;
  doFPushCuf(pc, false, true);
}

static inline ActRec* arFromInstr(TypedValue* sp, const Op* pc) {
  return arFromSpOffset((ActRec*)sp, instrSpToArDelta(pc));
}

// Good to go
OPTBLD_INLINE void iopFPassC(IOP_ARGS) {
  AS_GET;
  DEBUG_ONLY auto const ar = arFromInstr(vmStack().top(), (Op*)pc);
  pc++;
  UNUSED auto paramId = decode_iva(pc);
  assert(paramId < ar->numArgs());
}

// Good to go
OPTBLD_INLINE void iopFPassCW(IOP_ARGS) {
  AS_GET;
  auto const ar = arFromInstr(vmStack().top(), reinterpret_cast<const Op*>(pc));
  pc++;
  auto paramId = decode_iva(pc);
  assert(paramId < ar->numArgs());
  auto const func = ar->m_func;
  if (func->mustBeRef(paramId)) {
    raise_strict_warning("Only variables should be passed by reference");
  }
}

// Good to go
OPTBLD_INLINE void iopFPassCE(IOP_ARGS) {
  AS_GET;
  auto const ar = arFromInstr(vmStack().top(), reinterpret_cast<const Op*>(pc));
  pc++;
  auto paramId = decode_iva(pc);
  assert(paramId < ar->numArgs());
  auto const func = ar->m_func;
  if (func->mustBeRef(paramId)) {
    raise_error("Cannot pass parameter %d by reference", paramId+1);
  }
}

// Good to go
OPTBLD_INLINE void iopFPassV(IOP_ARGS) {
  AS_GET;
  ActRec* ar = arFromInstr(vmStack().top(), (Op*)pc);
  pc++;
  auto paramId = decode_iva(pc);
  assert(paramId < ar->numArgs());
  const Func* func = ar->m_func;
  if (!func->byRef(paramId)) {
    // cheng-hack:
    if (UNLIKELY(vmStack().topTV()->m_type == KindOfMulti)) {
      TypedValue* top = vmStack().topTV();
#ifdef CHENG_CHECK
      cheng_assert(top->m_data.pmulti->getType() == KindOfRef);
#endif
      unboxMulti(top);
    } else {
      // normal case
      vmStack().unbox();
    }
  }
}

// Good to go
//  DO NOT KNOW: Can be multi-ref?
OPTBLD_INLINE void iopFPassVNop(IOP_ARGS) {
  AS_GET;
  DEBUG_ONLY auto const ar = arFromInstr(vmStack().top(), (Op*)pc);
  pc++;
  UNUSED auto paramId = decode_iva(pc);
  assert(paramId < ar->numArgs());
  assert(ar->m_func->byRef(paramId));
}

// Good to go
OPTBLD_INLINE void iopFPassR(IOP_ARGS) {
  AS_GET;
  ActRec* ar = arFromInstr(vmStack().top(), (Op*)pc);
  pc++;
  auto paramId = decode_iva(pc);
  assert(paramId < ar->numArgs());
  const Func* func = ar->m_func;
  if (func->byRef(paramId)) {
    TypedValue* tv = vmStack().topTV();
    if (tv->m_type != KindOfRef) {
      if (UNLIKELY(tv->m_type == KindOfMulti)) {
        tvBoxMulti(tv);
      } else {
        tvBox(tv);
      }
    }
  } else {
    // cheng-hack:
    if (UNLIKELY(vmStack().topTV()->m_type == KindOfMulti)) {
      TypedValue* mTv = vmStack().topTV();
      if (mTv->m_data.pmulti->getType() == KindOfRef) {
        unboxMulti(mTv);
      }
    }
    if (vmStack().topTV()->m_type == KindOfRef) {
      vmStack().unbox();
    }
  }
}

// Supported by cgetl_inner_body()
OPTBLD_INLINE void iopFPassL(IOP_ARGS) {
  AS_GET;
  ActRec* ar = arFromInstr(vmStack().top(), (Op*)pc);
  pc++;
  auto paramId = decode_iva(pc);
  auto local = decode_la(pc);
  assert(paramId < ar->numArgs());
  TypedValue* fr = frame_local(vmfp(), local);
  TypedValue* to = vmStack().allocTV();
  if (!ar->m_func->byRef(paramId)) {
    cgetl_body(vmfp(), fr, to, local);
  } else {
    vgetl_body(fr, to);
  }
}

// Use CGetN 
OPTBLD_INLINE void iopFPassN(IOP_ARGS) {
  ActRec* ar = arFromInstr(vmStack().top(), (Op*)pc);
  PC origPc = pc;
  pc++;
  auto paramId = decode_iva(pc);
  assert(paramId < ar->numArgs());
  if (!ar->m_func->byRef(paramId)) {
    iopCGetN(origPc);
  } else {
    iopVGetN(origPc);
  }
}

// Use CGetG
OPTBLD_INLINE void iopFPassG(IOP_ARGS) {
  ActRec* ar = arFromInstr(vmStack().top(), (Op*)pc);
  PC origPc = pc;
  pc++;
  auto paramId = decode_iva(pc);
  assert(paramId < ar->numArgs());
  if (!ar->m_func->byRef(paramId)) {
    iopCGetG(origPc);
  } else {
    iopVGetG(origPc);
  }
}

// Use CGetS
OPTBLD_INLINE void iopFPassS(IOP_ARGS) {
  ActRec* ar = arFromInstr(vmStack().top(), (Op*)pc);
  PC origPc = pc;
  pc++;
  auto paramId = decode_iva(pc);
  assert(paramId < ar->numArgs());
  if (!ar->m_func->byRef(paramId)) {
    iopCGetS(origPc);
  } else {
    iopVGetS(origPc);
  }
}

// Supported
OPTBLD_INLINE void iopFPassM(IOP_ARGS) {
  AS_MEMBER;
  ActRec* ar = arFromInstr(vmStack().top(), (Op*)pc);
  pc++;
  auto paramId = decode_iva(pc);
  assert(paramId < ar->numArgs());
#ifdef CHENG_COUNT_INS
  nested_ins_level_inc();
#endif
  if (!ar->m_func->byRef(paramId)) {
    MemberState mstate;
    auto tvRet = getHelper(pc, mstate);
    // cheng-hack: This is good to go, since the getHelper will
    //             do the unbox for multi-ref
    if (tvRet->m_type == KindOfRef) {
      tvUnbox(tvRet);
    }
  } else {
    MemberState mstate;
    // cheng-hack: 
    // if we got multi-base/multi-index,
    // we should make the multi-ref here
    mstate.isMultiBase = false;
    mstate.isVGetM = false;
    TypedValue* tv1 = vmStack().allocTV();
    tvWriteUninit(tv1);
    if (!setHelperPre<false, true, false, true, 1,
        VectorLeaveCode::ConsumeAll>(pc, mstate)) {
      // cheng-hack:
      if (UNLIKELY(mstate.isMultiBase)) {
        TypedValue ret = MultiVal::makeMultiVal();
        for (auto it : *mstate.base_list) {
          if (it->m_type != KindOfRef) {
            tvBox(it);
          }
          ret.m_data.pmulti->addValue(*it);
        }
#ifdef CHENG_CHECK
        cheng_assert(ret.m_data.pmulti->getType() == KindOfRef);
#endif
        tvCopy(ret, *tv1);
      } else {
        // normal case
      if (mstate.base->m_type != KindOfRef) {
        tvBox(mstate.base);
      }
      refDup(*mstate.base, *tv1);
      }
    } else {
      tvWriteNull(tv1);
      tvBox(tv1);
    }
    setHelperPost<1>(mstate.ndiscard);
  }
#ifdef CHENG_COUNT_INS
  nested_ins_level_dec();
#endif
}

bool doFCall(ActRec* ar, PC& pc) {
  TRACE(3, "FCall: pc %p func %p base %d\n", vmpc(),
        vmfp()->m_func->unit()->entry(),
        int(vmfp()->m_func->base()));
  prepareFuncEntry(ar, pc, StackArgsState::Untrimmed);
  vmpc() = pc;
  if (EventHook::FunctionCall(ar, EventHook::NormalFunc)) return true;
  pc = vmpc();
  return false;
}

// Good to go
OPTBLD_INLINE void iopFCall(IOP_ARGS) {
  AS_CALL;
  ActRec* ar = arFromInstr(vmStack().top(), (Op*)pc);
  pc++;
  /*UNUSED*/ auto numArgs = decode_iva(pc);
  // cheng-hack: if the builtin_class_new is true, which means POINT2 might be the case
  // (1) check all the arguments, if there is any multival, do object split
  // (2) if split, replace the this object on stack to multi_this
  if (UNLIKELY(builtin_class_new)) {
    int multi_size = 0;
    TypedValue* rargs = vmStack().topTV();
    for (int i = 0; i < numArgs; i ++) {
      if (UNLIKELY(rargs[i].m_type == KindOfMulti)) {
        multi_size = rargs[i].m_data.pmulti->valSize(); break;
      }
    }
    if (multi_size != 0) {
      cheng_assert(ar->hasThis());
      // split object 
      sptr< std::vector<ObjectData*> > multi_this_ = 
               std::make_shared< std::vector<ObjectData*> >();
      auto obj = ar->getThisSingle();
      multi_this_->push_back(obj);
      for (int i=1; i < multi_size; i++) {
        ObjectData* clone = newInstance(obj->getVMClass());
        multi_this_->push_back(clone); 
      }
      cheng_assert(multi_this_->size() == multi_size);
      ar->setThisMulti(multi_this_);
      // replace this on stack
      TypedValue tv = genMultiVal(multi_this_);
      auto this_ptr = rargs + numArgs + 3 /*sizeof frame*/;
      cheng_assert(this_ptr->m_type == KindOfObject);
      tvCopy(tv, *this_ptr);
    }
  }
  builtin_class_new = false;

  assert(numArgs == ar->numArgs());
  checkStack(vmStack(), ar->m_func, 0);
  ar->setReturn(vmfp(), pc, mcg->tx().uniqueStubs.retHelper);
  doFCall(ar, pc);
}

// Good to go
OPTBLD_INLINE void iopFCallD(IOP_ARGS) {
  AS_CALL;
  auto const ar = arFromInstr(vmStack().top(), reinterpret_cast<const Op*>(pc));
  pc++;
  UNUSED auto numArgs = decode_iva(pc);
  UNUSED auto clsName = decode_litstr(pc);
  UNUSED auto funcName = decode_litstr(pc);
  if (!RuntimeOption::EvalJitEnableRenameFunction &&
      !(ar->m_func->attrs() & AttrInterceptable)) {
    assert(ar->m_func->name()->isame(funcName));
  }
  assert(numArgs == ar->numArgs());
  checkStack(vmStack(), ar->m_func, 0);
  ar->setReturn(vmfp(), pc, mcg->tx().uniqueStubs.retHelper);
  doFCall(ar, pc);
}

// Support
// FIXME: not handling when "this" is multivalue in a builtin method
OPTBLD_INLINE void iopFCallBuiltin(IOP_ARGS) {
  AS_CALL;
  pc++;
  auto numArgs = decode_iva(pc);
  auto numNonDefault = decode_iva(pc);
  auto id = decode<Id>(pc);
  const NamedEntity* ne = vmfp()->m_func->unit()->lookupNamedEntityId(id);
  Func* func = Unit::lookupFunc(ne);
  if (func == nullptr) {
    raise_error("Call to undefined function %s()",
                vmfp()->m_func->unit()->lookupLitstrId(id)->data());
  }
  TypedValue* args = vmStack().indTV(numArgs-1);
  TypedValue ret;

#ifdef CHENG_INS_ONLY_DEBUG
  if (should_count && func->name() && func->name()->data()) {
    debug_log << "     FCallBuiltin [" << func->name()->data() << "]\n";
  }
#endif
#ifdef CHENG_COUNT_INS
    nested_ins_level_inc();
#endif

  // cheng-hack:
  // (1) check if the args have multiVal
  bool multi_call = false; // whether we should do multicall
  int call_num = 0;  // how many multivalue in args
#ifdef CHENG_OPT_1
  int batch_call_opt_num = 1;
  bool same_following_val = true;
#endif
  // NOTE: since stack grow to low address, 
  // args is the high address; rargs is the low address
  TypedValue* rargs = vmStack().topTV();
  std::vector<TypedValue*> ref_args, ref_multi_list, obj_args, multi_args;
  std::vector<MultiVal*> obj_multi_list;
  std::vector<MultiVal*> multi_val_list;
  for (int i = 0; i < numArgs; i ++) {
    if (UNLIKELY(rargs[i].m_type == KindOfMulti)) {
      multi_call = true;
      if (call_num == 0) call_num = rargs[i].m_data.pmulti->valSize();
      multi_val_list.push_back(rargs[i].m_data.pmulti);
      multi_args.push_back(&rargs[i]);
    } else if (UNLIKELY(rargs[i].m_type == KindOfRef)) {
      // We meet side-effect builtin function,
      // record the ref, we will split it later
      //std::cout << "  FCallBuiltin [" << func->name()->data() << "] with ref\n";
      if (tvToCell(&rargs[i])->m_type == KindOfMulti) {
        //std::cout << "  FCallBuiltin [" << func->name()->data() << "] with ref to multi\n";
        call_num = tvToCell(&rargs[i])->m_data.pmulti->valSize();
        multi_call = true;
      }
      ref_args.push_back(&rargs[i]);
    } else if (UNLIKELY(rargs[i].m_type == KindOfObject)) {
      // We meet side-effect builtin function,
      // record the obj, we will split it later if necessary
      int num = MultiVal::containMultiVal(&rargs[i]);
      if (num != 0) {
        call_num = num; 
        multi_call = true;
      }
      obj_args.push_back(&rargs[i]);
    }
  }
  // (2) check if builtin function should be bypass
  if (UNLIKELY(multi_call && isBypassFunc(func->name()->data()))) {
    multi_call = false;
  }
  // call_counter indicates which turn are we in
  int call_counter = 0;
  TypedValue result;
  TypedValue orig_stack[numArgs];

  if (UNLIKELY(multi_call)) {START; AS_MCALL;} 

  if (UNLIKELY(single_mode_on && multi_call)) {
    for (int i = 0; i < multi_args.size(); i++) {
      // need change multi to single
      TypedValue *tmptv = multi_val_list[i]->getByVal(single_mode_cur_iter);
      tvDup(*tmptv, *multi_args[i]); // here will increase the inner counter
      //tvCopy(*tmptv, *multi_args[i]);
    }
    multi_call = false;
  }

multicall_begin:
  if (UNLIKELY(multi_call)) {
    // (3) Initial everything in the very beginning
    if (call_counter == 0) {
#ifdef CHENG_INS_DEBUG
    debug_log << "  FCallBuiltin [" << func->name()->data() << "] with "
      << " multi values. Args are: \n";
    for (int i = 0; i < numArgs; i++) {
      debug_log << "    " << rargs[i].pretty();
    }
#endif
      result = MultiVal::makeMultiVal();
      memcpy(orig_stack, rargs, sizeof(struct TypedValue)*numArgs);
      // split the non-multi ref_args
      // NOTE: this is tricky since we will have ref to multival
      if (ref_args.size() != 0) {
        for (auto ref_it : ref_args) {
          TypedValue *cell = ref_it->m_data.pref->tv();
          // if the ref is point to single element, split it!
          if (cell->m_type != KindOfMulti) {
            TypedValue tmp = splitElements(cell, call_num);
            tvRefcountedIncRef(cell);
            tvCopy(tmp, *cell);
          }
          // save the original 
          ref_multi_list.push_back(cell);
        }
      }
      // split the non-multi object
      if (obj_args.size() != 0) {
        for (auto obj_it : obj_args) {
          auto orig_obj_ptr = obj_it->m_data.pobj;
          // if the obj is single, split it
          if (!MultiVal::containMultiVal(obj_it)) {
            TypedValue tmp = splitElements(obj_it, call_num);
            tvCopy(tmp, *obj_it);
          } else {
            TypedValue tmp = MultiVal::transferObj(*obj_it);
            tvCopy(tmp, *obj_it);
          }
          obj_multi_list.push_back(obj_it->m_data.pmulti);
          // the original obj ptr is in orig_obj_ptr
          // the new multi-obj is in *obj_it
          // replace the obj on stack/global space 
          auto f = [orig_obj_ptr, obj_it] (TypedValue* tv) {
            if (tv->m_type == KindOfObject && 
                tv->m_data.pobj == orig_obj_ptr) {
#ifdef CHENG_INS_DEBUG
              debug_log << "    replace obj {" << tv->pretty() << "} at location "
                << tv << " into multi-obj\n";
#endif
              tvRefcountedDecRef(tv);
              tvDup(*obj_it, *tv); 
            }
          };
          // FIXME: there are three more: class static/array/object
          iterGlobalVar(f);
          iterLocalVar(f);
        }
      }
    }

    // (4) collect the result, and check if end
    if (call_counter > 0) {
#ifdef CHENG_OPT_1
      // there might be multiple same result
      for (int i = 0; i < batch_call_opt_num; i++) {
        result.m_data.pmulti->addValue(ret);
      }
#else
        // for the ret tv, there is one ref 
        result.m_data.pmulti->addValueNoInc(ret);
#endif
      for (int i = 0; i < ref_args.size(); i++) {
#ifdef CHENG_INS_DEBUG
        auto txt_ref = HHVM_FN(print_r)(tvAsVariant(tvToCell(ref_args[i])), true);
        debug_log << "   After Round[" << call_counter << "] " << i << "th Ref:[[" << txt_ref.toString().toCppString() << "]]\n";
#endif
      }
#ifdef CHENG_INS_DEBUG
      debug_log << "  Iter[" << call_counter << "], result is:" 
        << ret.pretty() << "\n";
#endif
    }

    if (call_counter >= call_num) {
      // USED TO BE A BUG: at the end of the call, the argument on stack will be removed
      //    with the reference decrease, that may make the multi-value a dangling pointer.
      //    So, we need to replace the argument here.
      memcpy(rargs, orig_stack, sizeof(TypedValue)*numArgs); // recover to original args
      // this is end, THERE IS NO RETURN!
#ifdef CHENG_INS_DEBUG
      debug_log << "  Return Value is:\n"  << result.m_data.pmulti->dump("    ");
#endif

      // Optimization, shrink, not sure if good for performance or bad
      TypedValue *shrink = result.m_data.pmulti->shrinkToSingle();
      if (shrink == nullptr) {
        // move the multi-result to ret 
        // they all have one ref-count in multival
        tvCopy(result, ret);
      } else {
        tvDup(*shrink, ret); 
        tvRefcountedDecRef(&result);
      }

      // update the ref-multi type
      for (auto ref_multi : ref_multi_list) {
        auto type = ref_multi->m_data.pmulti->getByVal(0)->m_type;
#ifdef CHENG_CHECK
        for (auto it : *ref_multi->m_data.pmulti) {
          cheng_assert(it->m_type == type);
        }
#endif
        ref_multi->m_data.pmulti->setType(type);
      }
      END;
      single_mode_on = false;
#ifdef CHENG_INS_ONLY_DEBUG
    debug_log << "single_mode_on = false\n";
#endif
      single_mode_cur_iter = -1;
      goto multicall_end;
    }

    // (5) prepare the single value call args
    // no need to do this, if multi will be updated later, if non-multi will be the same
    //memcpy(rargs, orig_stack, sizeof(TypedValue)*numArgs); // recover to original args
    for (int i = 0; i < multi_args.size(); i++) {
      // need change multi to single
      if (call_counter > 0) tvRefcountedDecRef(multi_args[i]);
      TypedValue *tmptv = multi_val_list[i]->getByVal(call_counter);
      tvDup(*tmptv, *multi_args[i]); // here will increase the inner counter
      //tvCopy(*tmptv, *multi_args[i]);
    }
    // NOTE: if there is one single value which has side effect,
    // what should we do? Split and copy.
    for (int i = 0; i < ref_args.size(); i++) {
      // ref_args[i] points to the location on stack
      // FIXME: this is dangerous!
      ref_args[i]->m_data.pref = (RefData *) ref_multi_list[i]->m_data.pmulti->getByVal(call_counter);
#ifdef CHENG_INS_DEBUG
      auto txt_ref = HHVM_FN(print_r)(tvAsVariant(tvToCell(ref_args[i])), true);
      debug_log << "    Round[" << (call_counter+1) << "] " << i << "th Ref:[[" << txt_ref.toString().toCppString() << "]]\n";
#endif
    }
    // replace multi-obj with single-obj
    for (int i = 0; i < obj_args.size(); i++) {
      // obj_args[i] points to the location on stack, and it is multi-obj
      tvCopy(*obj_multi_list[i]->getByVal(call_counter), *obj_args[i]);
    }
    // If we are here, it means we are not in the single_mode
    single_mode_on = true;
#ifdef CHENG_INS_ONLY_DEBUG
    debug_log << "single_mode_on = true\n";
#endif
    single_mode_cur_iter = call_counter;
    single_mode_size = obj_args.size();

#ifdef CHENG_OPT_1
    // batch_call optimization
    // check if the following multi-values are the same
    batch_call_opt_num = 1;
    same_following_val = true;
    while( (call_counter+batch_call_opt_num < call_num)  // call_counter + batch_call_opt_num is the index
          & same_following_val) {
      for (int i = 0; i < multi_args.size(); i++) {
        TypedValue *tmptv = multi_val_list[i]->getByVal(call_counter + batch_call_opt_num);
        if( multi_args[i]->m_type != tmptv->m_type || multi_args[i]->m_data.num != tmptv->m_data.num) {
          same_following_val = false;
          break;
        }
      }
      for (int i = 0; i < ref_args.size(); i++) {
        // ref_args[i] points to the location on stack
        if (ref_args[i]->m_data.pref != (RefData *) ref_multi_list[i]->m_data.pmulti->getByVal(call_counter + batch_call_opt_num)) {
          same_following_val = false;
          break;
        }
      }
      if (same_following_val) {
        batch_call_opt_num++;
      }
    }
    call_counter+=batch_call_opt_num;
#else
    call_counter++;
#endif
  }

  if (Native::coerceFCallArgs(args, numArgs, numNonDefault, func)) {
    Native::callFunc<true, false>(func, nullptr, args, ret);
  } else {
    if (func->attrs() & AttrParamCoerceModeNull) {
      ret.m_type = KindOfNull;
    } else {
      assert(func->attrs() & AttrParamCoerceModeFalse);
      ret.m_type = KindOfBoolean;
      ret.m_data.num = 0;
    }
  }

  // cheng-hack:
  if (multi_call) {
    goto multicall_begin;
  }
multicall_end:

  frame_free_args(args, numNonDefault);
  vmStack().ndiscard(numArgs);
  tvCopy(ret, *vmStack().allocTV());

#ifdef CHENG_COUNT_INS
    nested_ins_level_dec();
#endif
}

enum class CallArrOnInvalidContainer {
  // task #1756122: warning and returning null is what we /should/ always
  // do in call_user_func_array, but some code depends on the broken
  // behavior of casting the list of args to FCallArray to an array.
  CastToArray,
  WarnAndReturnNull,
  WarnAndContinue
};

// supported inside prepareArrayArgs() 
static bool doFCallArray(PC& pc, int numStackValues,
                         CallArrOnInvalidContainer onInvalid) {
  assert(numStackValues >= 1);
  ActRec* ar = (ActRec*)(vmStack().top() + numStackValues);
  assert(ar->numArgs() == numStackValues);

  Cell* c1 = vmStack().topC();
  if (UNLIKELY(!isContainer(*c1))) {
    switch (onInvalid) {
      case CallArrOnInvalidContainer::CastToArray:
        tvCastToArrayInPlace(c1);
        break;
      case CallArrOnInvalidContainer::WarnAndReturnNull:
        vmStack().pushNull();
        cleanupParamsAndActRec(vmStack(), ar, nullptr, nullptr);
        raise_warning("call_user_func_array() expects parameter 2 to be array");
        return false;
      case CallArrOnInvalidContainer::WarnAndContinue:
        tvRefcountedDecRef(c1);
        // argument_unpacking RFC dictates "containers and Traversables"
        raise_debugging("Only containers may be unpacked");
        c1->m_type = KindOfArray;
        c1->m_data.parr = staticEmptyArray();
        break;
    }
  }

  const Func* func = ar->m_func;
  {
    Cell args = *c1;
    vmStack().discard(); // prepareArrayArgs will push arguments onto the stack
    numStackValues--;
    SCOPE_EXIT { tvRefcountedDecRef(&args); };
    checkStack(vmStack(), func, 0);

    assert(!ar->resumed());
    TRACE(3, "FCallArray: pc %p func %p base %d\n", vmpc(),
          vmfp()->unit()->entry(),
          int(vmfp()->m_func->base()));
    ar->setReturn(vmfp(), pc, mcg->tx().uniqueStubs.retHelper);

    if (UNLIKELY((CallArrOnInvalidContainer::WarnAndContinue == onInvalid)
                 && func->anyByRef())) {
      raise_error("Unpacking unsupported for calls to functions that"
                  " take any arguments by reference");
      vmStack().pushNull();
      return false;
    }

    auto prepResult = prepareArrayArgs(ar, args, vmStack(), numStackValues,
                                       /* ref param checks */ true, nullptr);
    if (UNLIKELY(!prepResult)) {
      vmStack().pushNull(); // return value is null if args are invalid
      return false;
    }
  }

  prepareFuncEntry(ar, pc, StackArgsState::Trimmed);
  vmpc() = pc;
  if (UNLIKELY(!EventHook::FunctionCall(ar, EventHook::NormalFunc))) {
    pc = vmpc();
    return false;
  }
  return true;
}

// Supported
bool doFCallArrayTC(PC pc) {
  assert_native_stack_aligned();
  assert(tl_regState == VMRegState::DIRTY);
  tl_regState = VMRegState::CLEAN;
  auto const ret = doFCallArray(pc, 1, CallArrOnInvalidContainer::CastToArray);
  tl_regState = VMRegState::DIRTY;
  return ret;
}

// Support 
OPTBLD_INLINE void iopFCallArray(IOP_ARGS) {
  AS_CALL;
  pc++;
  doFCallArray(pc, 1, CallArrOnInvalidContainer::CastToArray);
}

// Support 
OPTBLD_INLINE void iopFCallUnpack(IOP_ARGS) {
  AS_CALL;
  ActRec* ar = arFromInstr(vmStack().top(), (Op*)pc);
  pc++;
  auto numArgs = decode_iva(pc);
  assert(numArgs == ar->numArgs());
  checkStack(vmStack(), ar->m_func, 0);
  doFCallArray(pc, numArgs, CallArrOnInvalidContainer::WarnAndContinue);
}

// Not Impl
OPTBLD_INLINE void iopCufSafeArray(IOP_ARGS) {
  AS_CALL;
  pc++;
  Array ret;
#ifdef CHENG_CHECK
  cheng_assert(vmStack().topTV()->m_type != KindOfMulti);
  cheng_assert(vmStack().indTV(1)->m_type != KindOfMulti);
#endif
  ret.append(tvAsVariant(vmStack().top() + 1));
  ret.appendWithRef(tvAsVariant(vmStack().top() + 0));
  vmStack().popTV();
  vmStack().popTV();
  tvAsVariant(vmStack().top()) = ret;
}

// Not Impl
OPTBLD_INLINE void iopCufSafeReturn(IOP_ARGS) {
  AS_CALL;
  pc++;
#ifdef CHENG_CHECK
  cheng_assert(vmStack().topTV()->m_type != KindOfMulti);
  cheng_assert(vmStack().indTV(1)->m_type != KindOfMulti);
  cheng_assert(vmStack().indTV(2)->m_type != KindOfMulti);
#endif
  bool ok = cellToBool(*tvToCell(vmStack().top() + 1));
  tvRefcountedDecRef(vmStack().top() + 1);
  tvRefcountedDecRef(vmStack().top() + (ok ? 2 : 0));
  if (ok) vmStack().top()[2] = vmStack().top()[0];
  vmStack().ndiscard(2);
}

// cheng-hack:
//   iter->init() may generate multi-iterator
inline bool initIterator(PC& pc, PC& origPc, Iter* it,
                         Offset offset, Cell* c1) {
  bool hasElems = it->init(c1);
  if (!hasElems) {
    pc = origPc + offset;
  }
  vmStack().popC();
  return hasElems;
}

// cheng-hack:
//    Support in initIterator()
OPTBLD_INLINE void iopIterInit(IOP_ARGS) {
  AS_ITER;
  PC origPc = pc;
  pc++;
  auto itId = decode_ia(pc);
  auto offset = decode<Offset>(pc);
  auto val = decode_la(pc);
  Cell* c1 = vmStack().topC();

  Iter* it = frame_iter(vmfp(), itId);
  TypedValue* tv1 = frame_local(vmfp(), val);
  // cheng-hack: c1 can be multi-value
  if (initIterator(pc, origPc, it, offset, c1)) {
    // cheng-hack:
    if (UNLIKELY(it->isMulti())) {
      START;
      AS_MITER;
      // used BUG: need to free the prev variable on tv1
      tvRefcountedDecRef(*tv1);
      tvCopy(it->arrSecond(), *tv1);
      END;
    } else {
      tvAsVariant(tv1) = it->arr().second();
    }
  }
}

// cheng-hack:
//    Support in initIterator()
OPTBLD_INLINE void iopIterInitK(IOP_ARGS) {
  AS_ITER;
  PC origPc = pc;
  pc++;
  auto itId = decode_ia(pc);
  auto offset = decode<Offset>(pc);
  auto val = decode_la(pc);
  auto key = decode_la(pc);
  Cell* c1 = vmStack().topC();
  Iter* it = frame_iter(vmfp(), itId);
  TypedValue* tv1 = frame_local(vmfp(), val);
  TypedValue* tv2 = frame_local(vmfp(), key);
  if (initIterator(pc, origPc, it, offset, c1)) {
    // cheng-hack:
    if (UNLIKELY(it->isMulti())) {
      START;
      AS_MITER;
      // the return value can be multi
      tvCopy(it->arrSecond(), *tv1);
      tvCopy(it->arrFirst(), *tv2);
      END;
    } else {
      tvAsVariant(tv1) = it->arr().second();
      tvAsVariant(tv2) = it->arr().first();
    }
  }
}

// Not Impl
OPTBLD_INLINE void iopWIterInit(IOP_ARGS) {
  AS_ITER;
  PC origPc = pc;
  pc++;
  auto itId = decode_ia(pc);
  auto offset = decode<Offset>(pc);
  auto val = decode_la(pc);
  Cell* c1 = vmStack().topC();
  Iter* it = frame_iter(vmfp(), itId);
  TypedValue* tv1 = frame_local(vmfp(), val);
  if (initIterator(pc, origPc, it, offset, c1)) {
    // cheng-hack: we do not support it for now
    cheng_assert(!it->isMulti());
    tvAsVariant(tv1).setWithRef(it->arr().secondRef());
  }
  // cheng-hack: not support multival yet
  it->setMultiVal(false);
}

// Not Impl
OPTBLD_INLINE void iopWIterInitK(IOP_ARGS) {
  AS_ITER;
  PC origPc = pc;
  pc++;
  auto itId = decode_ia(pc);
  auto offset = decode<Offset>(pc);
  auto val = decode_la(pc);
  auto key = decode_la(pc);
  Cell* c1 = vmStack().topC();
  Iter* it = frame_iter(vmfp(), itId);
  TypedValue* tv1 = frame_local(vmfp(), val);
  TypedValue* tv2 = frame_local(vmfp(), key);
  if (initIterator(pc, origPc, it, offset, c1)) {
    // cheng-hack: we do not support it for now
    cheng_assert(!it->isMulti());
    tvAsVariant(tv1).setWithRef(it->arr().secondRef());
    tvAsVariant(tv2) = it->arr().first();
  }
  // cheng-hack: not support multival yet
  it->setMultiVal(false);
}


inline bool initIteratorM(PC& pc, PC& origPc, Iter* it, Offset offset,
                          Ref* r1, TypedValue *val, TypedValue *key) {
  bool hasElems = false;
  TypedValue* rtv = r1->m_data.pref->tv();
  // cheng-hack:
  if (UNLIKELY(rtv->m_type == KindOfMulti)) {
    cheng_assert(false);
  }
  if (rtv->m_type == KindOfArray) {
    hasElems = new_miter_array_key(it, r1->m_data.pref, val, key);
  } else if (rtv->m_type == KindOfObject)  {
    Class* ctx = arGetContextClass(vmfp());
    hasElems = new_miter_object(it, r1->m_data.pref, ctx, val, key);
  } else {
    hasElems = new_miter_other(it, r1->m_data.pref);
  }

  if (!hasElems) {
    pc = origPc + offset;
  }

  vmStack().popV();
  return hasElems;
}

// Not Impl
OPTBLD_INLINE void iopMIterInit(IOP_ARGS) {
  AS_ITER;
  PC origPc = pc;
  pc++;
  auto itId = decode_ia(pc);
  auto offset = decode<Offset>(pc);
  auto val = decode_la(pc);
  Ref* r1 = vmStack().topV();
#ifdef CHENG_CHECK
  cheng_assert(r1->m_type != KindOfMulti);
#endif
  assert(r1->m_type == KindOfRef);
  Iter* it = frame_iter(vmfp(), itId);
  TypedValue* tv1 = frame_local(vmfp(), val);
  initIteratorM(pc, origPc, it, offset, r1, tv1, nullptr);
  // cheng-hack: not support multival yet
  it->setMultiVal(false);
}

// Not Impl
OPTBLD_INLINE void iopMIterInitK(IOP_ARGS) {
  AS_ITER;
  PC origPc = pc;
  pc++;
  auto itId = decode_ia(pc);
  auto offset = decode<Offset>(pc);
  auto val = decode_la(pc);
  auto key = decode_la(pc);
  Ref* r1 = vmStack().topV();
#ifdef CHENG_CHECK
  cheng_assert(r1->m_type != KindOfMulti);
#endif
  assert(r1->m_type == KindOfRef);
  Iter* it = frame_iter(vmfp(), itId);
  TypedValue* tv1 = frame_local(vmfp(), val);
  TypedValue* tv2 = frame_local(vmfp(), key);
  initIteratorM(pc, origPc, it, offset, r1, tv1, tv2);
  // cheng-hack: not support multival yet
  it->setMultiVal(false);
}

// Support
OPTBLD_INLINE void iopIterNext(IOP_ARGS) {
  AS_ITER;
  PC origPc = pc;
  pc++;
  auto itId = decode_ia(pc);
  auto offset = decode<Offset>(pc);
  auto val = decode_la(pc);
  jmpSurpriseCheck(offset);
  Iter* it = frame_iter(vmfp(), itId);
  TypedValue* tv1 = frame_local(vmfp(), val);
  if (it->next()) {
    pc = origPc + offset;
    // cheng-hack:
    if (UNLIKELY(it->isMulti())) {
      START;
      AS_MITER;
      // FIXME: in the original case, it use tvAsVariant, which may 
      //        generatee different behavior to tvCopy
      // used BUG: need to free the prev variable on tv1
      tvRefcountedDecRef(*tv1);
      tvCopy(it->arrSecond(), *tv1);
      END;
    } else {
      tvAsVariant(tv1) = it->arr().second();
    }
  }
}

// Support
OPTBLD_INLINE void iopIterNextK(IOP_ARGS) {
  AS_ITER;
  PC origPc = pc;
  pc++;
  auto itId = decode_ia(pc);
  auto offset = decode<Offset>(pc);
  auto val = decode_la(pc);
  auto key = decode_la(pc);
  jmpSurpriseCheck(offset);
  Iter* it = frame_iter(vmfp(), itId);
  TypedValue* tv1 = frame_local(vmfp(), val);
  TypedValue* tv2 = frame_local(vmfp(), key);
  if (it->next()) {
    pc = origPc + offset;
    // cheng-hack:
    if (UNLIKELY(it->isMulti())) {
      START;
      AS_MITER;
      // FIXME: in the original case, it use tvAsVariant, which may 
      //        generatee different behavior to tvCopy
      tvCopy(it->arrSecond(), *tv1);
      tvCopy(it->arrFirst(), *tv2);
      END;
    } else {
      tvAsVariant(tv1) = it->arr().second();
      tvAsVariant(tv2) = it->arr().first();
    }
  }
}

// Not Impl
OPTBLD_INLINE void iopWIterNext(IOP_ARGS) {
  AS_ITER;
  PC origPc = pc;
  pc++;
  auto itId = decode_ia(pc);
  auto offset = decode<Offset>(pc);
  auto val = decode_la(pc);
  jmpSurpriseCheck(offset);
  Iter* it = frame_iter(vmfp(), itId);
  TypedValue* tv1 = frame_local(vmfp(), val);
  // Not support for now
  cheng_assert(!it->isMulti());
  if (it->next()) {
    pc = origPc + offset;
    tvAsVariant(tv1).setWithRef(it->arr().secondRef());
  }
}

// Not Impl 
OPTBLD_INLINE void iopWIterNextK(IOP_ARGS) {
  AS_ITER;
  PC origPc = pc;
  pc++;
  auto itId = decode_ia(pc);
  auto offset = decode<Offset>(pc);
  auto val = decode_la(pc);
  auto key = decode_la(pc);
  jmpSurpriseCheck(offset);
  Iter* it = frame_iter(vmfp(), itId);
  TypedValue* tv1 = frame_local(vmfp(), val);
  TypedValue* tv2 = frame_local(vmfp(), key);
  // Not support for now
  cheng_assert(!it->isMulti());
  if (it->next()) {
    pc = origPc + offset;
    tvAsVariant(tv1).setWithRef(it->arr().secondRef());
    tvAsVariant(tv2) = it->arr().first();
  }
}

// Not Impl 
OPTBLD_INLINE void iopMIterNext(IOP_ARGS) {
  AS_ITER;
  PC origPc = pc;
  pc++;
  auto itId = decode_ia(pc);
  auto offset = decode<Offset>(pc);
  auto val = decode_la(pc);
  jmpSurpriseCheck(offset);
  Iter* it = frame_iter(vmfp(), itId);
  // Not support for now
  cheng_assert(!it->isMulti());
  TypedValue* tv1 = frame_local(vmfp(), val);
  if (miter_next_key(it, tv1, nullptr)) {
    pc = origPc + offset;
  }
}

// Not Impl
OPTBLD_INLINE void iopMIterNextK(IOP_ARGS) {
  AS_ITER;
  PC origPc = pc;
  pc++;
  auto itId = decode_ia(pc);
  auto offset = decode<Offset>(pc);
  auto val = decode_la(pc);
  auto key = decode_la(pc);
  jmpSurpriseCheck(offset);
  Iter* it = frame_iter(vmfp(), itId);
  // Not support for now
  cheng_assert(!it->isMulti());
  TypedValue* tv1 = frame_local(vmfp(), val);
  TypedValue* tv2 = frame_local(vmfp(), key);
  if (miter_next_key(it, tv1, tv2)) {
    pc = origPc + offset;
  }
}

// support in it->free()
OPTBLD_INLINE void iopIterFree(IOP_ARGS) {
  AS_ITER;
  pc++;
  auto itId = decode_ia(pc);
  Iter* it = frame_iter(vmfp(), itId);
  it->free();
}

// Not Impl 
OPTBLD_INLINE void iopMIterFree(IOP_ARGS) {
  AS_ITER;
  pc++;
  auto itId = decode_ia(pc);
  Iter* it = frame_iter(vmfp(), itId);
  // Not support for now
  cheng_assert(!it->isMulti());
  it->mfree();
}

// Not Impl 
OPTBLD_INLINE void iopCIterFree(IOP_ARGS) {
  AS_ITER;
  pc++;
  auto itId = decode_ia(pc);
  Iter* it = frame_iter(vmfp(), itId);
  // Not support for now
  // FIXME: I don't know why this will called for an uninitialized iterators
  // BUG situation: free itId=0, but only init itId=1
  // cheng_assert(!it->isMulti());
  it->setMultiVal(false);
  it->cfree();
}

// Should never include multiple files
OPTBLD_INLINE void inclOp(PC& pc, InclOpFlags flags) {
  pc++;
  Cell* c1 = vmStack().topC();

  // cheng-hack:
#ifdef CHENG_INS_DEBUG
  auto txt = HHVM_FN(print_r)(tvAsVariant(c1), true); 
  debug_log << "    include file " << txt.toString().toCppString() << "\n";
#endif
  if (UNLIKELY(c1->m_type == KindOfMulti)) {
    auto single = c1->m_data.pmulti->shrinkToSingle();
    if (single != nullptr) {
      tvCopy(*single, *c1);
    }
  }
  cheng_assert(c1->m_type != KindOfMulti);

  String path(prepareKey(*c1));
  bool initial;
  TRACE(2, "inclOp %s %s %s %s \"%s\"\n",
        flags & InclOpFlags::Once ? "Once" : "",
        flags & InclOpFlags::DocRoot ? "DocRoot" : "",
        flags & InclOpFlags::Relative ? "Relative" : "",
        flags & InclOpFlags::Fatal ? "Fatal" : "",
        path.data());

  auto curUnitFilePath = [&] {
    namespace fs = boost::filesystem;
    fs::path currentUnit(vmfp()->m_func->unit()->filepath()->data());
    fs::path currentDir(currentUnit.branch_path());
    return currentDir.string();
  };

  auto const unit = [&] {
    if (flags & InclOpFlags::Relative) {
      String absPath = curUnitFilePath() + '/';
      absPath += path;
      return lookupUnit(absPath.get(), "", &initial);
    }
    if (flags & InclOpFlags::DocRoot) {
      return lookupUnit(
        SourceRootInfo::RelativeToPhpRoot(path).get(), "", &initial);
    }
    return lookupUnit(path.get(), curUnitFilePath().c_str(), &initial);
  }();

  vmStack().popC();
  if (unit == nullptr) {
    if (flags & InclOpFlags::Fatal) {
      raise_error("File not found: %s", path.data());
    } else {
      raise_warning("File not found: %s", path.data());
    }
    vmStack().pushFalse();
    return;
  }

  if (!(flags & InclOpFlags::Once) || initial) {
    g_context->evalUnit(unit, pc, EventHook::PseudoMain);
  } else {
    Stats::inc(Stats::PseudoMain_Guarded);
    vmStack().pushTrue();
  }
}

// Good to go
OPTBLD_INLINE void iopIncl(IOP_ARGS) {
  inclOp(pc, InclOpFlags::Default);
}

// Good to go
OPTBLD_INLINE void iopInclOnce(IOP_ARGS) {
  inclOp(pc, InclOpFlags::Once);
}

// Good to go
OPTBLD_INLINE void iopReq(IOP_ARGS) {
  inclOp(pc, InclOpFlags::Fatal);
}

// Good to go
OPTBLD_INLINE void iopReqOnce(IOP_ARGS) {
  inclOp(pc, InclOpFlags::Fatal | InclOpFlags::Once);
}

// Good to go
OPTBLD_INLINE void iopReqDoc(IOP_ARGS) {
  inclOp(pc, InclOpFlags::Fatal | InclOpFlags::Once | InclOpFlags::DocRoot);
}

// Good to go
OPTBLD_INLINE void iopEval(IOP_ARGS) {
  pc++;
  Cell* c1 = vmStack().topC();

  if (UNLIKELY(RuntimeOption::EvalAuthoritativeMode)) {
    // Ahead of time whole program optimizations need to assume it can
    // see all the code, or it really can't do much.
    raise_error("You can't use eval in RepoAuthoritative mode");
  }

  String code(prepareKey(*c1));
  String prefixedCode = concat("<?php ", code);

  auto evalFilename = std::string();
  auto vm = &*g_context;
  string_printf(
    evalFilename,
    "%s(%d" EVAL_FILENAME_SUFFIX,
    vm->getContainingFileName()->data(),
    vm->getLine()
  );
  Unit* unit = vm->compileEvalString(prefixedCode.get(), evalFilename.c_str());

  const StringData* msg;
  int line = 0;

  vmStack().popC();
  if (unit->parseFatal(msg, line)) {
    int errnum = static_cast<int>(ErrorConstants::ErrorModes::WARNING);
    if (vm->errorNeedsLogging(errnum)) {
      // manual call to Logger instead of logError as we need to use
      // evalFileName and line as the exception doesn't track the eval()
      Logger::Error(
        "\nFatal error: %s in %s on line %d",
        msg->data(),
        evalFilename.c_str(),
        line
      );
    }

    vmStack().pushFalse();
    return;
  }
  vm->evalUnit(unit, pc, EventHook::Eval);
}

// Good to go
OPTBLD_INLINE void iopDefFunc(IOP_ARGS) {
  pc++;
  auto fid = decode_iva(pc);
  Func* f = vmfp()->m_func->unit()->lookupFuncId(fid);
  setCachedFunc(f, isDebuggerAttached());
}

// Good to go
OPTBLD_INLINE void iopDefCls(IOP_ARGS) {
  pc++;
  auto cid = decode_iva(pc);
  PreClass* c = vmfp()->m_func->unit()->lookupPreClassId(cid);
  Unit::defClass(c);
}

// Good to go
OPTBLD_INLINE void iopDefClsNop(IOP_ARGS) {
  pc++;
  decode_iva(pc); // cid
}

// Good to go
OPTBLD_INLINE void iopDefTypeAlias(IOP_ARGS) {
  pc++;
  auto tid = decode_iva(pc);
  vmfp()->m_func->unit()->defTypeAlias(tid);
}

static inline void checkThis(ActRec* fp) {
  if (!fp->hasThis()) {
    raise_error(Strings::FATAL_NULL_THIS);
  }
}

// Support
OPTBLD_INLINE void iopThis(IOP_ARGS) {
  AS_MISC;
  pc++;
  checkThis(vmfp());
  // cheng-hack:
  if (UNLIKELY(vmfp()->isMultiThis())) {
    START;
    AS_MMISC;
    auto this_ = vmfp()->getThisMulti();
    TypedValue tv = genMultiVal(this_);
    vmStack().pushMultiObject(tv);
    END;
  } else {
    // normal case
  ObjectData* this_ = vmfp()->getThisSingle();
  vmStack().pushObject(this_);
  }
}

// Support
OPTBLD_INLINE void iopBareThis(IOP_ARGS) {
  AS_MISC;
  pc++;
  auto bto = decode_oa<BareThisOp>(pc);
  if (vmfp()->hasThis()) {
    // cheng-hack:
    if (UNLIKELY(vmfp()->isMultiThis())) {
      START;
      AS_MMISC;
      auto this_ = vmfp()->getThisMulti();
      TypedValue tv = genMultiVal(this_);
      vmStack().pushMultiObject(tv);
      END;
    } else {
      // normal case
    ObjectData* this_ = vmfp()->getThisSingle();
    vmStack().pushObject(this_);
    }
  } else {
    vmStack().pushNull();
    switch (bto) {
    case BareThisOp::Notice:   raise_notice(Strings::WARN_NULL_THIS); break;
    case BareThisOp::NoNotice: break;
    case BareThisOp::NeverNull:
      assert(!"$this cannot be null in BareThis with NeverNull option");
      break;
    }
  }
}

// Good to go
OPTBLD_INLINE void iopCheckThis(IOP_ARGS) {
  pc++;
  checkThis(vmfp());
}

// Good to go
OPTBLD_INLINE void iopInitThisLoc(IOP_ARGS) {
  pc++;
  auto id = decode_la(pc);
  TypedValue* thisLoc = frame_local(vmfp(), id);
  tvRefcountedDecRef(thisLoc);
  if (vmfp()->hasThis()) {
    // cheng-hack:
    if (UNLIKELY(vmfp()->isMultiThis())) {
      TypedValue tv = genMultiVal(vmfp()->getThisMulti());
      tvCopy(tv, *thisLoc);
    } else {
      // normal case
    thisLoc->m_data.pobj = vmfp()->getThisSingle();
    thisLoc->m_type = KindOfObject;
    tvIncRef(thisLoc);
    }
  } else {
    tvWriteUninit(thisLoc);
  }
}

static inline RefData* lookupStatic(StringData* name,
                                    const ActRec* fp,
                                    bool& inited) {
  auto const func = fp->m_func;

  if (UNLIKELY(func->isClosureBody())) {
    assert(!func->hasVariadicCaptureParam());
    return lookupStaticFromClosure(
      frame_local(fp, func->numParams())->m_data.pobj, name, inited);
  }

  auto const refData = RDS::bindStaticLocal(func, name);
  inited = !refData->isUninitializedInRDS();
  if (!inited) refData->initInRDS();
  return refData.get();
}

// Support by tvBindMulti()
OPTBLD_INLINE void iopStaticLoc(IOP_ARGS) {
  pc++;
  auto localId = decode_la(pc);
  auto var = decode_litstr(pc);

  bool inited;
  auto const refData = lookupStatic(var, vmfp(), inited);
  if (!inited) {
    refData->tv()->m_type = KindOfNull;
  }

  auto const tvLocal = frame_local(vmfp(), localId);
  auto const tmpTV = make_tv<KindOfRef>(refData);
  //tvBind(&tmpTV, tvLocal);
  tvBindMulti(&tmpTV, tvLocal);
  if (inited) {
    vmStack().pushTrue();
  } else {
    vmStack().pushFalse();
  }
}

// No idea how to trigger this
OPTBLD_INLINE void iopStaticLocInit(IOP_ARGS) {
  pc++;
  auto localId = decode_la(pc);
  auto var = decode_litstr(pc);

  bool inited;
  auto const refData = lookupStatic(var, vmfp(), inited);

  if (!inited) {
    auto const initVal = vmStack().topC();
    cellDup(*initVal, *refData->tv());
  }

  auto const tvLocal = frame_local(vmfp(), localId);
  auto const tmpTV = make_tv<KindOfRef>(refData);
  //tvBind(&tmpTV, tvLocal);
  tvBindMulti(&tmpTV, tvLocal);
  vmStack().discard();
}

// Good to go
OPTBLD_INLINE void iopCatch(IOP_ARGS) {
  pc++;
  auto vm = &*g_context;
  assert(vm->m_faults.size() > 0);
  Fault fault = vm->m_faults.back();
  vm->m_faults.pop_back();
  assert(fault.m_raiseFrame == vmfp());
  assert(fault.m_faultType == Fault::Type::UserException);
  vmStack().pushObjectNoRc(fault.m_userException);
}

// good to go
OPTBLD_INLINE void iopLateBoundCls(IOP_ARGS) {
  pc++;
  Class* cls = frameStaticClass(vmfp());
  if (!cls) {
    raise_error(HPHP::Strings::CANT_ACCESS_STATIC);
  }
  vmStack().pushClass(cls);
}

// Skip the verification if param is multival
OPTBLD_INLINE void iopVerifyParamType(IOP_ARGS) {
  vmpc() = pc; // We might need vmpc() to be updated to throw.
  pc++;

  auto paramId = decode_la(pc);
  const Func *func = vmfp()->m_func;
  assert(paramId < func->numParams());
  assert(func->numParams() == int(func->params().size()));
  const TypeConstraint& tc = func->params()[paramId].typeConstraint;
  assert(tc.hasConstraint());
  if (!tc.isTypeVar()) {
    auto cur_param = frame_local(vmfp(), paramId);
    //if (UNLIKELY(MultiVal::containMultiVal(cur_param))) {
      //debug_log << "    meet a multival, and we skip the verifyParam\n";
    //} else {
    //}
    // FIXME: BUMMER! I commented out the below line to avoid calling the above line
    //tc.verifyParam(cur_param, func, paramId);
  }
}

OPTBLD_INLINE void implVerifyRetType(PC& pc) {
  if (LIKELY(!RuntimeOption::EvalCheckReturnTypeHints)) {
    pc++;
    return;
  }
  vmpc() = pc;
  pc++;
  const auto func = vmfp()->m_func;
  const auto tc = func->returnTypeConstraint();
  if (!tc.isTypeVar()) {
    // cheng-hack:
    // TODO: this is not tested yet.
    if (UNLIKELY(vmStack().topTV()->m_type == KindOfMulti)) {
      auto multi_val = vmStack().topTV();
      // assume there is no side effect inside
      tc.verifyReturn(multi_val->m_data.pmulti->getByVal(0), func);
    } else {
    // normal case
    tc.verifyReturn(vmStack().topTV(), func);
    }
  }
}

// Support by implVerifyRetType()
OPTBLD_INLINE void iopVerifyRetTypeC(IOP_ARGS) {
  implVerifyRetType(pc);
}

// Support by implVerifyRetType()
OPTBLD_INLINE void iopVerifyRetTypeV(IOP_ARGS) {
  implVerifyRetType(pc);
}

// support
OPTBLD_INLINE void iopNativeImpl(IOP_ARGS) {
  AS_CALL;
  pc++;
  BuiltinFunction func = vmfp()->func()->builtinFuncPtr();
  assert(func);

#ifdef CHENG_COUNT_INS
    nested_ins_level_inc();
#endif
  // cheng-hack:
  // TODO: this is not tested yet.
  // otherwise, the compiler will complain the goto 
  ActRec* sfp = nullptr;
  Offset soff {0}; 

  // NOTE: similar code to FCallBuiltin, but have no idea how to
  // make it more graceful. =.=
  TypedValue* rargs = vmStack().topTV();
  int32_t numArgs = vmfp()->func()->numParams();

  bool multi_call = false, multi_this = false; // whether we should do multicall
  bool multi_var_arglist = false;
  ArrayData* orig_var_arglist = nullptr;
//  bool is_multi[numArgs] = {false};
  bool is_multi[numArgs];
  memset(is_multi, 0, numArgs*sizeof(bool));
  int multival_num = 0, call_num = 0;  // how many multivalue in args
  // NOTE: since stack grow to low address, 
  // args is the high address; rargs is the low address
  for (int i = 0; i < numArgs; i++) {
    if (rargs[i].m_type == KindOfMulti) {
      multi_call = true;
      is_multi[i] = true;
      multival_num++;
      if (call_num == 0) call_num = rargs[i].m_data.pmulti->valSize();
    }
  }
  // cheng-hack: check variable-length argument list
  if (numArgs == 2 && rargs[0].m_type == KindOfArray) {
    // might be variable-length argument list, check
    orig_var_arglist = rargs[0].m_data.parr->copy();
    for (ArrayIter iter(rargs[0]); iter; ++iter) {
      if (iter.second().m_type == KindOfMulti) {
#ifdef CHENG_INS_DEBUG
        debug_log << "    During NativeImpl, meet the variable-length argument list\n";
#endif
        multi_call = true;
        multi_var_arglist = true;
        call_num = iter.second().m_data.pmulti->valSize();
      }
    }
  }
  // POINT2: if multi_this
  sptr< std::vector<ObjectData*> > orig_multi_this = nullptr;
  if (UNLIKELY(vmfp()->isMultiThis())) {
      orig_multi_this = vmfp()->getThisMulti();
      multi_this = true;
      call_num = orig_multi_this->size();
  }
  // check if builtin function should be bypass
  if (UNLIKELY( (multi_call || multi_this) 
                && isBypassFunc(vmfp()->func()->name()->data()))) {
    multi_call = false;
    multi_this = false;
  }

  // call_counter indicates which turn are we in
  int call_counter = 0;
  TypedValue result;
  TypedValue orig_stack[numArgs];
  struct ActRec orig_ar;
  struct Stack orig_stack_ptr;


  if (UNLIKELY(multi_call || multi_this)) {START; AS_MCALL;}

multicall_begin:
  if (UNLIKELY(multi_call || multi_this)) {
    /* (1) Keep the argument list and ActRec structure
     * (FIXME: what if side effect?)
     * (2) collect result and check if end
     * (3) recover the argument list and ActRec with single value
     */
    // (3) Initial everything in the very beginning
    if (call_counter == 0) {
#ifdef CHENG_INS_DEBUG
    debug_log << "  NativeImpl [" << vmfp()->func()->name()->data() << "] with " << multival_num
      << " multi values, multi_var_arglist: " << multi_var_arglist << "; Args are: \n";
    for (int i = 0; i < numArgs; i++) {
      debug_log << "    " << rargs[i].pretty();
      debug_log << ((is_multi[i]) ? ("\n"+rargs[i].m_data.pmulti->dump("    ")) : "\n");
    }
#endif
      result = MultiVal::makeMultiVal();
      vmfp()->setInMultiRound(true);
      memcpy(orig_stack, rargs, sizeof(struct TypedValue)*numArgs);
      memcpy(&orig_ar, vmfp(), sizeof(struct ActRec));
      orig_stack_ptr = vmStack();
    }

    // collect the result, and check if end
    if (call_counter > 0) {
      TypedValue* ret = vmStack().topTV();
      result.m_data.pmulti->addValue(*ret);
#ifdef CHENG_INS_DEBUG
      debug_log << "  Iter[" << call_counter << "], result is:" 
        << ret->pretty() << "\n";
#endif
    }
    if (call_counter >= call_num) {
      // restore the argument on the stack, in case the free will
      // free the element inside multi-value
      memcpy(rargs, orig_stack, sizeof(TypedValue)*numArgs); // recover to original args
      // this is end, THERE IS NO RETURN!
      TypedValue* ret = vmStack().topTV();
      tvCopy(result, *ret);
      END;
      single_mode_on = false;
#ifdef CHENG_INS_ONLY_DEBUG
    debug_log << "single_mode_on = false\n";
#endif
      single_mode_cur_iter = -1;
      goto multicall_end;
    }

    // prepare the single value call args
    // FIXME: if there is one single value which has side effect,
    // what should we do?
    vmStack() = orig_stack_ptr;
    memcpy(rargs, orig_stack, sizeof(TypedValue)*numArgs); // recover to original args
    memcpy(vmfp(), &orig_ar, sizeof(struct ActRec));
    for (int i = 0; i < numArgs; i++) {
      // need change multi to single
      if (is_multi[i]) {
#ifdef CHENG_CHECK
      cheng_assert(rargs[i].m_type == KindOfMulti);
#endif
        TypedValue *tmptv = rargs[i].m_data.pmulti->getByVal(call_counter);
        tvDup(*tmptv, rargs[i]); // this will increase the inner counter
      }
    }
    if (multi_var_arglist) {
      orig_var_arglist->incRefCount();
      for (ArrayIter iter(orig_var_arglist); iter; ++iter) {
        auto arr = rargs[0].m_data.parr;
        if (iter.second().m_type == KindOfMulti) {
          auto tmpv = iter.second().m_data.pmulti->getByVal(call_counter);
          arr->set(iter.first(), tvAsVariant(tmpv), false);
        } else {
          arr->set(iter.first(), iter.second(), false);
        }
      }
    }
    // POINT2: if this is the __construct for builtin class
    if (multi_this) {
#ifdef CHENG_INS_DEBUG
      debug_log << "    Meet multi-this, choose " << call_counter << " one\n";
#endif
      vmfp()->setThisSingle(orig_multi_this->at(call_counter));
    }

    // If we are here, it means we are not in single mode
    single_mode_on = true;
#ifdef CHENG_INS_ONLY_DEBUG
    debug_log << "single_mode_on = true\n";
#endif
    single_mode_cur_iter = call_counter;
    single_mode_size = call_num;

    call_counter++;
    // if it is last round, free as normal
    if (call_counter == call_num) {
      vmfp()->setInMultiRound(false);
      // FIXME: how to do it correctly to free the copied ArrayData?
      //decRefArr(orig_var_arglist);
    }
  }

  // Actually call the native implementation. This will handle freeing the
  // locals in the normal case. In the case of an exception, the VM unwinder
  // will take care of it.
  func(vmfp());

  // Grab caller info from ActRec.
  sfp = vmfp()->sfp();
  soff = vmfp()->m_soff;

  // Adjust the stack; the native implementation put the return value in the
  // right place for us already
  vmStack().ndiscard(vmfp()->func()->numSlotsInFrame());
  vmStack().ret();

  // cheng-hack:
  if (UNLIKELY(multi_call || multi_this)) {
    goto multicall_begin;
  }
multicall_end:

  // Return control to the caller.
  vmfp() = sfp;
  pc = LIKELY(vmfp() != nullptr) ? vmfp()->func()->getEntry() + soff : nullptr;

#ifdef CHENG_COUNT_INS
    nested_ins_level_dec();
#endif
}

// Good to go
OPTBLD_INLINE void iopSelf(IOP_ARGS) {
  pc++;
  Class* clss = arGetContextClass(vmfp());
  if (!clss) {
    raise_error(HPHP::Strings::CANT_ACCESS_SELF);
  }
  vmStack().pushClass(clss);
}

// Good to go
OPTBLD_INLINE void iopParent(IOP_ARGS) {
  pc++;
  Class* clss = arGetContextClass(vmfp());
  if (!clss) {
    raise_error(HPHP::Strings::CANT_ACCESS_PARENT_WHEN_NO_CLASS);
  }
  Class* parent = clss->parent();
  if (!parent) {
    raise_error(HPHP::Strings::CANT_ACCESS_PARENT_WHEN_NO_PARENT);
  }
  vmStack().pushClass(parent);
}

// Good to go
OPTBLD_INLINE void iopCreateCl(IOP_ARGS) {
  pc++;
  auto numArgs = decode_iva(pc);
  auto clsName = decode_litstr(pc);
  auto const cls = Unit::loadClass(clsName);
  auto const cl = static_cast<c_Closure*>(newInstance(cls));
  cl->init(numArgs, vmfp(), vmStack().top());
  vmStack().ndiscard(numArgs);
  vmStack().pushObject(cl);
}

const StaticString s_this("this");

// Good to go?
OPTBLD_INLINE void iopCreateCont(IOP_ARGS) {
  pc++;
  auto const fp = vmfp();
  auto const func = fp->func();
  auto const numSlots = func->numSlotsInFrame();
  auto const resumeOffset = func->unit()->offsetOf(pc);
  assert(!fp->resumed());
  assert(func->isGenerator());

  // Create the {Async,}Generator object. Create takes care of copying local
  // variables and iterators.
  auto const gen = func->isAsync()
    ? static_cast<BaseGenerator*>(
        c_AsyncGenerator::Create(fp, numSlots, nullptr, resumeOffset))
    : static_cast<BaseGenerator*>(
        c_Generator::Create<false>(fp, numSlots, nullptr, resumeOffset));

  EventHook::FunctionSuspendE(fp, gen->actRec());

  // Grab caller info from ActRec.
  ActRec* sfp = fp->sfp();
  Offset soff = fp->m_soff;

  // Free ActRec and store the return value.
  vmStack().ndiscard(numSlots);
  vmStack().ret();
  tvCopy(make_tv<KindOfObject>(gen), *vmStack().topTV());
  assert(vmStack().topTV() == &fp->m_r);

  // Return control to the caller.
  vmfp() = sfp;
  pc = LIKELY(sfp != nullptr) ? sfp->func()->getEntry() + soff : nullptr;
}

static inline BaseGenerator* this_base_generator(const ActRec* fp) {
  // cheng-hack: no idea
  auto const obj = fp->getThisSingle();
  assert(obj->instanceof(c_AsyncGenerator::classof()) ||
         obj->instanceof(c_Generator::classof()));
  return static_cast<BaseGenerator*>(obj);
}

static inline c_Generator* this_generator(const ActRec* fp) {
  auto const obj = this_base_generator(fp);
  assert(obj->getVMClass() == c_Generator::classof());
  return static_cast<c_Generator*>(obj);
}

OPTBLD_INLINE void contEnterImpl(PC& pc) {
  pc++;

  // The stack must have one cell! Or else resumableStackBase() won't work!
  assert(vmStack().top() + 1 ==
         (TypedValue*)vmfp() - vmfp()->m_func->numSlotsInFrame());

  // Do linkage of the generator's AR.
  assert(vmfp()->hasThis());
  BaseGenerator* gen = this_base_generator(vmfp());
  assert(gen->getState() == BaseGenerator::State::Running);
  ActRec* genAR = gen->actRec();
  genAR->setReturn(vmfp(), pc, mcg->tx().uniqueStubs.genRetHelper);

  vmfp() = genAR;

  assert(genAR->func()->contains(gen->resumable()->resumeOffset()));
  pc = genAR->func()->unit()->at(gen->resumable()->resumeOffset());
  vmpc() = pc;
  EventHook::FunctionResumeYield(vmfp());
}

// No idea
OPTBLD_INLINE void iopContEnter(IOP_ARGS) {
  contEnterImpl(pc);
}

// No idea
OPTBLD_INLINE void iopContRaise(IOP_ARGS) {
  contEnterImpl(pc);
  iopThrow(pc);
}

OPTBLD_INLINE void yield(PC& pc, const Cell* key, const Cell value) {
  auto const fp = vmfp();
  auto const func = fp->func();
  auto const resumeOffset = func->unit()->offsetOf(pc);
  assert(fp->resumed());
  assert(func->isGenerator());

  EventHook::FunctionSuspendR(fp, nullptr);

  if (!func->isAsync()) {
    // Non-async generator.
    assert(fp->sfp());
    frame_generator(fp)->yield(resumeOffset, key, value);

    // Push return value of next()/send()/raise().
    vmStack().pushNull();
  } else {
    // Async generator.
    auto const gen = frame_async_generator(fp);
    auto const eagerResult = gen->yield(resumeOffset, key, value);
    if (eagerResult) {
      // Eager execution => return StaticWaitHandle.
      assert(fp->sfp());
      vmStack().pushObjectNoRc(eagerResult);
    } else {
      // Resumed execution => return control to the scheduler.
      assert(!fp->sfp());
    }
  }

  // Grab caller info from ActRec.
  ActRec* sfp = fp->sfp();
  Offset soff = fp->m_soff;

  // Return control to the next()/send()/raise() caller.
  vmfp() = sfp;
  pc = sfp != nullptr ? sfp->func()->getEntry() + soff : nullptr;
}

// No idea
OPTBLD_INLINE void iopYield(IOP_ARGS) {
  pc++;
  auto const value = *vmStack().topC();
  vmStack().discard();
  yield(pc, nullptr, value);
}

// No idea
OPTBLD_INLINE void iopYieldK(IOP_ARGS) {
  pc++;
  auto const key = *vmStack().indC(1);
  auto const value = *vmStack().topC();
  vmStack().ndiscard(2);
  yield(pc, &key, value);
}

// No idea
OPTBLD_INLINE void iopContCheck(IOP_ARGS) {
  pc++;
  auto checkStarted = decode_iva(pc);
  this_base_generator(vmfp())->preNext(checkStarted);
}

// No idea
OPTBLD_INLINE void iopContValid(IOP_ARGS) {
  pc++;
  vmStack().pushBool(
    this_generator(vmfp())->getState() != BaseGenerator::State::Done);
}

// No idea
OPTBLD_INLINE void iopContKey(IOP_ARGS) {
  pc++;
  c_Generator* cont = this_generator(vmfp());
  cont->startedCheck();
  cellDup(cont->m_key, *vmStack().allocC());
}

// No idea
OPTBLD_INLINE void iopContCurrent(IOP_ARGS) {
  pc++;
  c_Generator* cont = this_generator(vmfp());
  cont->startedCheck();
  cellDup(cont->m_value, *vmStack().allocC());
}

OPTBLD_INLINE void asyncSuspendE(PC& pc, int32_t iters) {
  assert(!vmfp()->resumed());
  assert(vmfp()->func()->isAsyncFunction());
  const auto func = vmfp()->m_func;
  const auto resumeOffset = func->unit()->offsetOf(pc);

  // Pop the blocked dependency.
  Cell* value = vmStack().topC();
  assert(value->m_type == KindOfObject);
  assert(value->m_data.pobj->instanceof(c_WaitableWaitHandle::classof()));

  auto child = static_cast<c_WaitableWaitHandle*>(value->m_data.pobj);
  assert(!child->isFinished());
  vmStack().discard();

  // Create the AsyncFunctionWaitHandle object. Create takes care of
  // copying local variables and itertors.
  auto waitHandle = static_cast<c_AsyncFunctionWaitHandle*>(
    c_AsyncFunctionWaitHandle::Create(vmfp(), vmfp()->func()->numSlotsInFrame(),
                                      nullptr, resumeOffset, child));

  // Call the FunctionSuspend hook. FunctionSuspend will decref the newly
  // allocated waitHandle if it throws.
  EventHook::FunctionSuspendE(vmfp(), waitHandle->actRec());

  // Grab caller info from ActRec.
  ActRec* sfp = vmfp()->sfp();
  Offset soff = vmfp()->m_soff;

  // Free ActRec and store the return value.
  vmStack().ndiscard(vmfp()->m_func->numSlotsInFrame());
  vmStack().ret();
  tvCopy(make_tv<KindOfObject>(waitHandle), *vmStack().topTV());
  assert(vmStack().topTV() == &vmfp()->m_r);

  // Return control to the caller.
  vmfp() = sfp;
  pc = LIKELY(vmfp() != nullptr) ? vmfp()->func()->getEntry() + soff : nullptr;
}

OPTBLD_INLINE void asyncSuspendR(PC& pc) {
  auto const fp = vmfp();
  auto const func = fp->func();
  auto const resumeOffset = func->unit()->offsetOf(pc);
  assert(fp->resumed());
  assert(func->isAsync());

  // Obtain child
  Cell& value = *vmStack().topC();
  assert(value.m_type == KindOfObject);
  assert(value.m_data.pobj->instanceof(c_WaitableWaitHandle::classof()));
  auto const child = static_cast<c_WaitableWaitHandle*>(value.m_data.pobj);

  // Before adjusting the stack or doing anything, check the suspend hook.
  // This can throw.
  EventHook::FunctionSuspendR(fp, child);

  // Await child and suspend the async function/generator. May throw.
  if (!func->isGenerator()) {
    // Async function.
    assert(!fp->sfp());
    frame_afwh(fp)->await(resumeOffset, child);
    vmStack().discard();
  } else {
    // Async generator.
    auto const gen = frame_async_generator(fp);
    auto const eagerResult = gen->await(resumeOffset, child);
    vmStack().discard();
    if (eagerResult) {
      // Eager execution => return AsyncGeneratorWaitHandle.
      assert(fp->sfp());
      vmStack().pushObjectNoRc(eagerResult);
    } else {
      // Resumed execution => return control to the scheduler.
      assert(!fp->sfp());
    }
  }

  // Grab caller info from ActRec.
  ActRec* sfp = fp->sfp();
  Offset soff = fp->m_soff;

  // Return control to the caller or scheduler.
  vmfp() = sfp;
  pc = sfp != nullptr ? sfp->func()->getEntry() + soff : nullptr;
}

// No idea
OPTBLD_INLINE void iopAwait(IOP_ARGS) {
  pc++;
  auto iters = decode_iva(pc);

  auto const wh = c_WaitHandle::fromCell(vmStack().topC());
  if (UNLIKELY(wh == nullptr)) {
    raise_error("Await on a non-WaitHandle");
    not_reached();
  } else if (wh->isSucceeded()) {
    cellSet(wh->getResult(), *vmStack().topC());
    return;
  } else if (UNLIKELY(wh->isFailed())) {
    throw Object(wh->getException());
  }

  if (vmfp()->resumed()) {
    // suspend resumed execution
    asyncSuspendR(pc);
  } else {
    // suspend eager execution
    asyncSuspendE(pc, iters);
  }
}

// No idea
OPTBLD_INLINE void iopCheckProp(IOP_ARGS) {
  pc++;
  auto propName = decode_litstr(pc);

  auto* cls = vmfp()->getClass();
  auto* propVec = cls->getPropData();
  cheng_assert(propVec!=nullptr);

  auto* ctx = arGetContextClass(vmfp());
  auto idx = ctx->lookupDeclProp(propName);

  auto& tv = (*propVec)[idx];
  if (tv.m_type != KindOfUninit) {
    vmStack().pushTrue();
  } else {
    vmStack().pushFalse();
  }
}

// No idea
OPTBLD_INLINE void iopInitProp(IOP_ARGS) {
  pc++;
  auto propName = decode_litstr(pc);
  auto propOp = decode_oa<InitPropOp>(pc);

  auto* cls = vmfp()->getClass();
  TypedValue* tv;

  auto* ctx = arGetContextClass(vmfp());
  auto* fr = vmStack().topC();

  switch (propOp) {
    case InitPropOp::Static:
      tv = cls->getSPropData(ctx->lookupSProp(propName));
      break;

    case InitPropOp::NonStatic: {
      auto* propVec = cls->getPropData();
      cheng_assert(propVec!=nullptr);
      Slot idx = ctx->lookupDeclProp(propName);
      tv = &(*propVec)[idx];
    } break;
  }

  cellDup(*fr, *tvToCell(tv));
  vmStack().popC();
}

// cheng-hack: 
// new bytecode for add_multi value
// this will change the multi-value *in-place*
OPTBLD_INLINE void iopAddMulti(IOP_ARGS) {
  pc++;
  Cell* reqnum = vmStack().topC();
  Cell* value = vmStack().indC(1);
  Cell* multi = vmStack().indC(2);

#ifdef CHENG_CHECK
  cheng_assert(multi->m_type == KindOfMulti || 
                multi->m_type == KindOfNull ||
                multi->m_type == KindOfUninit);
  cheng_assert(reqnum->m_type == KindOfInt64);
#endif

  START;

  if (LIKELY(multi->m_type == KindOfMulti)) {
    MultiVal* mv = multi->m_data.pmulti;
    mv->addValue(*value);
  } else if (multi->m_type == KindOfNull || multi->m_type == KindOfUninit) {
    *multi = MultiVal::makeMultiVal();
    multi->m_data.pmulti->addValue(*value);
  } else {
    std::cout << "ERROR: Cannot add a value to a non-multi-value variable!\n";
    cheng_assert(false);
  }
  vmStack().popC();
  vmStack().popC();
#ifdef CHENG_INS_DEBUG
  debug_log << "  After add_multi: \n" << vmStack().topC()->m_data.pmulti->dump("  ");
#endif

  END;
}

// support
OPTBLD_INLINE void iopStrlen(IOP_ARGS) {
  AS_ARITH;
  pc++;
  TypedValue* subj = vmStack().topTV();

  // cheng-hack:
  if (UNLIKELY(subj->m_type == KindOfMulti)) {
    START;
    TypedValue result = MultiVal::makeMultiVal();
    for (auto it : *subj->m_data.pmulti) {
      TypedValue ret;
      ret.m_type = KindOfInt64;
      if (LIKELY(IS_STRING_TYPE(it->m_type))) {
        int64_t ans = it->m_data.pstr->size();
        ret.m_data.num = ans;
      } else {
        Variant vret = HHVM_FN(strlen)(tvAsVariant(it));
        ret.m_data.num = vret.getInt64();
      }
      result.m_data.pmulti->addValue(ret);
    }
    // Optmize:
    // check if the results are the same, shrink them if true
    auto single = result.m_data.pmulti->shrinkToSingle();
    if (single == nullptr) {
      tvCopy(result, *subj);
    } else {
#ifdef CHENG_INS_DEBUG
      debug_log << "    Shrink the result to single: " << single->pretty() << "\n";
#endif
      tvCopy(*single, *subj);
      // free the read_result
      tvRefcountedDecRef(&result);
    }
    END;
  } else {
  // normal case
  if (LIKELY(IS_STRING_TYPE(subj->m_type))) {
    int64_t ans = subj->m_data.pstr->size();
    tvRefcountedDecRef(subj);
    subj->m_type = KindOfInt64;
    subj->m_data.num = ans;
  } else {
    Variant ans = HHVM_FN(strlen)(tvAsVariant(subj));
    tvAsVariant(subj) = ans;
  }
  }
}

// No idea
OPTBLD_INLINE void iopIncStat(IOP_ARGS) {
  pc++;
  auto counter = decode_iva(pc);
  auto value = decode_iva(pc);
  Stats::inc(Stats::StatCounter(counter), value);
}

// No idea
OPTBLD_INLINE void iopOODeclExists(IOP_ARGS) {
  pc++;
  auto subop = decode<OODeclExistsOp>(pc);

  TypedValue* aloadTV = vmStack().topTV();
  tvCastToBooleanInPlace(aloadTV);
  assert(aloadTV->m_type == KindOfBoolean);
  bool autoload = aloadTV->m_data.num;
  vmStack().popX();

  TypedValue* name = vmStack().topTV();
  tvCastToStringInPlace(name);
  assert(IS_STRING_TYPE(name->m_type));

  ClassKind kind;
  switch (subop) {
    case OODeclExistsOp::Class : kind = ClassKind::Class; break;
    case OODeclExistsOp::Trait : kind = ClassKind::Trait; break;
    case OODeclExistsOp::Interface : kind = ClassKind::Interface; break;
  }
  tvAsVariant(name) = Unit::classExists(name->m_data.pstr, autoload, kind);
}

// No idea
OPTBLD_INLINE void iopSilence(IOP_ARGS) {
  pc++;
  auto localId = decode_la(pc);
  auto subop = decode_oa<SilenceOp>(pc);

  switch (subop) {
    case SilenceOp::Start: {
      auto level = zero_error_level();
      TypedValue* local = frame_local(vmfp(), localId);
      local->m_type = KindOfInt64;
      local->m_data.num = level;
      break;
    }
    case SilenceOp::End: {
      TypedValue* oldTV = frame_local(vmfp(), localId);
      assert(oldTV->m_type == KindOfInt64);
      restore_error_level(oldTV->m_data.num);
      break;
    }
  }
}

std::string prettyStack(const std::string& prefix) {
  if (!vmfp()) return "__Halted";
  int offset = (vmfp()->m_func->unit() != nullptr)
               ? pcOff() : 0;
  auto begPrefix = prefix + "__";
  auto midPrefix = prefix + "|| ";
  auto endPrefix = prefix + "\\/";
  auto stack = vmStack().toString(vmfp(), offset, midPrefix);
  return begPrefix + "\n" + stack + endPrefix;
}

// callable from gdb
void DumpStack() {
  fprintf(stderr, "%s\n", prettyStack("").c_str());
}

// callable from gdb
void DumpCurUnit(int skip) {
  ActRec* fp = vmfp();
  Offset pc = fp->m_func->unit() ? pcOff() : 0;
  while (skip--) {
    fp = g_context->getPrevVMStateUNSAFE(fp, &pc);
  }
  if (fp == nullptr) {
    std::cout << "Don't have a valid fp\n";
    return;
  }

  printf("Offset = %d, in function %s\n", pc, fp->m_func->name()->data());
  Unit* u = fp->m_func->unit();
  if (u == nullptr) {
    std::cout << "Current unit is NULL\n";
    return;
  }
  printf("Dumping bytecode for %s(%p)\n", u->filepath()->data(), u);
  std::cout << u->toString();
}

// callable from gdb
void PrintTCCallerInfo() {
  VMRegAnchor _;
  ActRec* fp = vmfp();
  Unit* u = fp->m_func->unit();
  fprintf(stderr, "Called from TC address %p\n",
          mcg->getTranslatedCaller());
  std::cerr << u->filepath()->data() << ':'
            << u->getLineNumber(u->offsetOf(vmpc())) << '\n';
}

// thread-local cached coverage info
static __thread Unit* s_prev_unit;
static __thread int s_prev_line;

void recordCodeCoverage(PC pc) {
  Unit* unit = vmfp()->m_func->unit();
  assert(unit != nullptr);
  if (unit == SystemLib::s_nativeFuncUnit ||
      unit == SystemLib::s_nativeClassUnit ||
      unit == SystemLib::s_hhas_unit) {
    return;
  }
  int line = unit->getLineNumber(pcOff());
  assert(line != -1);

  if (unit != s_prev_unit || line != s_prev_line) {
    ThreadInfo* info = ThreadInfo::s_threadInfo.getNoCheck();
    s_prev_unit = unit;
    s_prev_line = line;
    const StringData* filepath = unit->filepath();
    assert(filepath->isStatic());
    info->m_coverage->Record(filepath->data(), line, line);
  }
}

void resetCoverageCounters() {
  s_prev_line = -1;
  s_prev_unit = nullptr;
}

static inline void
condStackTraceSep(Op opcode) {
  TRACE(3, "%s "
        "========================================"
        "========================================\n",
        opcodeToName(opcode));
}

#define COND_STACKTRACE(pfx)\
  ONTRACE(3, auto stack = prettyStack(pfx);\
          Trace::trace("%s\n", stack.c_str());)

/**
 * The interpOne methods save m_pc, m_fp, and m_sp ExecutionContext,
 * then call the iop<opcode> function.
 */
#define O(opcode, imm, push, pop, flags) \
void interpOne##opcode(ActRec* ar, Cell* sp, Offset pcOff) {            \
  interp_set_regs(ar, sp, pcOff);                                       \
  SKTRACE(5, SrcKey(liveFunc(), vmpc(), liveResumed()), "%40s %p %p\n", \
          "interpOne" #opcode " before (fp,sp)", vmfp(), vmsp());       \
  assert(*reinterpret_cast<const Op*>(vmpc()) == Op::opcode);           \
  Stats::inc(Stats::Instr_InterpOne ## opcode);                         \
  if (Trace::moduleEnabled(Trace::interpOne, 1)) {                      \
    static const StringData* cat = makeStaticString("interpOne");       \
    static const StringData* name = makeStaticString(#opcode);          \
    Stats::incStatGrouped(cat, name, 1);                                \
  }                                                                     \
  INC_TPC(interp_one)                                                   \
  /* Correct for over-counting in TC-stats. */                          \
  Stats::inc(Stats::Instr_TC, -1);                                      \
  condStackTraceSep(Op##opcode);                                        \
  COND_STACKTRACE("op"#opcode" pre:  ");                                \
  PC pc = vmpc();                                                       \
  assert(*reinterpret_cast<const Op*>(pc) == Op##opcode);               \
  ONTRACE(1, auto offset = vmfp()->m_func->unit()->offsetOf(pc);        \
          Trace::trace("op"#opcode" offset: %d\n", offset));            \
  iop##opcode(pc);                                                      \
  vmpc() = pc;                                                          \
  COND_STACKTRACE("op"#opcode" post: ");                                \
  condStackTraceSep(Op##opcode);                                        \
  /*
   * Only set regstate back to dirty if an exception is not
   * propagating.  If an exception is throwing, regstate for this call
   * is actually still correct, and we don't have information in the
   * fixup map for interpOne calls anyway.
   */ \
  tl_regState = VMRegState::DIRTY;                                      \
}
OPCODES
#undef O

InterpOneFunc interpOneEntryPoints[] = {
#define O(opcode, imm, push, pop, flags) &interpOne##opcode,
OPCODES
#undef O
};

template <bool breakOnCtlFlow>
void dispatchImpl() {
  static const void *optabDirect[] = {
#define O(name, imm, push, pop, flags) \
    &&Label##name,
    OPCODES
#undef O
  };
  static const void *optabDbg[] = {
#define O(name, imm, push, pop, flags) \
    &&LabelDbg##name,
    OPCODES
#undef O
  };
  static const void *optabCover[] = {
#define O(name, imm, push, pop, flags) \
    &&LabelCover##name,
    OPCODES
#undef O
  };
  assert(sizeof(optabDirect) / sizeof(const void *) == Op_count);
  assert(sizeof(optabDbg) / sizeof(const void *) == Op_count);
  const void **optab = optabDirect;
  bool collectCoverage = ThreadInfo::s_threadInfo->
    m_reqInjectionData.getCoverage();
  if (collectCoverage) {
    optab = optabCover;
  }
  DEBUGGER_ATTACHED_ONLY(optab = optabDbg);
  bool isCtlFlow = false;

#define DISPATCH() do {                                                 \
    if (breakOnCtlFlow && isCtlFlow) {                                  \
      ONTRACE(1,                                                        \
              Trace::trace("dispatch: Halt dispatch(%p)\n", \
                           vmfp()));                                      \
      return;                                                           \
    }                                                                   \
    Op op = *reinterpret_cast<const Op*>(pc);                           \
    COND_STACKTRACE("dispatch:                    ");                   \
    ONTRACE(1,                                                          \
            Trace::trace("dispatch: %d: %s\n", pcOff(),                 \
                         opcodeToName(op)));                            \
    goto *optab[uint8_t(op)];                                           \
} while (0)

  ONTRACE(1, Trace::trace("dispatch: Enter dispatch(%p)\n",
          vmfp()));
  PC pc = vmpc();
  DISPATCH();

#ifndef CHENG_INS_ONLY_DEBUG

#ifndef CHENG_TIME_EVAL
// original
#define O(name, imm, push, pop, flags)                        \
  LabelDbg##name:                                             \
    phpDebuggerOpcodeHook(pc);                                \
  LabelCover##name:                                           \
    if (collectCoverage) {                                    \
      recordCodeCoverage(pc);                                 \
    }                                                         \
  Label##name: {                                              \
    iop##name(pc);                                            \
    vmpc() = pc;                                              \
    if (breakOnCtlFlow) {                                     \
      isCtlFlow = instrIsControlFlow(Op::name);               \
      Stats::incOp(Op::name);                                 \
    }                                                         \
    if (UNLIKELY(!pc)) {                                      \
      DEBUG_ONLY const Op op = Op::name;                      \
      assert(op == OpRetC || op == OpRetV ||                  \
             op == OpAwait || op == OpCreateCont ||           \
             op == OpYield || op == OpYieldK ||               \
             op == OpNativeImpl);                             \
      vmfp() = nullptr;                                       \
      return;                                                 \
    }                                                         \
    DISPATCH();                                               \
  }


#else

#define O(name, imm, push, pop, flags)                        \
  LabelDbg##name:                                             \
    phpDebuggerOpcodeHook(pc);                                \
  LabelCover##name:                                           \
    if (collectCoverage) {                                    \
      recordCodeCoverage(pc);                                 \
    }                                                         \
  Label##name: {                                              \
    ins_counter_inc();\
    iop##name(pc);                                            \
    vmpc() = pc;                                              \
    if (breakOnCtlFlow) {                                     \
      isCtlFlow = instrIsControlFlow(Op::name);               \
      Stats::incOp(Op::name);                                 \
    }                                                         \
    if (UNLIKELY(!pc)) {                                      \
      DEBUG_ONLY const Op op = Op::name;                      \
      assert(op == OpRetC || op == OpRetV ||                  \
             op == OpAwait || op == OpCreateCont ||           \
             op == OpYield || op == OpYieldK ||               \
             op == OpNativeImpl);                             \
      vmfp() = nullptr;                                       \
      return;                                                 \
    }                                                         \
    DISPATCH();                                               \
  }
#endif // CHENG_TIME_EVAL

#else
  // here is define CHENG_INS_ONLY_DEBUG

#define O(name, imm, push, pop, flags)                        \
  LabelDbg##name:                                             \
    phpDebuggerOpcodeHook(pc);                                \
  LabelCover##name:                                           \
    if (collectCoverage) {                                    \
      recordCodeCoverage(pc);                                 \
    }                                                         \
  Label##name: {                                              \
    ins_counter_inc();\
    printFullStack("");\
    print_ins(#name);\
    iop##name(pc);                                            \
    vmpc() = pc;                                              \
    if (breakOnCtlFlow) {                                     \
      isCtlFlow = instrIsControlFlow(Op::name);               \
      Stats::incOp(Op::name);                                 \
    }                                                         \
    if (UNLIKELY(!pc)) {                                      \
      DEBUG_ONLY const Op op = Op::name;                      \
      assert(op == OpRetC || op == OpRetV ||                  \
             op == OpAwait || op == OpCreateCont ||           \
             op == OpYield || op == OpYieldK ||               \
             op == OpNativeImpl);                             \
      vmfp() = nullptr;                                       \
      return;                                                 \
    }                                                         \
    DISPATCH();                                               \
  }

#endif // CHENG_INS_ONLY_DEBUG

  OPCODES
#undef O
#undef DISPATCH
}

static void dispatch() {
  dispatchImpl<false>();
}

// We are about to go back to translated code, check whether we should
// stick with the interpreter. NB: if we've just executed a return
// from pseudomain, then there's no PC and no more code to interpret.
void switchModeForDebugger() {
  if (DEBUGGER_FORCE_INTR && (vmpc() != 0)) {
    throw VMSwitchMode();
  }
}

void dispatchBB() {
  if (Trace::moduleEnabled(Trace::dispatchBB)) {
    auto cat = makeStaticString("dispatchBB");
    auto name = makeStaticString(show(SrcKey(vmfp()->func(), vmpc(),
                                             vmfp()->resumed())));
    Stats::incStatGrouped(cat, name, 1);
  }
  dispatchImpl<true>();
  switchModeForDebugger();
}

void ExecutionContext::pushVMState(Cell* savedSP) {
  if (UNLIKELY(!vmfp())) {
    // first entry
    assert(m_nestedVMs.size() == 0);
    return;
  }

  TRACE(3, "savedVM: %p %p %p %p\n", vmpc(), vmfp(), vmFirstAR(), savedSP);
  auto& savedVM = m_nestedVMs.alloc_back();
  savedVM.pc = vmpc();
  savedVM.fp = vmfp();
  savedVM.firstAR = vmFirstAR();
  savedVM.sp = savedSP;
  savedVM.mInstrState = vmMInstrState();
  m_nesting++;

  if (debug && savedVM.fp &&
      savedVM.fp->m_func &&
      savedVM.fp->m_func->unit()) {
    // Some asserts and tracing.
    const Func* func = savedVM.fp->m_func;
    /* bound-check asserts in offsetOf */
    func->unit()->offsetOf(savedVM.pc);
    TRACE(3, "pushVMState: saving frame %s pc %p off %d fp %p\n",
          func->name()->data(),
          savedVM.pc,
          func->unit()->offsetOf(savedVM.pc),
          savedVM.fp);
  }
}

void ExecutionContext::popVMState() {
  if (UNLIKELY(m_nestedVMs.empty())) {
    // last exit
    vmfp() = nullptr;
    vmpc() = nullptr;
    vmFirstAR() = nullptr;

    return;
  }

  assert(m_nestedVMs.size() >= 1);

  VMState &savedVM = m_nestedVMs.back();
  vmpc() = savedVM.pc;
  vmfp() = savedVM.fp;
  vmFirstAR() = savedVM.firstAR;
  vmStack().top() = savedVM.sp;
  vmMInstrState() = savedVM.mInstrState;

  if (debug) {
    if (savedVM.fp &&
        savedVM.fp->m_func &&
        savedVM.fp->m_func->unit()) {
      const Func* func = savedVM.fp->m_func;
      (void) /* bound-check asserts in offsetOf */
        func->unit()->offsetOf(savedVM.pc);
      TRACE(3, "popVMState: restoring frame %s pc %p off %d fp %p\n",
            func->name()->data(),
            savedVM.pc,
            func->unit()->offsetOf(savedVM.pc),
            savedVM.fp);
    }
  }

  m_nestedVMs.pop_back();
  m_nesting--;

  TRACE(1, "Reentry: exit fp %p pc %p\n", vmfp(), vmpc());
}

static void threadLogger(const char* header, const char* msg,
                         const char* ending, void* data) {
  auto* ec = static_cast<ExecutionContext*>(data);
  ec->write(header);
  ec->write(msg);
  ec->write(ending);
  ec->flush();
}

void ExecutionContext::requestInit() {
  assert(SystemLib::s_unit);
  assert(SystemLib::s_nativeFuncUnit);
  assert(SystemLib::s_nativeClassUnit);

  EnvConstants::requestInit(smart_new<EnvConstants>());
  VarEnv::createGlobal();
  vmStack().requestInit();
  ObjectData::resetMaxId();
  ResourceData::resetMaxId();
  mcg->requestInit();

  if (RuntimeOption::EvalJitEnableRenameFunction) {
    assert(SystemLib::s_anyNonPersistentBuiltins);
  }

  /*
   * The normal case for production mode is that all builtins are
   * persistent, and every systemlib unit is accordingly going to be
   * merge only.
   *
   * However, if we have rename_function generally enabled, or if any
   * builtin functions were specified as interceptable at
   * repo-generation time, we'll actually need to merge systemlib on
   * every request because some of the builtins will not be marked
   * persistent.
   */
  if (UNLIKELY(SystemLib::s_anyNonPersistentBuiltins)) {
    SystemLib::s_unit->merge();
    Extension::MergeSystemlib();
    if (SystemLib::s_hhas_unit) SystemLib::s_hhas_unit->merge();
    SystemLib::s_nativeFuncUnit->merge();
    SystemLib::s_nativeClassUnit->merge();
  } else {
    // System units are merge only, and everything is persistent.
    assert(SystemLib::s_unit->isEmpty());
    assert(!SystemLib::s_hhas_unit || SystemLib::s_hhas_unit->isEmpty());
    assert(SystemLib::s_nativeFuncUnit->isEmpty());
    assert(SystemLib::s_nativeClassUnit->isEmpty());
  }

  profileRequestStart();

  MemoryProfile::startProfiling();
  MM().setObjectTracking(false);

#ifdef DEBUG
  Class* cls = NamedEntity::get(s_stdclass.get())->clsList();
  assert(cls);
  assert(cls == SystemLib::s_stdclassClass);
#endif

  if (Logger::UseRequestLog) Logger::SetThreadHook(&threadLogger, this);
}

void ExecutionContext::requestExit() {
  MemoryProfile::finishProfiling();

  // cheng-hack: when leaving close the debug log
  flush_clock_cpu_time();
  thread_end();
#ifdef CHENG_INS_ONLY_DEBUG
  closeDebugLog();
#endif
#ifdef CHENG_TIME_EVAL
  STOP_SW(req_time);
  t_mtx.lock();
  std::ofstream otf1("/tmp/veri/php_runtime.log", std::ofstream::app);
  otf1 << GET_TIME(req_time) << ",";
  otf1.close();
  std::ofstream otf2("/tmp/veri/multi_runtime.log", std::ofstream::app);
  otf2 << GET_TIME(multi_time) << ",";
  otf2.close();
  std::ofstream otf3("/tmp/veri/ins_count.log", std::ofstream::app);
  otf3 << ins_counter << ",";
  otf3.close();
  std::ofstream otf4("/tmp/veri/multi_ins_count.log", std::ofstream::app);
  otf4 << GET_COUNT(multi_time) << ",";
  otf4.close();
  std::ofstream otf5("/tmp/veri/db_runtime.log", std::ofstream::app);
  otf5 << GET_TIME(db_query) << ",";
  otf5.close();


  std::ofstream prof_of_1("/tmp/veri/db_dedup.log", std::ofstream::app);
  prof_of_1 << GET_TIME(db_dedup_time) << ",";
  prof_of_1.close();
  std::ofstream prof_of_2("/tmp/veri/db_trans.log", std::ofstream::app);
  prof_of_2 << GET_TIME(db_trans_time) << ",";
  prof_of_2.close();
  std::ofstream prof_of_3("/tmp/veri/apc_time.log", std::ofstream::app);
  prof_of_3 << GET_TIME(apc_time) << ",";
  prof_of_3.close();
  std::ofstream prof_of_4("/tmp/veri/opmap_time.log", std::ofstream::app);
  prof_of_4 << GET_TIME(opmap_time) << ",";
  prof_of_4.close();


  t_mtx.unlock();
  RESET_SW(req_time);
  RESET_SW(multi_time);
  RESET_SW(db_query);

  RESET_SW(db_dedup_time);
  RESET_SW(db_trans_time);
  RESET_SW(apc_time);
  RESET_SW(opmap_time);

  START_SW(req_time); // may be running multiple times
  START_SW(multi_time);
  // FIXME: this popVMState() is not actually the real end!
  // but cannot find one so far.
  ins_counter = 0;
#endif
#ifdef CHENG_CYCLE_WAR_TUNING
  std::ofstream ins_of("/tmp/veri/cw_ins_time.log", std::ofstream::app);
  ins_of << GET_TIME(ins_time) << "|" << GET_COUNT(ins_time) << "\n";
  ins_of.close();
  std::ofstream ins_of_1("/tmp/veri/cw_ins_time1.log", std::ofstream::app);
  ins_of_1 << GET_TIME(ins_time_1) << "|" << GET_COUNT(ins_time_1) << "\n";
  ins_of_1.close();
  std::ofstream ins_of_2("/tmp/veri/cw_ins_time2.log", std::ofstream::app);
  ins_of_2 << GET_TIME(ins_time_2) << "|" << GET_COUNT(ins_time_2) << "\n";
  ins_of_2.close();
  std::ofstream ins_of_3("/tmp/veri/cw_ins_time3.log", std::ofstream::app);
  ins_of_3 << GET_TIME(ins_time_3) << "|" << GET_COUNT(ins_time_3) << "\n";
  ins_of_3.close();
  std::ofstream ins_of_4("/tmp/veri/cw_ins_time4.log", std::ofstream::app);
  ins_of_4 << GET_TIME(ins_time_4) << "|" << GET_COUNT(ins_time_4) << "\n";
  ins_of_4.close();
#endif

  manageAPCHandle();
  syncGdbState();
  mcg->requestExit();
  vmStack().requestExit();
  profileRequestEnd();
  EventHook::Disable();
  EnvConstants::requestExit();

  if (m_globalVarEnv) {
    smart_delete(m_globalVarEnv);
    m_globalVarEnv = 0;
  }

  if (!m_lastError.isNull()) {
    clearLastError();
  }

  if (Logger::UseRequestLog) Logger::SetThreadHook(nullptr, nullptr);
}

///////////////////////////////////////////////////////////////////////////////
}
