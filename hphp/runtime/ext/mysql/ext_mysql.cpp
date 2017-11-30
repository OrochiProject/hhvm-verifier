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
#include "hphp/runtime/ext/mysql/ext_mysql.h"

#include <netinet/in.h>
#include <netdb.h>
#include <poll.h>

#include <folly/ScopeGuard.h>
#include <folly/String.h>

#include "hphp/runtime/base/builtin-functions.h"
#include "hphp/runtime/base/comparisons.h"
#include "hphp/runtime/ext/mysql/mysql_common.h"
#include "hphp/runtime/ext/mysql/mysql_stats.h"
#include "hphp/system/systemlib.h"

#include "hphp/runtime/ext/std/ext_std_variable.h"
#include "vector"
#include "algorithm"
#include "runtime/ext/std/sql-parser.h"
#include "hphp/runtime/vm/yastopwatch.h"
#include "fstream"

namespace HPHP {
///////////////////////////////////////////////////////////////////////////////

using std::string;

///////////////////////////////////////////////////////////////////////////////

static Variant HHVM_FUNCTION(mysql_connect,
  const String& server,
  const String& username,
  const String& password,
  bool new_link,
  int client_flags,
  int connect_timeout_ms,
  int query_timeout_ms) {
  return php_mysql_do_connect(
    server,
    username,
    password,
    "",
    client_flags,
    false, false,
    connect_timeout_ms,
    query_timeout_ms
  );
}

static Variant HHVM_FUNCTION(mysql_connect_with_db,
  const String& server,
  const String& username,
  const String& password,
  const String& database,
  bool new_link,
  int client_flags,
  int connect_timeout_ms,
  int query_timeout_ms) {
  return php_mysql_do_connect(
    server,
    username,
    password,
    database,
    client_flags,
    false, false,
    connect_timeout_ms,
    query_timeout_ms
  );
}

static Variant HHVM_FUNCTION(mysql_pconnect,
  const String& server,
  const String& username,
  const String& password,
  int client_flags,
  int connect_timeout_ms,
  int query_timeout_ms) {
  return php_mysql_do_connect(
    server,
    username,
    password,
    "",
    client_flags,
    true, false,
    connect_timeout_ms,
    query_timeout_ms
  );
}

static Variant HHVM_FUNCTION(mysql_pconnect_with_db,
  const String& server,
  const String& username,
  const String& password,
  const String& database,
  int client_flags,
  int connect_timeout_ms,
  int query_timeout_ms) {
  return php_mysql_do_connect(
    server,
    username,
    password,
    database,
    client_flags,
    true, false,
    connect_timeout_ms,
    query_timeout_ms
  );
}

static bool HHVM_FUNCTION(mysql_set_timeout, int query_timeout_ms /* = -1 */,
                   const Variant& link_identifier /* = null */) {
  MySQL::SetDefaultReadTimeout(query_timeout_ms);
  return true;
}

static String HHVM_FUNCTION(mysql_escape_string,
                            const String& unescaped_string) {
  String new_str((size_t)unescaped_string.size() * 2 + 1, ReserveString);
  unsigned long new_len = mysql_escape_string(new_str.bufferSlice().begin(),
                                    unescaped_string.data(),
                                    unescaped_string.size());
  new_str.shrink(new_len);
  return new_str;
}

static Variant HHVM_FUNCTION(mysql_real_escape_string,
                             const String& unescaped_string,
                             const Variant& link_identifier /* = null */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (conn) {
    String new_str((size_t)unescaped_string.size() * 2 + 1, ReserveString);
    unsigned long new_len = mysql_real_escape_string(conn,
                                      new_str.bufferSlice().begin(),
                                      unescaped_string.data(),
                                      unescaped_string.size());

    new_str.shrink(new_len);
    return new_str;
  }
  return false;
}

static String HHVM_FUNCTION(mysql_get_client_info) {
  return String(mysql_get_client_info(), CopyString);
}

static Variant HHVM_FUNCTION(mysql_set_charset, const String& charset,
                   const Variant& link_identifier /* = uninit_null() */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return init_null();
  return !mysql_set_character_set(conn, charset.data());
}

static Variant HHVM_FUNCTION(mysql_ping,
                   const Variant& link_identifier /* = uninit_null() */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return init_null();
  return !mysql_ping(conn);
}
static Variant HHVM_FUNCTION(mysql_client_encoding,
                      const Variant& link_identifier /* = uninit_null() */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return false;
  return String(mysql_character_set_name(conn), CopyString);
}
static bool HHVM_FUNCTION(mysql_close,
                   const Variant& link_identifier /* = uninit_null() */) {
  return MySQL::CloseConn(link_identifier);
}

static Variant HHVM_FUNCTION(mysql_errno,
                      const Variant& link_identifier /* = null */) {
  auto mySQL = MySQL::Get(link_identifier);
  if (!mySQL) {
    raise_warning("supplied argument is not a valid MySQL-Link resource");
    return false;
  }
  MYSQL *conn = mySQL->get();
  if (conn) {
    return (int64_t)mysql_errno(conn);
  }
  if (mySQL->m_last_error_set) {
    return (int64_t)mySQL->m_last_errno;
  }
  return false;
}

static Variant HHVM_FUNCTION(mysql_error,
                      const Variant& link_identifier /* = null */) {
  auto mySQL = MySQL::Get(link_identifier);
  if (!mySQL) {
    raise_warning("supplied argument is not a valid MySQL-Link resource");
    return false;
  }
  MYSQL *conn = mySQL->get();
  if (conn) {
    return String(mysql_error(conn), CopyString);
  }
  if (mySQL->m_last_error_set) {
    return String(mySQL->m_last_error);
  }
  return false;
}

static Variant HHVM_FUNCTION(mysql_warning_count,
                      const Variant& link_identifier /* = null */) {
  auto mySQL = MySQL::Get(link_identifier);
  if (!mySQL) {
    raise_warning("supplied argument is not a valid MySQL-Link resource");
    return false;
  }
  MYSQL *conn = mySQL->get();
  if (conn) {
    return (int64_t)mysql_warning_count(conn);
  }
  return false;
}

static Variant HHVM_FUNCTION(mysql_get_host_info,
                      const Variant& link_identifier /* = uninit_null() */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return false;
  return String(mysql_get_host_info(conn), CopyString);
}
static Variant HHVM_FUNCTION(mysql_get_proto_info,
                      const Variant& link_identifier /* = uninit_null() */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return false;
  return (int64_t)mysql_get_proto_info(conn);
}
static Variant HHVM_FUNCTION(mysql_get_server_info,
                      const Variant& link_identifier /* = uninit_null() */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return false;
  return String(mysql_get_server_info(conn), CopyString);
}
static Variant HHVM_FUNCTION(mysql_info,
                      const Variant& link_identifier /* = uninit_null() */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return false;
  return String(mysql_info(conn), CopyString);
}
static Variant HHVM_FUNCTION(mysql_insert_id,
                      const Variant& link_identifier /* = uninit_null() */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return false;
  return static_cast<int64_t>(mysql_insert_id(conn));
}
static Variant HHVM_FUNCTION(mysql_stat,
                      const Variant& link_identifier /* = uninit_null() */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return false;
  return String(mysql_stat(conn), CopyString);
}
static Variant HHVM_FUNCTION(mysql_thread_id,
                      const Variant& link_identifier /* = uninit_null() */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return false;
  return (int64_t)mysql_thread_id(conn);
}

static bool HHVM_FUNCTION(mysql_select_db, const String& db,
                   const Variant& link_identifier /* = uninit_null() */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return false;
  return mysql_select_db(conn, db.data()) == 0;
}

static Variant HHVM_FUNCTION(mysql_affected_rows,
                      const Variant& link_identifier /* = uninit_null() */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return false;
  return static_cast<int64_t>(mysql_affected_rows(conn));
}

///////////////////////////////////////////////////////////////////////////////
// query functions

static Variant HHVM_FUNCTION(mysql_query, const String& query,
                      const Variant& link_identifier /* = null */) {
  return php_mysql_do_query_and_get_result(query, link_identifier, true, false);
}

static Variant HHVM_FUNCTION(mysql_multi_query, const String& query,
                      const Variant& link_identifier /* = null */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (conn == nullptr) {
    return false;
  }
  auto mySQL = MySQL::Get(link_identifier);
  if (!mySQL->m_multi_query &&
      !mysql_set_server_option(conn, MYSQL_OPTION_MULTI_STATEMENTS_ON)) {
    mySQL->m_multi_query = true;
  }

  if (mysql_real_query(conn, query.data(), query.size())) {
#ifdef HHVM_MYSQL_TRACE_MODE
    if (RuntimeOption::EnableHipHopSyntax) {
      raise_notice("runtime/ext_mysql: failed executing [%s] [%s]",
                   query.data(), mysql_error(conn));
    }
#endif
    // turning this off clears the errors
    if (!mysql_set_server_option(conn, MYSQL_OPTION_MULTI_STATEMENTS_OFF)) {
      mySQL->m_multi_query = false;
    }
    return false;
  }
  return true;
}

static int64_t HHVM_FUNCTION(mysql_next_result,
                  const Variant& link_identifier /* = null */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (conn == nullptr) {
    return 2006 /* CR_SERVER_GONE_ERROR */;
  }
  if (!mysql_more_results(conn)) {
    raise_strict_warning("There is no next result set. "
      "Please, call mysql_more_results() to check "
      "whether to call this function/method");
  }
  return mysql_next_result(conn);
}

static bool HHVM_FUNCTION(mysql_more_results,
                   const Variant& link_identifier /* = null */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (conn == nullptr) {
    return false;
  }
  return mysql_more_results(conn);
}

static Variant HHVM_FUNCTION(mysql_fetch_result,
                      const Variant& link_identifier /* = null */) {
    MYSQL *conn = MySQL::GetConn(link_identifier);
    if (conn == nullptr) {
      return false;
    }
    MYSQL_RES *mysql_result;

    mysql_result = mysql_store_result(conn);

    if (!mysql_result) {
      if (mysql_field_count(conn) > 0) {
        raise_warning("Unable to save result set");
        return false;
      }
      return true;
    }

    return Variant(makeSmartPtr<MySQLResult>(mysql_result));
}

static Variant HHVM_FUNCTION(mysql_unbuffered_query, const String& query,
                      const Variant& link_identifier /* = null */) {
  return php_mysql_do_query_and_get_result(
    query,
    link_identifier,
    false,
    false
  );
}

static Variant HHVM_FUNCTION(mysql_list_dbs,
                      const Variant& link_identifier /* = null */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return false;
  MYSQL_RES *res = mysql_list_dbs(conn, nullptr);
  if (!res) {
    raise_warning("Unable to save MySQL query result");
    return false;
  }
  return Variant(makeSmartPtr<MySQLResult>(res));
}

static Variant HHVM_FUNCTION(mysql_list_tables, const String& database,
                      const Variant& link_identifier /* = null */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return false;
  if (mysql_select_db(conn, database.data())) {
    return false;
  }
  MYSQL_RES *res = mysql_list_tables(conn, nullptr);
  if (!res) {
    raise_warning("Unable to save MySQL query result");
    return false;
  }
  return Variant(makeSmartPtr<MySQLResult>(res));
}

static Variant HHVM_FUNCTION(mysql_list_processes,
                      const Variant& link_identifier /* = null */) {
  MYSQL *conn = MySQL::GetConn(link_identifier);
  if (!conn) return false;
  MYSQL_RES *res = mysql_list_processes(conn);
  if (!res) {
    raise_warning("Unable to save MySQL query result");
    return false;
  }
  return Variant(makeSmartPtr<MySQLResult>(res));
}

///////////////////////////////////////////////////////////////////////////////
// async

/* The mysql_*_nonblocking calls are Facebook extensions to
   libmysqlclient; for now, protect with an ifdef.  Once open sourced,
   the client will be detectable via its own ifdef. */
#ifdef FACEBOOK

static Variant HHVM_FUNCTION(mysql_async_connect_start,
                      const String& server /* = null_string */,
                      const String& username /* = null_string */,
                      const String& password /* = null_string */,
                      const String& database /* = null_string */) {
  return php_mysql_do_connect(server, username, password, database,
                              0, false, true, 0, 0);
}

static bool HHVM_FUNCTION(mysql_async_connect_completed,
                   const Variant& link_identifier) {
  auto mySQL = MySQL::Get(link_identifier);
  if (!mySQL) {
    raise_warning("supplied argument is not a valid MySQL-Link resource");
    return true;
  }

  MYSQL* conn = mySQL->get();
  if (conn->async_op_status != ASYNC_OP_CONNECT) {
    // Don't warn if we're in UNSET state (ie between queries, etc)
    if (conn->async_op_status != ASYNC_OP_UNSET) {
      raise_warning("runtime/ext_mysql: no pending async connect in progress");
    }
    return true;
  }

  int error = 0;
  auto status = mysql_real_connect_nonblocking_run(conn, &error);
  return status == NET_ASYNC_COMPLETE;
}

static bool HHVM_FUNCTION(mysql_async_query_start,
                   const String& query, const Variant& link_identifier) {
  MYSQL* conn = MySQL::GetConn(link_identifier);
  if (!conn) {
    return false;
  }

  if (conn->async_op_status != ASYNC_OP_UNSET) {
    raise_warning("runtime/ext_mysql: attempt to run async query while async "
                  "operation already pending");
    return false;
  }
  Variant ret = php_mysql_do_query_and_get_result(query, link_identifier,
                                                  true, true);
  if (ret.getRawType() != KindOfBoolean) {
    raise_warning("runtime/ext_mysql: unexpected return from "
                  "php_mysql_do_query_and_get_result");
    return false;
  }
  return ret.toBooleanVal();
}

static Variant HHVM_FUNCTION(mysql_async_query_result,
                      const Variant& link_identifier) {
  auto mySQL = MySQL::Get(link_identifier);
  if (!mySQL) {
    raise_warning("supplied argument is not a valid MySQL-Link resource");
    return Variant(Variant::NullInit());
  }
  MYSQL* conn = mySQL->get();
  if (!conn || (conn->async_op_status != ASYNC_OP_QUERY &&
                conn->async_op_status != ASYNC_OP_UNSET)) {
    raise_warning("runtime/ext_mysql: attempt to check query result when query "
                  "not executing");
    return Variant(Variant::NullInit());
  }

  int error = 0;
  auto status = mysql_real_query_nonblocking(
    conn, mySQL->m_async_query.c_str(), mySQL->m_async_query.size(), &error);

  if (status != NET_ASYNC_COMPLETE) {
    return Variant(Variant::NullInit());
  }

  if (error) {
    return Variant(Variant::NullInit());
  }

  mySQL->m_async_query.clear();

  MYSQL_RES* mysql_result = mysql_use_result(conn);
  auto r = makeSmartPtr<MySQLResult>(mysql_result);
  r->setAsyncConnection(mySQL);
  return Variant(std::move(r));
}

static bool HHVM_FUNCTION(mysql_async_query_completed, const Resource& result) {
  auto const res = result.getTyped<MySQLResult>(true, true);
  return !res || res->get() == nullptr;
}

static Variant HHVM_FUNCTION(mysql_async_fetch_array, const Resource& result,
                                               int result_type /* = 1 */) {
  if ((result_type & PHP_MYSQL_BOTH) == 0) {
    throw_invalid_argument("result_type: %d", result_type);
    return false;
  }

  MySQLResult* res = php_mysql_extract_result(result);
  if (!res) {
    return false;
  }

  MYSQL_RES* mysql_result = res->get();
  if (!mysql_result) {
    raise_warning("invalid parameter to mysql_async_fetch_array");
    return false;
  }

  MYSQL_ROW mysql_row = nullptr;
  int status = mysql_fetch_row_nonblocking(mysql_result, &mysql_row);
  // Last row, or no row yet available.
  if (status != NET_ASYNC_COMPLETE) {
    return false;
  }
  if (mysql_row == nullptr) {
    res->close();
    return false;
  }

  unsigned long *mysql_row_lengths = mysql_fetch_lengths(mysql_result);
  if (!mysql_row_lengths) {
    return false;
  }

  mysql_field_seek(mysql_result, 0);

  Array ret;
  MYSQL_FIELD *mysql_field;
  int i;
  for (mysql_field = mysql_fetch_field(mysql_result), i = 0; mysql_field;
       mysql_field = mysql_fetch_field(mysql_result), i++) {
    Variant data;
    if (mysql_row[i]) {
      data = mysql_makevalue(String(mysql_row[i], mysql_row_lengths[i],
                                    CopyString), mysql_field);
    }
    if (result_type & PHP_MYSQL_NUM) {
      ret.set(i, data);
    }
    if (result_type & PHP_MYSQL_ASSOC) {
      ret.set(String(mysql_field->name, CopyString), data);
    }
  }

  return ret;
}

// This function takes an array of arrays, each of which is of the
// form array($dbh, ...).  The only thing that matters in the inner
// arrays is the first element being a MySQL instance.  It then
// procedes to block for up to 'timeout' seconds, waiting for the
// first actionable descriptor(s), which it then returns in the form
// of the original arrays passed in.  The intention is the caller
// would include other information they care about in the tail of the
// array so they can decide how to act on the
// potentially-now-queryable descriptors.
//
// This function is a poor shadow of how the async library can be
// used; for more complex cases, we'd use libevent and share our event
// loop with other IO operations such as memcache ops, thrift calls,
// etc.  That said, this function is reasonably efficient for most use
// cases.
static Variant HHVM_FUNCTION(mysql_async_wait_actionable, const Array& items,
                                                   double timeout) {
  size_t count = items.size();
  if (count == 0 || timeout < 0) {
    return empty_array();
  }

  struct pollfd* fds = (struct pollfd*)calloc(count, sizeof(struct pollfd));
  SCOPE_EXIT { free(fds); };

  // Walk our input, determine what kind of poll() operation is
  // necessary for the descriptor in question, and put an entry into
  // fds.
  int nfds = 0;
  for (ArrayIter iter(items); iter; ++iter) {
    Array entry = iter.second().toArray();
    if (entry.size() < 1) {
      raise_warning("element %d did not have at least one entry",
                   nfds);
      return empty_array();
    }

    auto rsrc = entry.rvalAt(0).toResource();
    auto conn = rsrc.getTyped<MySQLResource>()->mysql()->get();

    if (conn->async_op_status == ASYNC_OP_UNSET) {
      raise_warning("runtime/ext_mysql: no pending async operation in "
                    "progress");
      return empty_array();
    }

    pollfd* fd = &fds[nfds++];
    fd->fd = mysql_get_file_descriptor(conn);
    if (conn->net.async_blocking_state == NET_NONBLOCKING_READ) {
      fd->events = POLLIN;
    } else {
      fd->events = POLLOUT;
    }
    fd->revents = 0;
  }

  // The poll itself; either the timeout is hit or one or more of the
  // input fd's is ready.
  int timeout_millis = static_cast<long>(timeout * 1000);
  int res = poll(fds, nfds, timeout_millis);
  if (res == -1) {
    raise_warning("unable to poll [%d]: %s", errno,
                  folly::errnoStr(errno).c_str());
    return empty_array();
  }

  // Now just find the ones that are ready, and copy the corresponding
  // arrays from our input array into our return value.
  Array ret = Array::Create();
  nfds = 0;
  for (ArrayIter iter(items); iter; ++iter) {
    Array entry = iter.second().toArray();
    if (entry.size() < 1) {
      raise_warning("element %d did not have at least one entry",
                   nfds);
      return empty_array();
    }

    auto rsrc = entry.rvalAt(0).toResource();
    auto conn = rsrc.getTyped<MySQLResource>()->mysql()->get();

    pollfd* fd = &fds[nfds++];
    if (fd->fd != mysql_get_file_descriptor(conn)) {
      raise_warning("poll returned events out of order wtf");
      continue;
    }
    if (fd->revents != 0) {
      ret.append(iter.second());
    }
  }

  return ret;
}

static int64_t HHVM_FUNCTION(mysql_async_status,
                             const Variant& link_identifier) {
  auto mySQL = MySQL::Get(link_identifier);
  if (!mySQL || !mySQL->get()) {
    raise_warning("supplied argument is not a valid MySQL-Link resource");
    return -1;
  }

  return mySQL->get()->async_op_status;
}

#endif

///////////////////////////////////////////////////////////////////////////////
// row operations


// cheng-hack: because of query clustering, need to handle when resource has duplication
static bool HHVM_FUNCTION(multi_mysql_data_seek, const Variant& var, const Variant& row) {
  cheng_assert(row.m_type != KindOfMulti);
  cheng_assert(var.m_type == KindOfMulti);

  // FIXME: ugly copy/paste code
  // compare whether the results are duplicated
  std::set<ResourceData*> uniq_res;

  int meet_non_res = -1; // -1: uninitialized, 0: no null_resource, 1: all null_resource
  for (auto it : *var.m_data.pmulti) {
    if (it->m_type != KindOfResource) {
      cheng_assert(meet_non_res == 1 || meet_non_res == -1);
      meet_non_res = 1;
    } else {
      cheng_assert(meet_non_res == 0 || meet_non_res == -1);
      meet_non_res = 0; // I meet a good resource
      uniq_res.insert(it->m_data.pres);
    }
  }

  // handle non_res first and if so return
  if (meet_non_res == 1) {
    MySQLResult *res = php_mysql_extract_result(null_resource);
    if (res == nullptr) return false;
    return res->seekRow(row.asInt64Val());
  }

  // we do have some resources
  TypedValue res_template;
  res_template.m_type = KindOfResource;

  bool is_first = true;
  bool first_ret = true;
  for (auto it : uniq_res) {
    res_template.m_data.pres = it;
    Resource result = tvAsVariant(&res_template).toResource();
    MySQLResult *res = php_mysql_extract_result(result);

    if (is_first) {
      if (res == nullptr) {
        first_ret = false;
      } else {
        first_ret = res->seekRow(row.asInt64Val());
      }
      is_first = false;
    } else {
      if (res == nullptr) {
        cheng_assert(first_ret == false);
      } else {
        bool ret = res->seekRow(row.asInt64Val());
        cheng_assert(ret == first_ret);
      }
    }
  }
  return first_ret; 
}

static bool HHVM_FUNCTION(mysql_data_seek, const Resource& result, int row) {
  MySQLResult *res = php_mysql_extract_result(result);
  if (res == nullptr) return false;

  return res->seekRow(row);
}

// cheng-hack: since query cluster, the multi-value resources can have duplicated ones 
static Variant HHVM_FUNCTION(multi_mysql_fetch_array, const Variant& var,
                                         const Variant& result_type /* = 3 */) {
  cheng_assert(result_type.m_type != KindOfMulti);
  cheng_assert(var.m_type == KindOfMulti);


  // cheng-hack:
  // db deduplication may generate an multivalue with many duplicated resources
  // find the unique ones and add the seq_num to a map
  TypedValue multi_ret = MultiVal::makeMultiVal();
  std::map<void*, Variant> res2properties;

  // check whether the resource is null_resource
  int meet_non_res = -1; // -1: uninitialized, 0: no null_resource, 1: all null_resource
  for (int i=0; i<var.m_data.pmulti->valSize(); i++) {
    auto it = var.m_data.pmulti->getByVal(i);

    if (it->m_type != KindOfResource) {
      cheng_assert(meet_non_res == 1 || meet_non_res == -1);
      meet_non_res = 1;
    } else {
      cheng_assert(meet_non_res == 0 || meet_non_res == -1);
      meet_non_res = 0; // I meet a good resource

      // collect the unique resource and their seq_num
      void* ptr = (void*) it->m_data.pres;
      if (res2properties.find(ptr) == res2properties.end()) {
        // find a new Resource
        auto var = tvAsVariant(it);
        Resource result = var.isResource() ? var.toResource() : null_resource;
        Variant properties = php_mysql_fetch_hash(result, result_type.asInt64Val());
        res2properties[ptr] = properties;

        multi_ret.m_data.pmulti->addValue(properties);
      } else {
        // find an existing resource
        multi_ret.m_data.pmulti->addValue(res2properties[ptr]);
      }
    }
  }

  // if all are null_resource
  if (meet_non_res == 1) {
    return php_mysql_fetch_hash(null_resource, result_type.asInt64Val());
  }

  cheng_assert(meet_non_res == 0);
  // construct the multivalue for properties
  return tvAsVariant(&multi_ret);
}

static Variant HHVM_FUNCTION(mysql_fetch_array, const Resource& result,
                                         int result_type /* = 3 */) {
  return php_mysql_fetch_hash(result, result_type);
}

static Variant HHVM_FUNCTION(mysql_fetch_object,
                      const Variant& var_result,
                      const String& class_name /* = "stdClass" */,
                      const Variant& params /* = null */) {

  Resource result = var_result.isResource() ? var_result.toResource()
                                            : null_resource;
  Variant properties = php_mysql_fetch_hash(result, PHP_MYSQL_ASSOC);
  if (!same(properties, false)) {
    Object obj;

    const auto paramsArray = params.isArray()
      ? params.asCArrRef()
      : Array();

    // We need to create an object without initialization (constructor call),
    // and set the fetched fields as dynamic properties on the object prior
    // calling the constructor.
    obj = create_object_only(class_name);

    // Set the fields.
    obj->o_setArray(properties.toArray());

    // And finally initialize the object by calling the constructor.
    obj = init_object(class_name, paramsArray, obj.get());

    return obj;
  }

  return false;
}


// cheng-hack: tmp debug
static std::ofstream debug_db_log;
static void
writetolog(std::string msg) {
  debug_db_log.open("/tmp/db_debug.log", std::ofstream::out | std::ofstream::app);
  debug_db_log << msg << "\n";
  debug_db_log.close();
}



// cheng-hack: used for do not call __set multiple times
extern thread_local bool allow_mv_in_con;
static Variant HHVM_FUNCTION(multi_mysql_fetch_object,
                      const Variant& var_result,
                      const String& class_name /* = "stdClass" */,
                      const Variant& params /* = null */) {
  bool var_multi = (var_result.m_type == KindOfMulti);
  bool is_multi_param = (params.m_type == KindOfMulti);

  if (!var_multi && !is_multi_param) {
    return HHVM_FN(mysql_fetch_object)(var_result, class_name, params);
  }

//writetolog("------------fetch_object---------");
//std::cout << "---------" << HHVM_FN(print_r)(var_result, true).toString().toCppString() << "\n";
//std::cout << "------------end_fetch_object---------\n";

  int size;
  if (var_multi) {
    size = var_result.m_data.pmulti->valSize();
  } else if (is_multi_param) {
    size = params.m_data.pmulti->valSize();
  } else {
    cheng_assert(false);
  }

  if (var_multi) {
    cheng_assert(var_result.m_data.pmulti->getType() == KindOfResource);
  } else {
    cheng_assert(var_result.m_type == KindOfResource);
  }

  if (is_multi_param) {
    cheng_assert(params.m_data.pmulti->valSize() == size);
    cheng_assert(params.m_data.pmulti->getType() == KindOfArray);
  }

  sptr< std::vector<ObjectData*> > obj_arr = 
               std::make_shared< std::vector<ObjectData*> >();

  // if the var_result is multi:
  if (var_multi) {

  // cheng-hack:
  // db deduplication may generate an multivalue with many duplicated resources
  // find the unique ones and add the seq_num to a map

  std::vector<Variant> properties_list;
  std::map<void*, Variant> res2properties;
  for (int i=0; i<size; i++) {
    auto it = var_result.m_data.pmulti->getByVal(i);

    // find the ptr
    void* ptr = (void*) 0;
    if (it->m_type == KindOfResource) {
      ptr = (void*) it->m_data.pres;
    } else {
      std::cout << "The multival is not a rsource, we don't have a ptr \n";
      cheng_assert(false);
    }

    if (res2properties.find(ptr) == res2properties.end()) {
      // find a new Resource
      auto var = tvAsVariant(it);
      Resource result = var.isResource() ? var.toResource() // var.toResource() may consume the resource?
                        : null_resource;
      Variant properties = php_mysql_fetch_hash(result, PHP_MYSQL_ASSOC);
      res2properties[ptr] = properties;

      if (same(properties, false)) {
        return false;
      }

      properties_list.push_back(properties);
    } else {
      // find an existing resource
      properties_list.push_back(res2properties[ptr]);
    }
  }

  for (int i=0; i< size; i++) {
    // cheng-hack: original logic to fetch result from Resource
    // however, because of the db dedup, there might be duplicated resources
    // so we move the php_mysql_fetch_hash() ahead
/*
    auto it = var_result.m_data.pmulti->getByVal(i);
    auto var = tvAsVariant(it);

    Resource result = var.isResource() ? var.toResource()
      : null_resource;
    Variant properties = php_mysql_fetch_hash(result, PHP_MYSQL_ASSOC);
    if (same(properties, false)) {
      return false;
    }
*/
    // cheng-hack: next line replace the above chunk
    Variant properties = properties_list[i]; 

    Object obj;

    // We need to create an object without initialization (constructor call),
    // and set the fetched fields as dynamic properties on the object prior
    // calling the constructor.
    obj = create_object_only(class_name);

    // Set the fields.
    obj->o_setArray(properties.toArray());

    // collect the obj
    obj_arr->push_back(obj.get());
    obj->incRefCount();
  }
  } else {
    cheng_assert(is_multi_param);

    Resource result = var_result.isResource() ? var_result.toResource()
      : null_resource;
    Variant properties = php_mysql_fetch_hash(result, PHP_MYSQL_ASSOC);

    if (same(properties, false)) {
      return false;
    }


    // loop here
    for (int i=0; i< size; i++) {
      Object obj = create_object_only(class_name);
      obj->o_setArray(properties.toArray());
      obj_arr->push_back(obj.get());
      obj->incRefCount();
    }
  }

  //for(auto it: *obj_arr) {
  //  auto txt = HHVM_FN(print_r)(Variant(it), true);
  //  std::cout << txt.toString().toCppString() << "\n";
  //}

  Array paramsArray;
  TypedValue multi_arr_list;
  if (!is_multi_param) {
    paramsArray = params.isArray()
      ? params.asCArrRef()
      : Array();
  } else {
    multi_arr_list = MultiVal::invertTransferArray(params);
    paramsArray = tvAsVariant(&multi_arr_list).asCArrRef();
  }

  // And finally initialize the object by calling the constructor.
  //auto obj = init_object(class_name, paramsArray, obj.get());
  auto obj_new_arr = init_object_multi(class_name, paramsArray, obj_arr);
  auto multi_obj = genMultiVal(obj_new_arr);

  // free unused
  tvRefcountedDecRef(&multi_arr_list);
  for (auto it : *obj_new_arr) {
    it->decRefCount();
  }

  //HHVM_FN(print_r)(Variant(obj));

  return tvAsVariant(&multi_obj); 
}

Variant HHVM_FUNCTION(mysql_fetch_lengths, const Resource& result) {
  MySQLResult *res = php_mysql_extract_result(result);
  if (res == nullptr) return false;

  if (res->isLocalized()) {
    if (!res->isRowReady()) return false;

    Array ret;
    for (int i = 0; i < res->getFieldCount(); i++) {
      MySQLFieldInfo *info = res->getFieldInfo(i);
      if (info->type == MYSQL_TYPE_YEAR) {
        // special case for years, because of leading zeros
        ret.set(i, info->length);
      } else {
        // convert fields back to Strings to get lengths
        ret.set(i, res->getField(i).toString().length());
      }
    }
    return ret;
  }

  MYSQL_RES *mysql_result = res->get();
  unsigned long *lengths = mysql_fetch_lengths(mysql_result);
  if (!lengths) {
    return false;
  }

  Array ret;
  int num_fields = mysql_num_fields(mysql_result);
  for (int i = 0; i < num_fields; i++) {
    ret.set(i, (int)lengths[i]);
  }
  return ret;
}

static Variant HHVM_FUNCTION(mysql_result, const Resource& result, int row,
                                    const Variant& field /* = 0 */) {
  MySQLResult *res = php_mysql_extract_result(result);
  if (res == nullptr) return false;

  MYSQL_RES *mysql_result = nullptr;
  MYSQL_ROW sql_row = nullptr;
  unsigned long *sql_row_lengths = nullptr;

  if (res->isLocalized()) {
    if (!res->seekRow(row)) return false;
    if (!res->fetchRow()) return false;
  } else {
    mysql_result = res->get();
    if (row < 0 || row >= (int)mysql_num_rows(mysql_result)) {
      raise_warning("Unable to jump to row %d on MySQL result index %d",
                      row, result->o_getId());
      return false;
    }
    mysql_data_seek(mysql_result, row);

    sql_row = mysql_fetch_row(mysql_result);
    if (!sql_row) {
      return false;
    }
    sql_row_lengths = mysql_fetch_lengths(mysql_result);
    if (!sql_row_lengths) {
      return false;
    }
  }

  int field_offset = 0;
  if (!field.isNull()) {
    if (field.isString()) {
      String sfield = field.toString();
      const char *tmp = strchr(sfield.data(), '.');
      String table_name, field_name;
      if (tmp) {
        int pos = tmp - sfield.data();
        table_name = sfield.substr(0, pos);
        field_name = sfield.substr(pos + 1);
      } else {
        field_name = sfield;
      }

      int i = 0;
      bool found = false;
      res->seekField(0);
      while (i < res->getFieldCount()) {
        MySQLFieldInfo *info = res->getFieldInfo(i);
        if ((table_name.empty() || table_name.same(info->table)) &&
            field_name.same(info->name)) {
          field_offset = i;
          found = true;
          break;
        }
        i++;
      }
      if (!found) { /* no match found */
        raise_warning("%s%s%s not found in MySQL result index %d",
                        table_name.data(), (table_name.empty() ? "" : "."),
                        field_name.data(), result->o_getId());
        return false;
      }
    } else {
      field_offset = field.toInt32();
      if (field_offset < 0 ||
          field_offset >= (int)res->getFieldCount()) {
        raise_warning("Bad column offset specified");
        return false;
      }
    }
  }

  if (res->isLocalized()) {
    Variant f = res->getField(field_offset);
    if (!f.isNull()) {
      return f.toString();
    }
  } else {
    if (sql_row[field_offset]) {
      return String(sql_row[field_offset], sql_row_lengths[field_offset],
                    CopyString);
    }
  }
  return init_null();
}

///////////////////////////////////////////////////////////////////////////////
// result functions

Variant HHVM_FUNCTION(mysql_num_fields, const Resource& result) {
  MySQLResult *res = php_mysql_extract_result(result);
  if (res) {
    return res->getFieldCount();
  }
  return false;
}

Variant HHVM_FUNCTION(mysql_num_rows, const Resource& result) {
  MySQLResult *res = php_mysql_extract_result(result);
  if (res) {
    return res->getRowCount();
  }
  return false;
}


// cheng-hack: because of query clustering
static bool HHVM_FUNCTION(multi_mysql_free_result, const Variant& var) {
  bool multiresult = (var.m_type == KindOfMulti);

  if (multiresult) {
    // compare whether the results are duplicated
    std::set<ResourceData*> uniq_res;

    int meet_non_res = -1; // -1: uninitialized, 0: no null_resource, 1: all null_resource
    for (auto it : *var.m_data.pmulti) {
      if (it->m_type != KindOfResource) {
        cheng_assert(meet_non_res == 1 || meet_non_res == -1);
        meet_non_res = 1;
      } else {
        cheng_assert(meet_non_res == 0 || meet_non_res == -1);
        meet_non_res = 0; // I meet a good resource
        uniq_res.insert(it->m_data.pres);
      }
    }

    // handle non_res first and if so return
    if (meet_non_res == 1) {
      MySQLResult *res = php_mysql_extract_result(null_resource);
      if (res) {
        res->close();
        return true;
      }
      return false;
    }

    // we do have some resources
    TypedValue res_template;
    res_template.m_type = KindOfResource;

    bool is_first = true;
    bool first_ret = true;
    for (auto it : uniq_res) {
      res_template.m_data.pres = it;
      Resource result = tvAsVariant(&res_template).toResource();
      MySQLResult *res = php_mysql_extract_result(result);

      if (is_first) {
        if (res) {
          res->close();
          first_ret = true;
        } else {
          first_ret = false;
        }
        is_first = false;
      } else {
        if (res) {
          res->close();
          cheng_assert(first_ret == true);
        } else {
          cheng_assert(first_ret == false);
        }
      }
    }
    return first_ret;
  } else {
    Resource result = var.isResource() ? var.toResource() : null_resource;
    // from orignal mysql_free_result:
    MySQLResult *res = php_mysql_extract_result(result);
    if (res) {
      res->close();
      return true;
    }
    return false;
  }
}


static bool HHVM_FUNCTION(mysql_free_result, const Resource& result) {
  MySQLResult *res = php_mysql_extract_result(result);
  if (res) {
    res->close();
    return true;
  }
  return false;
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

/**
 * cheng-hack: Borrow from member-operations.h
 * SetElem helper with Array base and Int64 key
 */
static inline ArrayData*
SetElemArrayPre_keyint(ArrayData* a,
                                  int64_t key,
                                  Cell* value,
                                  bool copy) {
  return a->set(key, cellAsCVarRef(*value), copy);
}

/**
 * cheng-hack: Borrow from member-operations.h
 * SetElem when base is an Array
 */
static inline ArrayData*
SetElemArray(ArrayData* a, int64_t key,
                         Cell* value) {
  //ArrayData* a = base->m_data.parr;
  bool copy = (a->hasMultipleRefs())
    || (value->m_type == KindOfArray && value->m_data.parr == a);

  auto* newData = SetElemArrayPre_keyint(a, key, value, copy);

  //arrayRefShuffle<true>(a, newData, base);
  // cheng-hack: following is the translate of above
  if (newData != a) {
    newData->incRefCount();
    a->decRefAndRelease();
  }
  return newData;
}

// defined in bytecode.cpp
#define MAX_IN_TXN 10000
extern int search_opmap(int rid, int opnum, int type);

static std::vector<int64_t>
genQueryTimeStamp(const Variant& req_no, int64_t opnum, int64_t query_num) {
  std::vector<int64_t> tss;
  // single req_no
  if (req_no.m_type == KindOfInt64) {
    // get timestamp from (rid, opnum) pair
    int rid = req_no.m_data.num;
    // both read and write can be here!
    int64_t seq_num = search_opmap(rid, opnum, TYPE_NONE);
    int64_t ts = seq_num * MAX_IN_TXN + query_num;
    tss.push_back(ts);
  } else if (req_no.m_type == KindOfMulti) {
    cheng_assert(req_no.m_data.pmulti->getType() == KindOfInt64);

    // get timestamp from multiple (rid, opnum) pairs
    for (auto it : *req_no.m_data.pmulti) {
      int rid = it->m_data.num;
      int64_t seq_num = search_opmap(rid, opnum, TYPE_NONE);
      int64_t ts = seq_num * MAX_IN_TXN + query_num;
      tss.push_back(ts);
    }
  } else {
    // should never be here
    cheng_assert(false);
  }
  return tss;
}

static inline bool
checkQuerySelect(const Variant& query) {
  if (query.m_type != KindOfMulti) {
    auto str = (query.toString().toCppString()).substr(0,6);
    std::transform(str.begin(), str.end(), str.begin(), ::tolower);
    if (str == "select") {
      return true;
    }
    return false;
  } else {
    int ret_true = -1;
    for (auto it : *query.m_data.pmulti) {
      auto str = (tvAsVariant(it).toString().toCppString()).substr(0,6);
      std::transform(str.begin(), str.end(), str.begin(), ::tolower);
      if (ret_true == -1) {
        ret_true = (str == "select");
      } else {
        cheng_assert(ret_true == (str == "select"));
      }
    }
    return ret_true;
  }
}

static inline bool
checkQueryShow(const Variant& query) {
  if (query.m_type != KindOfMulti) {
    auto str = (query.toString().toCppString()).substr(0,4);
    std::transform(str.begin(), str.end(), str.begin(), ::tolower);
    return (str == "show");
  } else {
    auto str = (tvAsVariant(query.m_data.pmulti->getByVal(0)).toString().toCppString()).substr(0,4);
    std::transform(str.begin(), str.end(), str.begin(), ::tolower);
    return (str == "show");
  }
}

extern Variant HHVM_METHOD(mysqli, hh_get_connection, int64_t state);
extern Variant HHVM_METHOD(mysqli, hh_get_result, bool use_store);
extern Variant HHVM_METHOD(mysqli, hh_real_query, const String& query);


//------------------------------
//--------cheng-hack------------
//------------------------------

uint64_t search_table_update_log (std::string tname, uint64_t cur_ts);
static inline bool
noTableUpdate(std::vector<std::string> tnames, std::vector<int64_t> tss) {
  bool run_once = true;
  for (auto name : tnames) {
    bool first = true;
    uint64_t last_ts = 0;
    for (auto cur_ts : tss) {
      auto tmp_last = search_table_update_log(name, cur_ts);
      if (first) {
        first = false;
        last_ts = tmp_last;
      } else {
        run_once = (last_ts == tmp_last);
      }
//if (!run_once) std::cout << "    fail on dedup, table[" << name << "], cur_ts=" << cur_ts 
//<< ", other_last=" << last_ts << ", cur_last=" << tmp_last << "\n";
      if (!run_once) break;
    }
    if (!run_once) break;
  }
  return run_once;
}

// we have to guarantee that this returned string
// includes all the last modification time for all the tables
static inline std::string 
lastModifiedTssStr(std::vector<std::string> tnames, int64_t cur_ts) {
  std::string last_tss_str;
  for (auto name : tnames) {
    auto tmp_last = search_table_update_log(name, cur_ts);
    // find the oldest modification timestamp
    last_tss_str += std::to_string(tmp_last)+"-";
  }
  return last_tss_str;
}

// cheng-hack:
// Inputs:
//   query: can be either single-string or multi-value string
//   req_no: can be either one int or multi-value int
//   mysqli_obj: is $this in mysqli
// Output:
//     an array of query results, should use "new mysql_result($result, MYSQLI_STORE_RESULT)"
//     to construct the return value of mysqli->query().

extern bool table_update_log_loaded;
// NOTE: ASSUMPTION: the resultmode == MYSQLI_STORE_RESULT
//static Variant HHVM_FUNCTION(ttdb_query, const Variant& query, const Variant& req_no,
//                             const int64_t op_num, const int64_t query_num, const Variant& mysqli_obj) {

// stop watch for db query
extern struct __stopwatch__ __SW(db_dedup_time);
extern enum __stopwatch__source__ __SOURCE(db_dedup_time); 
extern enum __stopwatch__type__ __TYPE(db_dedup_time);

extern struct __stopwatch__ __SW(db_trans_time);
extern enum __stopwatch__source__ __SOURCE(db_trans_time); 
extern enum __stopwatch__type__ __TYPE(db_trans_time);


// cheng-hack: this is an optimization for tracing table name
// query => table_name vector
std::map<std::string, std::vector<std::string> >  table_name_cache;

static inline std::vector<std::string>
get_table_names_from_cache(std::string sql) {
  if (table_name_cache.find(sql) == table_name_cache.end()) {
    table_name_cache[sql] = extractTableNames(sql);
  }
  return table_name_cache[sql];
}


// NOTE: ASSUMPTION: the resultmode == MYSQLI_STORE_RESULT
static Variant HHVM_FUNCTION(ttdb_query, const Variant& query, const Variant& req_no,
                             const int64_t op_num, const int64_t query_num, const Variant& mysqli_obj) {
//static Variant xxx_ttdb_query (const Variant& query, const Variant& req_no,
//                             const int64_t op_num, const int64_t query_num, const Variant& mysqli_obj) {
  // (1) genQueryTimeStamp
  // (2) if query is update, just return
  // (3) rewrite the select query
  // (4) do real query
  // (5) collect result and return
  cheng_assert(table_update_log_loaded); // we only support this now
  auto tss = genQueryTimeStamp(req_no, op_num, query_num);
  bool is_read = checkQuerySelect(query);

  {
    // dump the other query to file
    std::ofstream of("/tmp/veri/sql-verify-2.log", std::ofstream::app);
    int size = tss.size();
    for (int i=0 ; i<size; i++) {
      std::string str_q;
      if (query.m_type == KindOfMulti) {
        str_q = tvAsVariant(query.m_data.pmulti->getByVal(i)).toString().toCppString();
      } else {
        str_q = query.toString().toCppString();
      }
      of << tss[i] << "#&#" << str_q << "|]|";
    }
    of.close();
  }

  bool is_show = checkQueryShow(query);
  cheng_assert(!is_show);

  // (2) check if select
  if (!is_read) {
    // FIXME: failure handling needed
    return true;
  }

  // (3) rewrite the select query 
  bool is_multi_req = (req_no.m_type == KindOfMulti);
  // query_cluster[sql][ts] => [seqnum1, seqnum2...]
  std::map<std::string, std::map<std::string, std::vector<int> > > query_cluster;

  //START_SW(db_dedup_time);
  if (UNLIKELY(!is_multi_req)) {
    // this is single request,
    // query_cluster will be [query][ts]=>[0]
    cheng_assert(tss.size() == 1);
    auto q_str = query.toString().toCppString();
    query_cluster[q_str] = std::map<std::string, std::vector<int> >();
    query_cluster[q_str]["single"] = std::vector<int>();
    query_cluster[q_str]["single"].push_back(0);
  } else {
    cheng_assert(is_multi_req);
    bool is_multi_query = (query.m_type == KindOfMulti);

    for (int i=0; i<tss.size(); i++) {
      auto cur_q = (is_multi_query
                    ? tvAsVariant(query.m_data.pmulti->getByVal(i)).toString().toCppString()
                    : query.toString().toCppString());

      // fit this query into query_cluster[cur_q][last_modified_tss_str]
      auto table_names = get_table_names_from_cache(cur_q); // FIXME: here might be a lot of redundency
      auto last_m_tss_str = lastModifiedTssStr(table_names, tss[i]);

      if (query_cluster.find(cur_q) == query_cluster.end()) {
        // new query
        query_cluster[cur_q] = std::map<std::string, std::vector<int> >();
      }
      if (query_cluster[cur_q].find(last_m_tss_str) == query_cluster[cur_q].end()) {
        // new ts
        query_cluster[cur_q][last_m_tss_str] = std::vector<int>();
      }
      query_cluster[cur_q][last_m_tss_str].push_back(i);
    }
  }
  // in below, all the queries belong to one query_cluster[query][last_tss_str] can be dedup
  //STOP_SW(db_dedup_time);

  // (4) do query & collect results
  ArrayData* ret_array = staticEmptyArray();
  bool ret_bool = false;
  // -1: uninitialized
  // 0: get null
  // 1: get 2
  // 2: get others
  int has_ret = -1;

  // we need:
  //  -- query_cluster (with sql as key, and ts_map as value)
  //  -- tss [timestamp for each query, same seqnum in query_cluster) 
  for (auto it : query_cluster) {
    auto orig_sql = it.first;
    auto ts_map = it.second;

    for (auto ts_it : ts_map) {
      // current queries should have (1) same query and (2) same last_ts, can be dedup
      auto seq_vec = ts_it.second;
      auto first_ts = tss[seq_vec[0]]; // get the ts from first sql
      START_SW(db_trans_time);
      auto tt_sql = rewriteOptSelect(orig_sql, first_ts);
      STOP_SW(db_trans_time);
      // do once for all
      auto q_rst = HHVM_MN(mysqli, hh_real_query)(mysqli_obj.m_data.pobj, Variant(tt_sql).toString());

      if (has_ret == -1) {
        if (q_rst.m_type == KindOfInt64 && q_rst.m_data.num == 2) {
          has_ret = 1;
        } else if (q_rst.m_type == KindOfNull) {
          has_ret = 0;
        } else if (q_rst.m_type == KindOfInt64) {
          has_ret = 2;
          ret_bool = (q_rst.m_data.num != 0);
        } else {
          // shouldn't be other value!
          cheng_assert(false);
        }
      }
      if (has_ret == 1) {
        cheng_assert(q_rst.m_data.num == 2);
        auto result = HHVM_MN(mysqli, hh_get_result)(mysqli_obj.m_data.pobj, true);
        // all the query in this query cluster should have the same value
        // but this is resource!!!!
        for (auto seqnum : seq_vec) {
          ret_array = SetElemArray(ret_array, seqnum, result.asTypedValue());
        }
        cheng_assert(result.m_type == KindOfResource);
      } else if (has_ret == 2) {
        cheng_assert( (q_rst.m_data.num !=0 ) == ret_bool);
      } else {
        cheng_assert(q_rst.m_type == KindOfNull);
      }

    } // end iter of ts_map
  } // end iter of query_cluster

  if (has_ret == 0) {
    return init_null();
  } else if (has_ret == 1) {
    return ret_array;
  } else if (has_ret == 2) {
    return ret_bool;
  } else {
    cheng_assert(false);
    return 0;
  }
}


static Variant HHVM_FUNCTION(ttdb_query_mysqli_result, const Variant& query, const Variant& req_no,
                             const int64_t op_num, const int64_t query_number, const Variant& mysqli_obj) {
  START_SW(db_dedup_time);
  auto ret_arr = HHVM_FN(ttdb_query)(query, req_no, op_num, query_number, mysqli_obj);
  if (is_bool(ret_arr)) {
    STOP_SW(db_dedup_time);
    return ret_arr;
  }
  cheng_assert(is_array(ret_arr));
  int size = ret_arr.asCArrRef().size();
  cheng_assert(size > 0);

  if (size == 1) {
    // only one result
    auto obj = create_object_only("mysqli_result");
    // The argument of the mysqli_result is "a resource" from "hh_get_result"
    // we accidentally can use the return array for this purpose
    const auto paramsArray = ret_arr.asCArrRef(); 
    obj = init_object("mysqli_result", paramsArray, obj.get());
    STOP_SW(db_dedup_time);
    return obj;
  } else {
    // create multiple obj
    sptr< std::vector<ObjectData*> > obj_arr = 
      std::make_shared< std::vector<ObjectData*> >();
    for (int i = 0; i < size; i++) {
      auto obj = create_object_only("mysqli_result");
      obj->incRefCount();
      obj_arr->push_back(obj.get());
    }
    // construct the parameter list
    TypedValue multi_arg = MultiVal::makeMultiVal();
    for (int i = 0; i < size; i++) {
      multi_arg.m_data.pmulti->addValueNoInc(ret_arr.asArrRef()[i]);
    }
    ArrayData* params = staticEmptyArray();
    params = SetNewElemArray(params, &multi_arg);
    const auto paramsArray = Variant(params).asCArrRef();

    // call constructor in one turn
    auto obj_new_arr = init_object_multi("mysqli_result", paramsArray, obj_arr);
    auto multi_obj = genMultiVal(obj_new_arr);

    // free unused
    for (auto it : *obj_new_arr) {
      it->decRefCount();
    }
    STOP_SW(db_dedup_time);
    return tvAsVariant(&multi_obj);
  }
}

// cheng-hack:
// Inputs:
//     query: should be either multi-value string or single string as sql query
//     tss:   multi-value int as timestamp for rewriting
//     mysqli_obj: the object of mysqli, used as $this
// Output:
//     an array of query results, should use "new mysql_result($result, MYSQLI_STORE_RESULT)"
//     to construct the return value of mysqli->query().

static Variant HHVM_FUNCTION(ttdb_multi_query, const Variant& query, const Variant& req_no,
                             const int64_t op_num, const int64_t query_number, const Variant& mysqli_obj) {
  always_assert(query.m_type == KindOfMulti 
    || query.m_type == KindOfStaticString || query.m_type == KindOfString);
  always_assert(req_no.m_type == KindOfMulti);
  always_assert(mysqli_obj.m_type == KindOfObject);

  if (!checkQuerySelect(query)) {
    return true;
  }
  
  // do the multi_query, and then return myqli_result as multi_val
  bool multi_q = (query.m_type == KindOfMulti);
  if (multi_q) {
    cheng_assert(query.m_data.pmulti->valSize()
                  == req_no.m_data.pmulti->valSize());
  }

  // construct new query
  std::stringstream ss;
  //ss << "START TRANSACTION;";
  int size = 1;
  if (multi_q) {
    size = query.m_data.pmulti->valSize();
  }

  for (int i = 0; i < size; i++) {
    const Variant curq = (multi_q ? tvAsVariant(query.m_data.pmulti->getByVal(i)) : query);
    int64_t rid = (multi_q ? tvAsVariant(req_no.m_data.pmulti->getByVal(i)).asInt64Val() : req_no.asInt64Val());
    auto ttq = HHVM_FN(rewrite_select_sql)(curq, rid , op_num, query_number);
    cheng_assert(ttq.m_type == KindOfString);
    ss << ttq.toString().toCppString() << ";";
  }
  //ss << "COMMIT;";

  // do multi_query
  auto link = HHVM_MN(mysqli, hh_get_connection)(mysqli_obj.m_data.pobj, 2);
  auto ret = HHVM_FN(mysql_multi_query)(ss.str(), link);
  cheng_assert(ret.m_type == KindOfBoolean && ret.m_data.num != 0);

  // get result and generate multi-value
  ArrayData* ret_array = staticEmptyArray();
  bool next = false;
  do {
    auto result = HHVM_MN(mysqli, hh_get_result)(mysqli_obj.m_data.pobj, true);
    ret_array = SetNewElemArray(ret_array, result.asTypedValue());
    cheng_assert(result.m_type == KindOfResource);
    next = ! HHVM_FN(mysql_next_result)(link);
  } while(next);

  return ret_array;
}
///////////////////////////////////////////////////////////////////////////////
// field info

static Variant HHVM_FUNCTION(mysql_fetch_field, const Resource& result,
                                         int field /* = -1 */) {
  MySQLResult *res = php_mysql_extract_result(result);
  if (res == nullptr) return false;

  if (field != -1) {
    if (!res->seekField(field)) return false;
  }
  MySQLFieldInfo *info;
  if (!(info = res->fetchFieldInfo())) return false;

  Object obj(SystemLib::AllocStdClassObject());
  obj->o_set("name",         info->name);
  obj->o_set("table",        info->table);
  obj->o_set("def",          info->def);
  obj->o_set("max_length",   (int)info->max_length);
  obj->o_set("not_null",     IS_NOT_NULL(info->flags)? 1 : 0);
  obj->o_set("primary_key",  IS_PRI_KEY(info->flags)? 1 : 0);
  obj->o_set("multiple_key", info->flags & MULTIPLE_KEY_FLAG? 1 : 0);
  obj->o_set("unique_key",   info->flags & UNIQUE_KEY_FLAG? 1 : 0);
  obj->o_set("numeric",      IS_NUM(info->type)? 1 : 0);
  obj->o_set("blob",         IS_BLOB(info->flags)? 1 : 0);
  obj->o_set("type",         php_mysql_get_field_name(info->type));
  obj->o_set("unsigned",     info->flags & UNSIGNED_FLAG? 1 : 0);
  obj->o_set("zerofill",     info->flags & ZEROFILL_FLAG? 1 : 0);
  return obj;
}


// cheng-hack: due to query clustering, resources may duplicate
static Variant HHVM_FUNCTION(multi_mysql_fetch_field, const Variant& var,
                                         const Variant& field /* = -1 */) {
  cheng_assert(var.m_type == KindOfMulti);
  cheng_assert(field.m_type != KindOfMulti);

  // check the uniq resources and reserve the seq_num
  // FIXME: ugly copy paste code
  TypedValue multi_ret = MultiVal::makeMultiVal();
  std::map<void*, Variant> res2properties;

  for (int i=0; i<var.m_data.pmulti->valSize(); i++) {
    auto it = var.m_data.pmulti->getByVal(i);

    // find the ptr
    void* ptr = (void*) 0;
    if (it->m_type == KindOfResource) {
      ptr = (void*) it->m_data.pres;
    } else {
      std::cout << "The multival is not a rsource, we don't have a ptr \n";
      cheng_assert(false);
    }

    if (res2properties.find(ptr) == res2properties.end()) {
      // find a new Resource
      auto var = tvAsVariant(it);
      Resource result = var.isResource() ? var.toResource() : null_resource;
      auto obj = HHVM_FN(mysql_fetch_field)(result, field.asInt64Val());
      // put it into the map
      res2properties[ptr] = obj;
      // add it to the multi_ret
      // FIXME: doe we need clone??
      multi_ret.m_data.pmulti->addValue(obj);
    } else {
      // find an existing resource
      multi_ret.m_data.pmulti->addValue(res2properties[ptr]);
    }
  }

  return tvAsVariant(&multi_ret);
}



// cheng-hack: query clustering may make the resource duplicated
static bool HHVM_FUNCTION(multi_mysql_field_seek, const Variant& var, const Variant& field) {
  cheng_assert(var.m_type == KindOfMulti);
  cheng_assert(field.m_type != KindOfMulti);

  // FIXME: ugly copy/paste code
  // compare whether the results are duplicated
  std::set<ResourceData*> uniq_res;

  int meet_non_res = -1; // -1: uninitialized, 0: no null_resource, 1: all null_resource
  for (auto it : *var.m_data.pmulti) {
    if (it->m_type != KindOfResource) {
      cheng_assert(meet_non_res == 1 || meet_non_res == -1);
      meet_non_res = 1;
    } else {
      cheng_assert(meet_non_res == 0 || meet_non_res == -1);
      meet_non_res = 0; // I meet a good resource
      uniq_res.insert(it->m_data.pres);
    }
  }

  // handle non_res first and if so return
  if (meet_non_res == 1) {
    MySQLResult *res = php_mysql_extract_result(null_resource);
    if (res == nullptr) return false;
    return res->seekField(field.asInt64Val());
  }

  // we do have some resources
  TypedValue res_template;
  res_template.m_type = KindOfResource;

  bool is_first = true;
  bool first_ret = true;
  for (auto it : uniq_res) {
    res_template.m_data.pres = it;
    Resource result = tvAsVariant(&res_template).toResource();
    MySQLResult *res = php_mysql_extract_result(result);

    if (is_first) {
      if (res == nullptr) {
        first_ret = false;
      } else {
        first_ret = res->seekField(field.asInt64Val());
      }
      is_first = false;
    } else {
      if (res == nullptr) {
        cheng_assert(first_ret == false);
      } else {
        bool ret = res->seekRow(field.asInt64Val());
        cheng_assert(ret == first_ret);
      }
    }
  }
  return first_ret; 
}

static bool HHVM_FUNCTION(mysql_field_seek, const Resource& result, int field) {
  MySQLResult *res = php_mysql_extract_result(result);
  if (res == nullptr) return false;
  return res->seekField(field);
}

static Variant HHVM_FUNCTION(mysql_field_name, const Resource& result,
                                               int field) {
  return php_mysql_field_info(result, field, PHP_MYSQL_FIELD_NAME);
}
static Variant HHVM_FUNCTION(mysql_field_table, const Resource& result,
                                                int field) {
  return php_mysql_field_info(result, field, PHP_MYSQL_FIELD_TABLE);
}
static Variant HHVM_FUNCTION(mysql_field_len, const Resource& result,
                                              int field) {
  return php_mysql_field_info(result, field, PHP_MYSQL_FIELD_LEN);
}
static Variant HHVM_FUNCTION(mysql_field_type, const Resource& result,
                                               int field) {
  return php_mysql_field_info(result, field, PHP_MYSQL_FIELD_TYPE);
}
static Variant HHVM_FUNCTION(mysql_field_flags, const Resource& result,
                                                int field) {
  return php_mysql_field_info(result, field, PHP_MYSQL_FIELD_FLAGS);
}

///////////////////////////////////////////////////////////////////////////////

const StaticString s_MYSQL_ASSOC("MYSQL_ASSOC");
const StaticString s_MYSQL_BOTH("MYSQL_BOTH");
const StaticString s_MYSQL_CLIENT_COMPRESS("MYSQL_CLIENT_COMPRESS");
const StaticString s_MYSQL_CLIENT_IGNORE_SPACE("MYSQL_CLIENT_IGNORE_SPACE");
const StaticString s_MYSQL_CLIENT_INTERACTIVE("MYSQL_CLIENT_INTERACTIVE");
const StaticString s_MYSQL_CLIENT_SSL("MYSQL_CLIENT_SSL");
const StaticString s_MYSQL_NUM("MYSQL_NUM");
const StaticString s_ASYNC_OP_INVALID("ASYNC_OP_INVALID");
const StaticString s_ASYNC_OP_UNSET("ASYNC_OP_UNSET");
const StaticString s_ASYNC_OP_CONNECT("ASYNC_OP_CONNECT");
const StaticString s_ASYNC_OP_QUERY("ASYNC_OP_QUERY");

void mysqlExtension::moduleInit() {
  HHVM_FE(mysql_connect);
  HHVM_FE(mysql_connect_with_db);
  HHVM_FE(mysql_pconnect);
  HHVM_FE(mysql_pconnect_with_db);
  HHVM_FE(mysql_set_timeout);
  HHVM_FE(mysql_escape_string);
  HHVM_FE(mysql_real_escape_string);
  HHVM_FE(mysql_get_client_info);
  HHVM_FE(mysql_set_charset);
  HHVM_FE(mysql_ping);
  HHVM_FE(mysql_client_encoding);
  HHVM_FE(mysql_close);
  HHVM_FE(mysql_errno);
  HHVM_FE(mysql_error);
  HHVM_FE(mysql_warning_count);
  HHVM_FE(mysql_get_host_info);
  HHVM_FE(mysql_get_proto_info);
  HHVM_FE(mysql_get_server_info);
  HHVM_FE(mysql_info);
  HHVM_FE(mysql_insert_id);
  HHVM_FE(mysql_stat);
  HHVM_FE(mysql_thread_id);
  HHVM_FE(mysql_select_db);
  HHVM_FE(mysql_affected_rows);
  HHVM_FE(mysql_query);
  HHVM_FE(mysql_multi_query);
  HHVM_FE(ttdb_query); // cheng-hack
  HHVM_FE(ttdb_query_mysqli_result); // cheng-hack
  HHVM_FE(ttdb_multi_query); // cheng-hack
  HHVM_FE(mysql_next_result);
  HHVM_FE(mysql_more_results);
  HHVM_FE(mysql_fetch_result);
  HHVM_FE(mysql_unbuffered_query);
  HHVM_FE(mysql_list_dbs);
  HHVM_FE(mysql_list_tables);
  HHVM_FE(mysql_list_processes);
  HHVM_FE(mysql_data_seek);
  HHVM_FE(multi_mysql_data_seek); //cheng-hack
  HHVM_FE(mysql_fetch_array);
  HHVM_FE(multi_mysql_fetch_array); // cheng-hack
  HHVM_FE(mysql_fetch_object);
  HHVM_FE(multi_mysql_fetch_object); // cheng-hack
  HHVM_FE(mysql_fetch_lengths);
  HHVM_FE(mysql_result);
  HHVM_FE(mysql_num_fields);
  HHVM_FE(mysql_num_rows);
  HHVM_FE(mysql_free_result);
  HHVM_FE(multi_mysql_free_result); // cheng-hack
  HHVM_FE(mysql_fetch_field);
  HHVM_FE(mysql_field_seek);
  HHVM_FE(multi_mysql_field_seek); // cheng-hack
  HHVM_FE(mysql_field_name);
  HHVM_FE(mysql_field_table);
  HHVM_FE(mysql_field_len);
  HHVM_FE(mysql_field_type);
  HHVM_FE(mysql_field_flags);

  Native::registerConstant<KindOfInt64>(
    s_MYSQL_ASSOC.get(), PHP_MYSQL_ASSOC
  );
  Native::registerConstant<KindOfInt64>(
    s_MYSQL_BOTH.get(), PHP_MYSQL_BOTH
  );
  Native::registerConstant<KindOfInt64>(
    s_MYSQL_NUM.get(), PHP_MYSQL_NUM
  );
  Native::registerConstant<KindOfInt64>(
    s_MYSQL_CLIENT_COMPRESS.get(), 32
  );
  Native::registerConstant<KindOfInt64>(
    s_MYSQL_CLIENT_IGNORE_SPACE.get(), 256
  );
  Native::registerConstant<KindOfInt64>(
    s_MYSQL_CLIENT_INTERACTIVE.get(), 1024
  );
  Native::registerConstant<KindOfInt64>(
    s_MYSQL_CLIENT_SSL.get(), 2048
  );
  Native::registerConstant<KindOfInt64>(
    s_ASYNC_OP_INVALID.get(), k_ASYNC_OP_INVALID
  );
  Native::registerConstant<KindOfInt64>(
    s_ASYNC_OP_UNSET.get(), k_ASYNC_OP_UNSET
  );
  Native::registerConstant<KindOfInt64>(
    s_ASYNC_OP_CONNECT.get(), k_ASYNC_OP_CONNECT
  );
  Native::registerConstant<KindOfInt64>(
    s_ASYNC_OP_QUERY.get(), k_ASYNC_OP_QUERY
  );

  loadSystemlib("mysql");

#ifdef FACEBOOK
  HHVM_FE(mysql_async_connect_start);
  HHVM_FE(mysql_async_connect_completed);
  HHVM_FE(mysql_async_query_start);
  HHVM_FE(mysql_async_query_result);
  HHVM_FE(mysql_async_query_completed);
  HHVM_FE(mysql_async_fetch_array);
  HHVM_FE(mysql_async_wait_actionable);
  HHVM_FE(mysql_async_status);

  loadSystemlib("mysql-async");
#endif
}

mysqlExtension s_mysql_extension;

bool mysqlExtension::ReadOnly = false;
#ifdef FACEBOOK
bool mysqlExtension::Localize = false;
#endif
int mysqlExtension::ConnectTimeout = 1000;
int mysqlExtension::ReadTimeout = 60000;
int mysqlExtension::WaitTimeout = -1;
int mysqlExtension::SlowQueryThreshold = 1000; // ms
bool mysqlExtension::KillOnTimeout = false;
int mysqlExtension::MaxRetryOpenOnFail = 1;
int mysqlExtension::MaxRetryQueryOnFail = 1;
std::string mysqlExtension::Socket = "";
bool mysqlExtension::TypedResults = true;

int mysqlExtension::debuggerSupport() {
  return SupportInfo;
}

void mysqlExtension::debuggerInfo(InfoVec &info) {
  auto count = MySQL::NumCachedConnections();
  Add(info, "Persistent", FormatNumber("%" PRId64, count));
  AddServerStats(info, "sql.conn"       );
  AddServerStats(info, "sql.reconn_new" );
  AddServerStats(info, "sql.reconn_ok"  );
  AddServerStats(info, "sql.reconn_old" );
  AddServerStats(info, "sql.query"      );
}

void mysqlExtension::moduleLoad(const IniSetting::Map& ini, Hdf config) {
  Hdf mysql = config["MySQL"];
  Config::Bind(ReadOnly, ini, mysql["ReadOnly"], false);
#ifdef FACEBOOK
  Config::Bind(Localize, ini, mysql["Localize"], false);
#endif
  Config::Bind(ConnectTimeout, ini, mysql["ConnectTimeout"], 1000);
  Config::Bind(ReadTimeout, ini, mysql["ReadTimeout"], 60000);
  Config::Bind(WaitTimeout, ini, mysql["WaitTimeout"], -1);
  Config::Bind(SlowQueryThreshold, ini, mysql["SlowQueryThreshold"], 1000);
  Config::Bind(KillOnTimeout, ini, mysql["KillOnTimeout"], false);
  Config::Bind(MaxRetryOpenOnFail, ini, mysql["MaxRetryOpenOnFail"], 1);
  Config::Bind(MaxRetryQueryOnFail, ini, mysql["MaxRetryQueryOnFail"], 1);
  Config::Bind(Socket, ini, mysql["Socket"], "");
  Config::Bind(TypedResults, ini, mysql["TypedResults"], true);
}

}
