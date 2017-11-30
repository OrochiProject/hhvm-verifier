#include "unistd.h"
#include "iostream"
#include "string"
#include "algorithm"
#include "sstream"
#include "vector"
#include "regex"
#include "map"
#include "fstream"

namespace HPHP {
//==============Helper=================

static void fail (std::string msg) {
  std::cout << "FATAL ERROR: " << msg << "\n";
  exit(1);
}

static inline bool str_replace (std::string &subj, std::string search, std::string replace) {
  size_t start_pos = subj.find(search);
  if(start_pos == std::string::npos)
    return false;
  subj.replace(start_pos, search.length(), replace);
  return true;
}

static std::vector<std::string> explode(std::string const & s, char delim) {
  std::vector<std::string> result;
  std::istringstream iss(s);
  for (std::string token; std::getline(iss, token, delim); ) {
    result.push_back(std::move(token));
  }
  return result;
}

static std::vector<std::string> explode(std::string const & s, std::string delim) {
  std::vector<std::string> tokens;
  std::string::size_type start_pos = 0, end_pos = 0, length = s.length(), dlen = delim.length();

  while(end_pos < length) {

    end_pos = s.find(delim, end_pos);
    if (end_pos == std::string::npos)
    {
      // cannot find anything any more
      end_pos = length;
      break;
    }

    tokens.push_back( s.substr(start_pos, end_pos - start_pos) );

    start_pos = end_pos + dlen;
    end_pos = start_pos; 
  }

  if (start_pos < end_pos) {
    tokens.push_back( s.substr(start_pos, end_pos - start_pos) );
  }

  return tokens;
}

static std::string print_array(std::vector<std::string> arr) {
  std::stringstream ss;
  ss << "Array {";
  for (auto it : arr) {
    ss << "<" << it << ">, ";
  }
  ss << "}";
  return ss.str();
}

static inline std::string trim(const std::string &s)
{
  auto wsfront=std::find_if_not(s.begin(),s.end(),[](int c){return std::isspace(c);});
  auto wsback=std::find_if_not(s.rbegin(),s.rend(),[](int c){return std::isspace(c);}).base();
  return (wsback<=wsfront ? std::string() : std::string(wsfront,wsback));
}

static bool bothAreSpaces(char lhs, char rhs) {
  return std::isspace(lhs) && std::isspace(rhs); 
}

static void removeDupSpace(std::string &str) {
  std::string::iterator new_end = std::unique(str.begin(), str.end(), bothAreSpaces);
  str.erase(new_end, str.end());
}

static void removeComments(std::string &str) {
  // find the first comment
  auto s_pos = str.find("/*");
  auto e_pos = str.find("*/");
  if (s_pos != std::string::npos &&
      e_pos != std::string::npos && s_pos < e_pos) {
    str.erase(s_pos, e_pos-s_pos+2);
  }
}

static void replaceNewline(std::string &str) {
  std::string::size_type pos = 0;
  while ((pos = str.find("\n", pos)) != std::string::npos) {
    str.replace(pos, 1, " ");
  }
}

static void inline strtolower (std::string& str) {
  std::transform(str.begin(), str.end(), str.begin(), ::tolower);
}

// str_repeat
// std::string(5,'*')

// substr_replace
// str.replace(pos, len, str)

// strpos
// str.find(str, pos)

// substr
// str.substr(pos, len)

//================Functional=============

static void clearContentsInParenthese(std::string &sql) {
  int p_counter = -1;
  int start_pos = 0, end_pos = 0;
  bool earse = false;
  for (int i = 0; i < sql.length(); i++) {
    if (sql[i] == '(') {
      if (p_counter == -1) {
        start_pos = i;
        p_counter = 0;
      }
      p_counter++;
    } else if (sql[i] == ')') {
      p_counter --;
      if (p_counter == 0) {
        end_pos = i;
        p_counter = -1;
        earse = true;
      }
    }

    if (earse) {
      earse = false;
      int len = end_pos - start_pos -1;
      sql.replace(start_pos+1, len, std::string(len, '*'));
    }
  }
}

// forward declar
std::string _rewriteOptSelect (std::string sql, std::string timestamp);

std::string
extractTableName(std::string sql, std::vector<std::string> following_str_arry,
                 std::pair<std::string, std::string> &pair, std::string timestamp) {
  sql = trim(sql);

  // FIXME: what if the '(' is in a string?
  if (sql[0] == '(') {
    // find the subsql query
    int subsql_end_pos = 0, parenthese = 1;
    for (int i=1; i<sql.length(); i++) {
      if (sql[i] == ')') {
        parenthese--;
      } else if (sql[i] == '(') {
        parenthese++;
      }
      if (parenthese == 0) {
        subsql_end_pos = i-1; // we exclude the last ')'
        break;
      }
    }
    if (subsql_end_pos == 0) {
      fail("extractTableName: cannot find the correct subsql");
    }

    // (ab), the subsql_end_pos would be at 'b' which is 2
    std::string subsql = sql.substr(1, subsql_end_pos);

    if (trim(subsql).substr(0,6) == "select") {
      std::string rewrite = _rewriteOptSelect(subsql, timestamp);
      pair.first = subsql;
      pair.second = rewrite;
      return "";
    } else {
      // (tablename n)
      return extractTableName(subsql, following_str_arry, pair, timestamp);
    }
  } else {
    // can be multiple table names
    // (i). from [ table1 t, table2 as t2 ] using ...
    // (ii). from [ table1 t cross join table2 as t2 ] using ...
    auto table_chunks = explode(sql, ',');
    if (table_chunks.size() == 1) {
      // FIXME: try case (ii)
      table_chunks = explode(table_chunks[0], "CROSS JOIN");
    }
    std::vector<std::string> tnames;

    for (auto tname_str : table_chunks) {
      bool found_name = false;
      auto elements = explode(trim(tname_str), ' ');
      // 1. "tablename"
      // 2. "tablename alias"
      // 3. "tablename as alias"
      // 4. "tablename on/using (....)"
      if (elements.size()==1) {
        // case 1.
        tnames.push_back(elements[0]);
        found_name = true;
        continue;
      }

      // case 4.
      auto next_token = elements[1];
      strtolower(next_token);
      for (auto it : following_str_arry) {
        if (next_token == it) {
          // case "tablename using"
          tnames.push_back(elements[0]);
          found_name = true;
        }
      }
      if (found_name) continue;

      if (next_token == "as") {
        // case 2.
        tnames.push_back(elements[2]);
      } else {
        //case 3.
        tnames.push_back(elements[1]);
      }
    }

    std::string ret = "";
    for (int i = 0; i<tnames.size(); i++) {
      if (i==0) {
        ret = tnames[i];
      } else {
        ret +=  "," + tnames[i];
      }
    }
    return ret;
  }
}

std::pair<std::string, std::string>
extractJoinTable(std::string &sql,
                             int start_pos, int end_pos,
                             std::pair<std::string, std::string> &pair,
                             std::string timestamp) {
  int s_pos = start_pos + 5; // 5 = strlen("join ")
  std::string subsql = sql.substr(s_pos, end_pos - s_pos);
  std::vector<std::string> following_str_arry{"on", "using", "" };
  auto name = extractTableName(subsql, following_str_arry, pair, timestamp);
  // rewrite the join clause
  // (1) on (...) => on (start_ts<=cur AND end_ts>cur AND ...)
  // (2) on ... => on start_ts<=cur AND end_ts>cur AND ...
  // (3) using (xxx) => on (start_ts<=cur AND end_ts>cur AND from.xxx=join.xxx)
  if (name == "") {
    // this join is a anoth full sql
    return std::pair<std::string, std::string>("","");
  }
  std::stringstream instr;
  instr << name << ".start_ts<=" << timestamp << " AND " << name << ".end_ts>" << timestamp << " AND ";
  auto str_instr = instr.str();

  int on_using_pos = subsql.find(name) + name.length();
  auto orig =  subsql.substr(on_using_pos);
  orig = trim(orig); // should start with on or using

  int orig_length = orig.length();
  std::string replacement;

find_on_using:
  if ( (orig[0] == 'o' || orig[0] == 'O') &&
       (orig[1] == 'n' || orig[1] == 'N') ) {
    // find next non_space char
    int non_space= 1;
    while(orig[++non_space] == ' '){
      if (non_space > orig_length) {
        fail("there is nothing after on in "+sql);
      }
    };

    if (orig[non_space] == '(') {
      // case (1)
      replacement = "on (" + str_instr + orig.substr(non_space+1);
    } else {
      // case (2)
      replacement = "on " + str_instr + orig.substr(non_space);
    } 
  } else if (orig.substr(0,5) == "using") {
    // find next non-space char
    int open_parn = 4;
    while(orig[++open_parn] == ' '){
      if (open_parn > orig_length) {
        fail("there is nothing after on in "+sql);
      }
    };

    if (orig[open_parn] != '(') {
      fail("error format, join using is following with ( in " + sql);
    }

    // get the attribute name
    int close_parn = open_parn;
    while(orig[++close_parn] != ')'){
      if (close_parn > orig_length) {
        fail("cannot find ) to pair ( in "+sql);
      }
    };

    auto attr_name = trim(orig.substr(open_parn+1, close_parn-open_parn-1));

    replacement = " on ( " + str_instr + " [__FROM_TABLE_NAME__]." + attr_name + "=" + name + "." + attr_name + ")"
                   + orig.substr(close_parn+1);
  } else {
    // It can be " join PaperReview r on (...) "
    int next_word = 0;
    while(orig[++next_word] !=' ');
    orig = trim(orig.substr(next_word));
    goto find_on_using;

    fail ("cannot find on/using in the join clause:\n " + sql);
  }

  return std::pair<std::string,std::string>(orig, replacement);
}

std::string
extractFromTable(std::string &sql,
                             int start_pos, int end_pos,
                             std::pair<std::string, std::string> &pair,
                             std::string timestamp) {
  int s_pos = start_pos + 5; // 5 = strlen("from ")
  std::string subsql = sql.substr(s_pos, end_pos - s_pos);
  std::vector<std::string> following_str_arry
                  {"left", "right", "full", "inner", "" };
  auto name = extractTableName(subsql, following_str_arry, pair, timestamp);
  //std::cout << "from table name [" << name << "] from [" << subsql << "]\n";
  return name;
}

//=================API====================

// the tokens can be:
// from t1,t2,t3 or from t1, t2, t3
static std::string
getNextTableNames(std::string str, int pos) {
  if (pos >= str.size()) return "";

  //auto curstr = str.substr(pos);
  //std::regex e(" *, *");
  //auto newstr = std::regex_replace(curstr, e, std::string(","));
  //std::cout << "!!!!! before: " << curstr << " } after { " << newstr << " }\n";

  auto new_str = str.substr(pos);
  int cur_pos = 0;
  while(new_str[cur_pos]==' ') {
    cur_pos++;
  }
  auto loc = new_str.find(" ", cur_pos);
  if (loc == std::string::npos) {
    return new_str.substr(cur_pos);
  } else {
    return new_str.substr(cur_pos, loc - cur_pos);
  }
}

static bool
valid_table_name(std::string token) {
  strtolower(token);
  if (token[0] == '(' ||
      token == "select") {
    return false;
  }
  return true;
}

std::vector<std::string>
extractTableNames(std::string sql) {
  std::vector<std::string> tnames;

  // clear the string
  replaceNewline(sql);
  removeDupSpace(sql);
  removeComments(sql);

  std::string lsql = sql; // copy as the template
  strtolower(lsql);

  int cur_pos = 0, from_pos = 0, join_pos = 0;
  for(;;) {
    from_pos = lsql.find(" from ", cur_pos);
    join_pos = lsql.find(" join ", cur_pos);

    // end of finding
    if (from_pos == std::string::npos &&
        join_pos == std::string::npos) break;

    if (from_pos == std::string::npos) {
      cur_pos = join_pos;
    } else if (join_pos == std::string::npos) {
      cur_pos = from_pos;
    } else {
      cur_pos = (from_pos > join_pos) ? join_pos : from_pos;
    }

    cur_pos += 6; // find token next "from"/"join"
    auto name_token = getNextTableNames(sql, cur_pos); 
    if (name_token != "") {
      auto names = explode(name_token, ',');
      for (auto tname : names) {
        tname = trim(tname);
        if (valid_table_name(tname)) {
          tnames.push_back(tname);
        }
      }
    }
  }
  
  return tnames;
}

// cheng-hack: sql template for the rewriting:
// If two queries are the same, only difference is the ts, we can
// simply rewrite it by replacing the place holder
//   original query => query template (place holder: template_ts_place_holder)
std::string template_ts_place_holder = "__TIMESTAMP__";
std::map<std::string, std::string> sql_query_templates;

std::string rewriteOptSelect (std::string sql, int64_t timestamp) {
  // try to find the template
  if (sql_query_templates.find(sql) == sql_query_templates.end()) {
    sql_query_templates[sql] = _rewriteOptSelect(sql, template_ts_place_holder);
  }
  auto tt_sql = sql_query_templates[sql];
  auto str_ts = std::to_string(timestamp);
  while (str_replace(tt_sql, template_ts_place_holder, str_ts)) {};
  return tt_sql;
}

std::string
_rewriteOptSelect (std::string sql, std::string timestamp) {
  // clear the string
  replaceNewline(sql);
  removeDupSpace(sql);
  removeComments(sql);

  std::string lsql = sql; // copy as the template
  strtolower(lsql);
  clearContentsInParenthese(lsql);

  int cur_pos = 0;
  int from_pos, where_pos, group_by_pos, order_by_pos, limit_pos; 
  std::vector<int> join_pos_arr;

  from_pos = lsql.find("from", cur_pos);
  if (from_pos == std::string::npos) {
    return sql;
  }
  cur_pos = from_pos;

  int tmp_pos;
  while ((tmp_pos = lsql.find("join", cur_pos)) != std::string::npos ){
    join_pos_arr.push_back(tmp_pos);
    cur_pos = tmp_pos + 4; // start from the end of join
  }

  where_pos = lsql.find("where", cur_pos);
  if (where_pos != std::string::npos) {
    cur_pos = where_pos;
  }

  group_by_pos = lsql.find("group by", cur_pos);
  if (group_by_pos != std::string::npos) {
    cur_pos = group_by_pos;
  }

  order_by_pos = lsql.find("order by", cur_pos);
  if (order_by_pos != std::string::npos) {
    cur_pos = order_by_pos;
  }

  limit_pos = lsql.find("limit", cur_pos);

  // make sure what we have
  bool has_join = !join_pos_arr.empty();
  bool has_where = (where_pos != std::string::npos);
  bool has_group_by = (group_by_pos != std::string::npos);
  bool has_order_by = (order_by_pos != std::string::npos);
  bool has_limit = (limit_pos != std::string::npos);
  std::vector<std::string> from_table_name;
  std::vector<std::pair<std::string, std::string> > replace_list;
  std::pair<std::string, std::string> sql_pair;

  int r_pos = lsql.length();
  if (has_where) {
    r_pos = where_pos;
  } else if (has_group_by) {
    r_pos = group_by_pos;
  } else if (has_order_by) {
    r_pos = order_by_pos;
  } else if (has_limit) {
    r_pos = limit_pos;
  }

  if (has_join) {
    // extract join table names
    for (int i = join_pos_arr.size()-1; i >=0 ; i--) {
      auto join_rewriting = extractJoinTable(sql, join_pos_arr[i], r_pos, sql_pair, timestamp);
      if (join_rewriting.first != "") {
        replace_list.push_back(join_rewriting);
      } else {
        replace_list.push_back(sql_pair);
      }
      r_pos = join_pos_arr[i];
    }
  }

  auto from_name = extractFromTable(sql, from_pos, r_pos, sql_pair, timestamp);
  if (from_name != "") {
    auto names = explode(from_name, ',');
    for (auto tname : names) {
      from_table_name.push_back(trim(tname));
    }
  } else {
    replace_list.push_back(sql_pair);
  }

  // construct the where clause
  // shoule be "WHERE (start_ts... AND end_ts..)
  //           "... AND (start_ts... AND end_ts..)
  std::string where_cond;
  where_cond.reserve(1000);
  if (has_where) {
    // replace "where" into "where(" later
    where_cond.append(") AND (");
  } else if (from_table_name.size() > 0) {
    // if there is no tablenames, we don't need where clause
    where_cond.append( " WHERE (");
  }

  // append the from_table constraint
  if (from_table_name.size() > 0 ) {
    for (auto tname : from_table_name) {
      std::stringstream from_cons;
      from_cons << tname << ".start_ts<=" << timestamp << " AND "
        << tname << ".end_ts>" << timestamp << " AND ";
      where_cond.append(from_cons.str());
    }
    where_cond.append(" TRUE )");
  }

  //std::stringstream wss;
  //wss << ".start_ts<=" << timestamp << " AND ";
  //auto where_piece1 = wss.str(); 
  //wss.str(std::string());
  //wss << ".end_ts>" << timestamp;
  //auto where_piece2 = wss.str();

  //// apply to all the tables
  //bool first = true;
  //for (auto table : table_names) {
  //  if (first) first=false; else where_cond.append(" AND ");
  //  where_cond.append(table);
  //  where_cond.append(where_piece1);
  //  where_cond.append(table);
  //  where_cond.append(where_piece2);
  //}
  //where_cond.append(" ");

  // construct all pieces
  std::string ret_sql;
  if (has_group_by || has_order_by || has_limit) {
    // [select] [join] [where] [OURS] [group by] [order by] [limi]
    std::string prefix, suffix;
    if (has_group_by) {
      prefix = sql.substr(0, group_by_pos);
      suffix = sql.substr(group_by_pos);
    } else if (has_order_by) {
      prefix = sql.substr(0, order_by_pos);
      suffix = sql.substr(order_by_pos);
    } else if (has_limit) {
      prefix = sql.substr(0, limit_pos);
      suffix = sql.substr(limit_pos);
    }
    ret_sql = prefix + where_cond + suffix; 
  } else {
    ret_sql = sql + where_cond;
  }
  // replace "where" into "where(" later
  if (has_where) {
    // assumption: where_pos has the same position
    // strlen(where) = 5
    ret_sql.insert(where_pos+5, "(");
  }

  // replace all the sub sql queries
  for (auto it : replace_list) {
    bool r = str_replace(ret_sql, it.first, it.second); 
    if (!r) {
      std::cout << "Try to replace:\n     <<" << it.first << ">>\n"
        << "    as <<" << it.second << ">>\n"
        << "    in <<" << ret_sql << ">>\n";
      fail("replace fail!");
    }
  }

  // replace the "[__FROM_TABLE_NAME__]" in join clause
  while (str_replace(ret_sql, "[__FROM_TABLE_NAME__]", from_name)) {};
  
  return ret_sql;
}

}// end of namespace
