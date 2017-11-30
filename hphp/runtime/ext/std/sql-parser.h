#ifndef CHENG_SQL_PARSER
#define CHENG_SQL_PARSER
namespace HPHP {
  std::string rewriteOptSelect (std::string sql, int64_t timestamp);
  std::vector<std::string> extractTableNames(std::string sql);
}
#endif

