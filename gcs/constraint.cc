#include <gcs/constraint.hh>
#include <gcs/exception.hh>
#include <gcs/innards/s_expr.hh>

using std::string;
using std::variant;

using namespace gcs;
using namespace gcs::innards;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
#else
using fmt::format;
#endif

Constraint::~Constraint() = default;

// Bridge between the structured s_expr() and the legacy string s_exprify(). A
// constraint overrides exactly one; the other is derived here. s_expr() is the
// full `(name op args...)` list, s_exprify() is its body without the enclosing
// parentheses (the `#` alternate form), so they wrap/unwrap one level.
auto Constraint::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    return parse_s_expr("(" + s_exprify(model) + ")");
}

auto Constraint::s_exprify(const innards::ProofModel * const model) const -> string
{
    return format("{:#}", s_expr(model));
}

namespace gcs
{
    auto as_string(const ConstraintID & constraint_id) -> std::string
    {
        return visit([](const auto & n) { return n.as_string(); }, constraint_id);
    }
}
