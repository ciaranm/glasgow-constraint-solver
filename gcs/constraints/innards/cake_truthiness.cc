#include <gcs/constraints/innards/cake_truthiness.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/s_expr.hh>

#include <util/overloaded.hh>

#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::vector;

auto gcs::innards::reify_tuple_term(const Literal & lit, const NamesAndIDsTracker & tracker) -> SExpr
{
    // cake's and / or / parity operands are (Z op v) reification tuples. The
    // static literals become a constant tuple: (1 >= 1) is trivially true,
    // (0 >= 1) trivially false.
    return overloaded{[](const TrueLiteral &) -> SExpr { return SExpr::list(vector<SExpr>{SExpr::atom("1"), SExpr::atom(">="), SExpr::atom("1")}); },
        [](const FalseLiteral &) -> SExpr { return SExpr::list(vector<SExpr>{SExpr::atom("0"), SExpr::atom(">="), SExpr::atom("1")}); },
        [&](const IntegerVariableCondition & cond) -> SExpr {
            return SExpr::list(
                vector<SExpr>{tracker.s_expr_term_of(cond.var), SExpr::atom(tracker.s_expr_name_of(cond.op)), SExpr::atom(cond.value.to_string())});
        }}
        .visit(lit);
}
