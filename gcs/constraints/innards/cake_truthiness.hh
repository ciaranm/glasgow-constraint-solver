#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_CAKE_TRUTHINESS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_CAKE_TRUTHINESS_HH

#include <gcs/innards/literal.hh>

namespace gcs::innards
{
    class NamesAndIDsTracker;
    class SExpr;

    /**
     * \brief The cake_pb_cp reification-term for a literal: the tuple
     * `(Z op v)` cake reads as the reified test "Z op v".
     *
     * cake's `and` / `or` / `parity` constraints take a list of these tuples
     * (one per operand) plus one for the reification. Every literal maps
     * directly: a condition `(var op value)` becomes `(var op value)` (the op
     * spelled as cake's symbol via s_expr_name_of), and the static literals
     * become a constant tuple that is trivially true (`(1 >= 1)`) or false
     * (`(0 >= 1)`). cake maps each tuple to the same ge / eq encoding atom the
     * solver's proof already uses (`i[v][ge<k>]` / `i[v][eq<k>]`), so no
     * bounds-dependent conformability check is needed and every logical operand
     * chain-verifies.
     *
     * A view-conditioned operand renders its variable as an s-expression list,
     * which cake's var/const parser rejects, so those instances still skip the
     * verified-encoding chain (they were never expressible as a cake operand).
     * read_scp reads the tuples back for round-trip stability.
     */
    [[nodiscard]] auto reify_tuple_term(const Literal & lit, const NamesAndIDsTracker & tracker) -> SExpr;
}

#endif
