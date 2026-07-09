#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_CAKE_TRUTHINESS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_CAKE_TRUTHINESS_HH

#include <gcs/innards/literal.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <functional>
#include <optional>
#include <utility>

namespace gcs::innards
{
    /**
     * \brief The cake_pb_cp positive form of a literal, if it has one.
     *
     * cake reads a bare operand X of its `and` / `or` / `parity` terms as the
     * test "X > 0". A literal is representable as such an operand exactly when
     * it is semantically equivalent to "X > 0" for some variable or constant X
     * under the variables' initial bounds: `v != 0` or `v >= 1` with lb(v) >= 0,
     * `v == 1` with bounds within [0, 1], or a statically-valued literal (as
     * the constant 1 or 0). Negations (`v == 0`), shifted comparisons, `!= 0`
     * over a negative-capable domain (where our non-zero semantics diverges
     * from cake's positive semantics), and view conditions have no such form.
     *
     * `bounds_of` supplies a variable's initial bounds; callers pass
     * State::bounds at prepare time or NamesAndIDsTracker::tracked_bounds at
     * scp-writing time (identical values, see Regular's s_expr).
     */
    [[nodiscard]] auto cake_positive_form(const Literal & lit,
        const std::function<std::pair<Integer, Integer>(const SimpleIntegerVariableID &)> & bounds_of) -> std::optional<IntegerVariableID>;

    /**
     * \brief The literal a cake positive form stands for: `var >= 1` for a
     * variable, TrueLiteral / FalseLiteral for a constant.
     *
     * When every literal of a logical constraint has a positive form, the
     * constraint's rows and its propagator's inferences use these in place of
     * the originals (they are state-equivalent given the bounds check above),
     * so the proof never touches the `!= 0` atom machinery whose ge0 boundary
     * atoms cake's OPB does not define.
     */
    [[nodiscard]] auto cake_positive_literal(const IntegerVariableID & form) -> Literal;

    class NamesAndIDsTracker;
    class SExpr;

    /**
     * \brief A faithful s-expression term for a literal: `1` / `0` for the
     * static literals, and a `(var op value)` triple otherwise.
     *
     * Used by the `_lits` forms of the logical constraints' s_expr when a
     * literal has no cake positive form: cake_pb_cp has no term for these, so
     * the writer records the literal's real shape (rather than a bare variable
     * cake would silently reinterpret as "> 0") and the chain skips the
     * instance. read_scp reads the triples back for round-trip stability.
     */
    [[nodiscard]] auto faithful_literal_term(const Literal & lit, const NamesAndIDsTracker & tracker) -> SExpr;
}

#endif
