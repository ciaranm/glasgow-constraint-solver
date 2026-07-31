#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_POWER_POWER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_POWER_POWER_HH

#include <gcs/consistency.hh>
#include <gcs/constraint.hh>
#include <gcs/constraints/innards/linear_stages.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/multiply/signed_multiply.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <optional>
#include <tuple>
#include <variant>
#include <vector>

namespace gcs
{
    /**
     * \brief The consistency levels supported by Power: consistency::Auto (the
     * default), bounds consistency of the decomposition, or generalised arc
     * consistency by tabulation. A variable exponent is always tabulated.
     *
     * \ingroup Consistency
     */
    using PowerConsistency = std::variant<consistency::Auto, consistency::BC, consistency::Tabulated>;

    /**
     * \brief Constrain that base ^ exponent = result.
     *
     * The semantics follow MiniZinc (and fix a historical disagreement between
     * solvers): 0 ^ 0 = 1; a negative exponent gives 1 div base^|exponent|
     * truncated, so 2 ^ -5 = 0, 1 ^ -n = 1, (-1) ^ -n is 1 or -1 by parity,
     * and 0 ^ -n has no support. A result too big for the solver's integers
     * likewise has no support.
     *
     * A constant exponent dispatches structurally: 0 and 1 are linear
     * equalities, k >= 2 becomes a chain of Multiply constraints over
     * auxiliary variables (with the auxiliaries' ranges clamped by the
     * result's, so a hopeless chain fails rather than overflowing), a negative
     * or enormous exponent becomes a small case analysis on the base. Under
     * consistency::Auto with small domains, or consistency::Tabulated, the whole
     * relation is additionally tabulated in-proof. A variable exponent falls
     * back on innards::PowerTable, the one remaining table-in-the-OPB
     * encoding.
     *
     * \ingroup Constraints
     * \sa Multiply
     * \sa innards::PowerTable
     */
    class Power : public Constraint
    {
    private:
        IntegerVariableID _base, _exponent, _result;
        PowerConsistency _level = consistency::Auto{};

        // The case analysis prepare() settles on. The linear pieces travel as specs
        // because their rows and their stages are wanted in different phases; the
        // multiplication links of a base^k chain carry their operands from prepare()
        // and their encoding handles from define_proof_model().
        std::vector<innards::StageSpec> _specs;
        std::shared_ptr<std::vector<innards::signed_multiply::Data>> _links;

        // The chain's intermediate variables with the ranges to declare them by,
        // one per link bar the last (which writes the result handle), so link i has
        // _aux_chain[i] exactly when i is a valid index.
        std::vector<std::tuple<SimpleIntegerVariableID, Integer, Integer>> _aux_chain;

        /// A negative exponent has no support for a zero base, and says so by propagation.
        bool _prune_zero_base = false;

        /// Constant base and exponent with no representable power: the empty relation.
        bool _no_representable_result = false;

        /// Unset when the constraint is not tabulating.
        std::optional<innards::TabulationPlan> _tabulation;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Power(IntegerVariableID base, IntegerVariableID exponent, IntegerVariableID result);

        /// Select the consistency level; consistency::Auto (the default) tabulates when the
        /// domains are small. Requesting an unsupported level is a compile-time error.
        auto with_consistency(PowerConsistency level) -> Power &;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
