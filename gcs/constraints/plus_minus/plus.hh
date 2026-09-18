#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PLUS_MINUS_PLUS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PLUS_MINUS_PLUS_HH

#include <gcs/consistency.hh>
#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <gcs/constraints/innards/plus_minus_mutations.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/innards/proofs/proof_logger.hh>

#include <optional>
#include <utility>
#include <variant>

namespace gcs
{
    /**
     * \brief The consistency levels supported by Plus and Minus:
     * consistency::Auto (the default), bounds consistency, generalised arc
     * consistency, generalised arc consistency while it is cheap
     * (consistency::Dynamic), or generalised arc consistency by tabulation.
     *
     * \ingroup Consistency
     */
    using PlusConsistency = std::variant<consistency::Auto, consistency::BC, consistency::GAC, consistency::Dynamic, consistency::Tabulated>;

    /**
     * \brief Constrain that a + b = result.
     *
     * consistency::GAC prunes each variable to the sums or differences of the
     * other two domains, computed over their intervals, so its cost depends on
     * how many intervals the domains have rather than on how wide they are. It
     * reaches generalised arc consistency whenever the three variables are
     * distinct; with two positions sharing a variable it is sound but can be
     * weaker, where tabulation is not.
     *
     * consistency::Dynamic is the same propagator, except that a step whose
     * two operands have more pairs of intervals than
     * innards::default_interval_pairs_threshold() allows combines each operand
     * with the other's hull instead: cheaper, and still stronger than bounds
     * consistency. On every model measured in issue #192 the threshold was never
     * reached where generalised arc consistency paid.
     *
     * consistency::Auto (the default) is consistency::Dynamic, except that small
     * domains with two positions sharing a variable are tabulated, as
     * consistency::Tabulated does, since that reaches generalised arc
     * consistency there. consistency::BC is the dedicated bounds propagator. The
     * choice never changes the OPB encoding: a table is derived in-proof.
     *
     * \ingroup Constraints
     */
    class Plus : public Constraint
    {
    private:
        IntegerVariableID _a, _b, _result;
        PlusConsistency _level = consistency::Auto{};
        std::pair<std::optional<innards::ProofLine>, std::optional<innards::ProofLine>> _sum_line;
        innards::PlusMinusProofMutation _proof_mutation = innards::plus_minus_proof_mutation::None{};

        // Decided by prepare() (it needs the initial domains), installed by
        // install_propagators(). Empty means not tabulating.
        std::optional<innards::TabulationPlan> _tabulation;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Plus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result);

        /// Select the consistency level; see the class documentation for what
        /// consistency::Auto (the default) does. Requesting an unsupported level is
        /// a compile-time error.
        auto with_consistency(PlusConsistency level) -> Plus &;

        /// See innards::PlusMinusProofMutation. Never use this outside a test.
        auto with_proof_mutation(innards::PlusMinusProofMutation mutation) -> Plus &;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
