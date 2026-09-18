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
     * consistency, or generalised arc consistency by tabulation.
     *
     * \ingroup Consistency
     */
    using PlusConsistency = std::variant<consistency::Auto, consistency::BC, consistency::GAC, consistency::Tabulated>;

    /**
     * \brief Constrain that a + b = result.
     *
     * The dedicated propagator is bounds consistent; requesting
     * consistency::Tabulated, or leaving the default consistency::Auto with small
     * domains, additionally tabulates the relation, with the table derived
     * in-proof so the OPB encoding is unchanged by the choice.
     *
     * Requesting consistency::GAC instead prunes each variable to the sums or
     * differences of the other two domains, computed over their intervals, so
     * its cost depends on how many intervals the domains have rather than on how
     * wide they are, and it never tabulates. It reaches generalised arc
     * consistency whenever the three variables are distinct; with two positions
     * sharing a variable it is sound but can be weaker, where tabulation is not.
     * Nothing chooses it automatically: consistency::Auto still tabulates small
     * domains and otherwise propagates bounds.
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
        // install_propagators(). Empty means bounds consistency only.
        std::optional<innards::TabulationPlan> _tabulation;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Plus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result);

        /// Select the consistency level; consistency::Auto (the default) tabulates when the
        /// domains are small. Requesting an unsupported level is a compile-time error.
        auto with_consistency(PlusConsistency level) -> Plus &;

        /// See innards::PlusMinusProofMutation. Never use this outside a test.
        auto with_proof_mutation(innards::PlusMinusProofMutation mutation) -> Plus &;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
