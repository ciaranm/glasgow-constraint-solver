#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_PARITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_PARITY_HH 1

#include <gcs/constraint.hh>
#include <gcs/constraints/parity/parity_chain.hh>
#include <gcs/innards/literal.hh>
#include <gcs/lifetime.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <string>
#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that an odd number of literals are true.
     *
     * \ingroup Constraints
     */
    class ParityOdd : public Constraint
    {
    private:
        const innards::Literals _lits;

        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        // Equivalent to ParityOdd([var != 0 : var in vars])
        explicit ParityOdd(const std::vector<IntegerVariableID> & vars);

        explicit ParityOdd(innards::Literals);

        virtual auto clone() const -> std::unique_ptr<Constraint> override;

        /**
         * \brief The literals, as posted.
         *
         * Public so that a presolver gathering several of these into one GF(2)
         * system can read the rows back. \sa ParitySystemGathering
         */
        [[nodiscard]] auto literals() const GCS_LIFETIME_BOUND -> const innards::Literals &
        {
            return _lits;
        }

        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };

    /**
     * \brief ParityOdd's published proof output: its accumulator chain.
     *
     * There is no single primary row --- the chain is a family, four clauses per
     * literal plus three pins --- so primary_row_role is honestly nullopt and
     * \ref chain_naming is what a citer wants. Pass what it returns to
     * innards::find_parity_chain along with this constraint's id and its
     * literals().size(), and the whole chain comes back or nothing does.
     *
     * Public API, and doubly so: these are cake_pb_cp's own names, re-derived at
     * the other end from the `.scp`, so changing one is a cross-tool break
     * rather than merely an internal one.
     *
     * \ingroup Innards
     */
    template <>
    struct innards::ConstraintProofModelData<ParityOdd>
    {
        /**
         * \brief Always nullopt: a chain has no one row a citer could mean.
         */
        [[nodiscard]] static auto primary_row_role(const ParityOdd &) -> std::optional<std::string>;

        /**
         * \brief How this constraint's single chain names its rows and flags.
         */
        [[nodiscard]] static auto chain_naming() -> innards::ParityChainNaming;
    };
}

#endif
