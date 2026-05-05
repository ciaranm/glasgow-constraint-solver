#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_HH 1

#include <gcs/constraint.hh>
#include <gcs/innards/literal.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

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

        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        // Equivalent to ParityOdd([var != 0 : var in vars])
        explicit ParityOdd(const std::vector<IntegerVariableID> & vars);

        explicit ParityOdd(innards::Literals);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
