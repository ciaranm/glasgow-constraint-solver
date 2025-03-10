#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MINUS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MINUS_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <utility>

namespace gcs
{
    /**
     * \brief Constrain that a - b = result.
     *
     * \ingroup Constraints
     */
    class Minus : public Constraint
    {
    private:
        IntegerVariableID _a, _b, _result;

    public:
        explicit Minus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
