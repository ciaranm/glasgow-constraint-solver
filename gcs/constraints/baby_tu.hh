

#ifndef GLASGOW_CONSTRAINT_SOLVER_BABY_TU_HH
#define GLASGOW_CONSTRAINT_SOLVER_BABY_TU_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

namespace gcs
{
    class BabyTU : public Constraint
    {
    private:
        IntegerVariableID _x, _y;

    public:
        explicit BabyTU(const IntegerVariableID x, const IntegerVariableID y);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_BABY_TU_HH
