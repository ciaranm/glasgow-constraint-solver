

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CIRCUIT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CIRCUIT_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proof-fwd.hh>
#include <gcs/innards/proof.hh>

#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>
#include <list>
#include <map>
#include <optional>
#include <vector>
namespace gcs
{
    using ProofLine2DMap = std::map<std::pair<Integer, Integer>, innards::ProofLine>;

    /**
     * \brief Circuit constraint: requires the variables, representing graph nodes, take values
     * such that each variable's value represents the index of the next node in a tour that visits
     * all variables.
     *
     * \ingroup Constraints
     */
    class CircuitBase : public Constraint
    {
    protected:
        const bool _gac_all_different;
        const std::vector<IntegerVariableID> _succ;
        virtual auto set_up(innards::Propagators &, innards::State &) -> std::pair<std::vector<innards::ProofOnlySimpleIntegerVariableID>, ProofLine2DMap>;

    public:
        explicit CircuitBase(std::vector<IntegerVariableID> var, bool gac_all_different = false);
        virtual auto clone() const -> std::unique_ptr<Constraint> override = 0;
        virtual auto describe_for_proof() -> std::string override;
        //        virtual auto install(innards::Propagators &, innards::State &) && -> void = 0;
    };

    class CircuitSCC : public CircuitBase
    {
    public:
        using CircuitBase::CircuitBase;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
    };

    class CircuitPrevent : public CircuitBase
    {
    public:
        using CircuitBase::CircuitBase;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
    };

    class CircuitPreventIncremental : public CircuitBase
    {
    public:
        using CircuitBase::CircuitBase;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
    };

    using Circuit = CircuitPreventIncremental;

    auto propagate_non_gac_alldifferent(
        const innards::ConstraintStateHandle & unassigned_handle, innards::State & state) -> innards::Inference;
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CIRCUIT_HH
