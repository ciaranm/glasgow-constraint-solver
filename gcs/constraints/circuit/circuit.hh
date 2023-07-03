

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CIRCUIT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CIRCUIT_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proof-fwd.hh>

#include <gcs/variable_id.hh>
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

    public:
        explicit CircuitBase(std::vector<IntegerVariableID> var, bool gac_all_different = true);
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        virtual auto describe_for_proof() -> std::string override;
        virtual auto set_up(innards::Propagators &, innards::State &) -> ProofLine2DMap;
    };

    class CircuitSCC : public CircuitBase
    {
    public:
        explicit CircuitSCC(std::vector<IntegerVariableID> var);
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
    };

    class CircuitPrevent : public CircuitBase
    {

    public:
        explicit CircuitPrevent(std::vector<IntegerVariableID> var, bool gac_all_different = true);
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
    };

    using Circuit = CircuitPrevent;

    auto propagate_non_gac_alldifferent(const std::optional<IntegerVariableID> & trigger_var,
        const std::vector<IntegerVariableID> & succ, innards::State & state) -> innards::Inference;
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CIRCUIT_HH
