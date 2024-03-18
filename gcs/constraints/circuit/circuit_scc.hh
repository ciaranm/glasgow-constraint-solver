#ifndef GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_SCC_HH
#define GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_SCC_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/circuit/circuit_base.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>
#include <list>
#include <map>
#include <optional>
#include <vector>

namespace gcs
{
    struct SCCOptions
    {
        bool prune_root = true;
        bool prune_skip = true;
        bool fix_req = true;
        bool prune_within = true;
        bool prove_using_dominance = false;
        bool enable_comments = true;
    };

    class CircuitSCC : public innards::circuit::CircuitBase
    {
    protected:
        const SCCOptions scc_options;

    public:
        explicit CircuitSCC(std::vector<IntegerVariableID> var, bool gac_all_different = false, SCCOptions scc_options = SCCOptions{});
        [[nodiscard]] auto clone() const -> std::unique_ptr<Constraint> override;
        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_SCC_HH
