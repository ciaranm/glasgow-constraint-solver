

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
    struct ProofFlagData
    {
        innards::ProofFlag flag;
        innards::ProofLine forwards_reif_line;
        innards::ProofLine backwards_reif_line;
    };

    struct PosVarLineData
    {
        innards::ProofLine leq_line;
        innards::ProofLine geq_line;
    };

    struct PosVarData
    {
        innards::ProofOnlySimpleIntegerVariableID var;
        std::map<long, PosVarLineData> plus_one_lines;
    };

    using ProofFlagDataMap = std::map<long, std::map<long, ProofFlagData>>;
    using PosVarDataMap = std::map<long, PosVarData>;

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
        virtual auto set_up(innards::Propagators &, innards::State &) -> PosVarDataMap;

    public:
        explicit CircuitBase(std::vector<IntegerVariableID> var, bool gac_all_different = false);
        [[nodiscard]] auto clone() const -> std::unique_ptr<Constraint> override = 0;
        auto describe_for_proof() -> std::string override;
        //        virtual auto install(innards::Propagators &, innards::State &) && -> void = 0;
    };

    class CircuitSCC : public CircuitBase
    {
    public:
        using CircuitBase::CircuitBase;
        [[nodiscard]] auto clone() const -> std::unique_ptr<Constraint> override;
        auto install(innards::Propagators &, innards::State &) && -> void override;
    };

    /**
     * Circuit constraint that propagates by identifying chains and removing the head of each chain from the domain of
     * the tail "preventing" small cycles.
     */
    class CircuitPrevent : public CircuitBase
    {
    public:
        using CircuitBase::CircuitBase;
        [[nodiscard]] auto clone() const -> std::unique_ptr<Constraint> override;
        auto install(innards::Propagators &, innards::State &) && -> void override;
    };

    /**
     * The same prevent algorithm, but updating the chains incrementally.
     */
    class CircuitPreventIncremental : public CircuitBase
    {
    public:
        using CircuitBase::CircuitBase;
        [[nodiscard]] auto clone() const -> std::unique_ptr<Constraint> override;
        auto install(innards::Propagators &, innards::State &) && -> void override;
    };

    using Circuit = CircuitPreventIncremental;

    auto propagate_non_gac_alldifferent(
        const innards::ConstraintStateHandle & unassigned_handle, innards::State & state) -> innards::Inference;

    auto output_cycle_to_proof(const std::vector<IntegerVariableID> & succ,
        const long & start,
        const long & length,
        const PosVarDataMap & pos_var_data,
        innards::State & state,
        innards::Proof & proof,
        const std::optional<Integer> & prevent_idx = std::nullopt,
        const std::optional<Integer> & prevent_value = std::nullopt) -> void;

    auto prevent_small_cycles(const std::vector<IntegerVariableID> & succ, const PosVarDataMap & pos_var_data,
        const innards::ConstraintStateHandle & unassigned_handle, innards::State & state) -> innards::Inference;

}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CIRCUIT_HH
