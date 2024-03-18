#ifndef GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_BASE_HH
#define GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_BASE_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>

#include <list>
#include <map>
#include <optional>
#include <vector>

namespace gcs::innards::circuit
{
    struct ProofFlagData
    {
        std::string comment_name;
        ProofFlag flag;
        ProofLine forwards_reif_line;
        innards::ProofLine backwards_reif_line;
        std::map<long, innards::ProofLine> neq_lines;
    };

    struct PosVarLineData
    {
        ProofLine leq_line;
        ProofLine geq_line;
    };

    struct PosVarData
    {
        std::string comment_name;
        ProofOnlySimpleIntegerVariableID var;
        std::map<long, PosVarLineData> plus_one_lines;
    };

    struct PosAllDiffData
    {
        std::map<long, ProofLine> at_most_1_lines;
        std::map<long, ProofLine> at_least_1_lines;
    };

    using ProofFlagDataMap = std::map<long, std::map<long, ProofFlagData>>;
    using PosVarDataMap = std::map<long, PosVarData>;

    struct ShiftedPosDataMaps
    {
        std::map<long, ProofFlagData> greater_than;
        ProofFlagDataMap shifted_pos_eq;
        ProofFlagDataMap shifted_pos_geq;
    };

    auto output_cycle_to_proof(const std::vector<IntegerVariableID> & succ,
        const long & start,
        const long & length,
        const PosVarDataMap & pos_var_data,
        State & state,
        ProofLogger & logger,
        const std::optional<Integer> & prevent_idx = std::nullopt,
        const std::optional<Integer> & prevent_value = std::nullopt) -> void;

    [[nodiscard]] auto prevent_small_cycles(const std::vector<IntegerVariableID> & succ, const PosVarDataMap & pos_var_data,
        const ConstraintStateHandle & unassigned_handle, State & state, ProofLogger * const logger) -> Inference;

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
        virtual auto set_up(innards::Propagators &, innards::State &, ProofModel * const) -> innards::circuit::PosVarDataMap;

    public:
        explicit CircuitBase(std::vector<IntegerVariableID> var, bool gac_all_different = false);
        [[nodiscard]] auto clone() const -> std::unique_ptr<Constraint> override = 0;
        auto describe_for_proof() -> std::string override;
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_BASE_HH
