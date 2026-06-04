#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_REGULAR_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_REGULAR_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <set>
#include <unordered_map>
#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that the sequence of variables is a member of the
     * language recognised by the given Deterministic Finite Automaton,
     * equivalent to a regex expression.
     *
     * Proof scaffolding mirrors the upfront pattern used by MDD,
     * Knapsack, and BinPacking Stage 3: the OPB encoding is the natural
     * per-(state, val) forward chains plus per-layer exactly-one, and a
     * one-shot Top-level initialiser derives per-val backward chains
     * plus statically-dead-node lines. The per-call propagator's
     * `~state[i][q]` derivations RUP-close through that scaffolding
     * instead of re-emitting per-(parent, val) intermediates on every
     * propagation call.
     *
     * The `short_reasons` flag is retained for API parity with
     * RegularLegacy and benchmarking. The new propagator emits at most
     * one proof line per state-death, so the effect of the flag is
     * small or zero here — it is forwarded as a hint to the per-call
     * reason emission, no more.
     *
     * \ingroup Constraints
     */
    class Regular : public Constraint
    {
    private:
        struct Bridge;

        const std::vector<IntegerVariableID> _vars;
        const long _num_states;
        std::vector<std::unordered_map<Integer, long>> _transitions;
        const std::vector<long> _final_states;
        const bool _short_reasons;
        std::vector<Integer> _symbols;
        std::shared_ptr<Bridge> _bridge;
        innards::ConstraintStateHandle _graph_idx;
        innards::ConstraintStateHandle _dead_cache_idx;
        std::set<Integer> _opb_alphabet;

        [[nodiscard]] auto symbols() const -> const std::vector<Integer> &;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Regular(std::vector<IntegerVariableID> vars,
            long num_states,
            std::vector<std::unordered_map<Integer, long>> transitions,
            std::vector<long> final_states, bool short_reasons = true);

        explicit Regular(std::vector<IntegerVariableID> vars,
            long num_states,
            std::vector<std::vector<long>> transitions,
            std::vector<long> final_states, bool short_reasons = true);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
