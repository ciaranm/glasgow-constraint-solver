#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_REGULAR_BACCHUS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_REGULAR_BACCHUS_HH

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
     * \brief Same semantics as Regular, but with Bacchus's transition-variable
     * encoding derived in an initialiser so that GAC follows by plain unit
     * propagation on the proof database. The OPB stays unchanged from
     * Regular's "natural" encoding (start state, accept ALO, per-layer
     * exactly-one, and per-(state, val) forward chains); the initialiser
     * introduces a fresh t[i][q][v] proof flag for every (i, q, v) with
     * delta(q, v) defined (via redundance) and emits the in/out and
     * variable-support AL1s (via RUP). With those in the proof DB the
     * per-call propagator emits no proof lines: every value-pruning is
     * NoJustificationNeeded, and the eventual backtrack RUP closes via
     * UP alone.
     *
     * The `short_reasons` constructor argument is kept for API parity with
     * Regular and RegularLegacy, and so that one example binary can
     * benchmark all three variants from one call site (see
     * [[feedback_legacy_flags_as_dummies]]). It is unused by this
     * implementation.
     *
     * \ingroup Constraints
     * \sa Regular
     * \sa RegularLegacy
     */
    class RegularBacchus : public Constraint
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
        std::set<Integer> _opb_alphabet;

        [[nodiscard]] auto symbols() const -> const std::vector<Integer> &;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit RegularBacchus(std::vector<IntegerVariableID> vars,
            long num_states,
            std::vector<std::unordered_map<Integer, long>> transitions,
            std::vector<long> final_states, bool short_reasons = true);

        explicit RegularBacchus(std::vector<IntegerVariableID> vars,
            long num_states,
            std::vector<std::vector<long>> transitions,
            std::vector<long> final_states, bool short_reasons = true);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
