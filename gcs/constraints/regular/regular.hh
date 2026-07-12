#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_REGULAR_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_REGULAR_HH

#include <gcs/constraint.hh>
#include <gcs/extensional.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/state.hh>
#include <gcs/proof_strategy.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <optional>
#include <set>
#include <string>
#include <unordered_map>
#include <variant>
#include <vector>

namespace gcs
{
    /**
     * \brief The proof-logging strategies Regular supports:
     * proof_strategy::Upfront (the default), proof_strategy::PerCall, or
     * proof_strategy::Bacchus.
     *
     * All three draw the same inferences (generalised arc consistency on the
     * automaton) and find the same solutions; they differ only in the proof.
     * Upfront (the default, because a Regular automaton is narrow so its
     * Top-level scaffold is tiny) emits per-val backward chains and
     * statically-dead-node lines once at the root; PerCall re-emits
     * per-(parent, val) intermediates on every propagation call; Bacchus emits
     * a stronger transition-extension encoding at the root so the per-call
     * propagator needs no proof lines. Bacchus supports only a deterministic
     * automaton, not regular-expression / NFA input. See dev_docs/regular.md.
     *
     * \ingroup ProofStrategy
     */
    using RegularProofStrategy = std::variant<proof_strategy::Upfront, proof_strategy::PerCall, proof_strategy::Bacchus>;

    /**
     * \brief Constrain that the sequence of variables is a member of the
     * language recognised by the given finite automaton, equivalent to a regex
     * expression. The automaton may be non-deterministic: each (state, value)
     * pair maps to a set of next states.
     *
     * The automaton may instead be given as a regular expression string, which
     * is compiled to an NFA over the constrained variables' domains. The syntax
     * matches MiniZinc/Gecode (see regular/regex.hh).
     *
     * The OPB encoding — the natural per-(state, val) forward chains plus
     * per-layer exactly-one — is shared by every proof strategy. By default the
     * upfront strategy is used: a one-shot Top-level initialiser derives
     * per-val backward chains plus statically-dead-node lines, and the per-call
     * propagator's `~state[i][q]` derivations RUP-close through that
     * scaffolding. Select a different strategy with with_proof_strategy() (see
     * RegularProofStrategy); the choice is proof-only and never changes the
     * inferences, solutions, or OPB encoding.
     *
     * The `short_reasons` flag (with_short_reasons()) is a proof-log tuning
     * knob retained for benchmarking; it has little or no effect on the default
     * upfront strategy.
     *
     * \ingroup Constraints
     */
    class Regular : public Constraint
    {
    private:
        struct Bridge;

        const std::vector<IntegerVariableID> _vars;
        long _num_states;
        std::vector<std::unordered_map<Integer, std::set<long>>> _transitions;
        std::vector<long> _final_states;
        bool _short_reasons = true;
        RegularProofStrategy _proof_strategy = proof_strategy::Upfront{};
        const std::optional<std::string> _regex;
        std::vector<Integer> _symbols;
        std::shared_ptr<Bridge> _bridge;
        innards::ConstraintStateHandle _graph_idx;
        innards::ConstraintStateHandle _dead_cache_idx;
        std::set<Integer> _opb_alphabet;

        // Copy-style constructor used by clone(): takes the internal multi-target
        // representation (and the regex, if any) directly.
        Regular(std::vector<IntegerVariableID> vars, long num_states, std::vector<std::unordered_map<Integer, std::set<long>>> transitions,
            std::vector<long> final_states, std::vector<Integer> symbols, bool short_reasons, std::optional<std::string> regex);

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Regular(std::vector<IntegerVariableID> vars, long num_states, std::vector<std::unordered_map<Integer, long>> transitions,
            std::vector<long> final_states);

        explicit Regular(
            std::vector<IntegerVariableID> vars, long num_states, std::vector<std::vector<long>> transitions, std::vector<long> final_states);

        /**
         * \brief Constrain that the sequence of variables matches the given
         * regular expression. The expression is compiled to an NFA over the
         * contiguous min..max range of the variables' domains.
         */
        explicit Regular(std::vector<IntegerVariableID> vars, std::string regex);

        /// Whether to use short reasons in the proof log (default true). Takes a
        /// std::optional<bool> so a runtime flag can be passed directly; nullopt
        /// or no argument leaves it at true.
        auto with_short_reasons(std::optional<bool> short_reasons = true) -> Regular &;

        /// Select the proof-logging strategy: proof_strategy::Upfront (the
        /// default), proof_strategy::PerCall, or proof_strategy::Bacchus.
        /// Proof-only: it never changes the inferences drawn, the solutions
        /// found, or the OPB encoding. proof_strategy::Bacchus requires a
        /// deterministic automaton (not regular-expression / NFA input).
        auto with_proof_strategy(RegularProofStrategy strategy) -> Regular &;

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
