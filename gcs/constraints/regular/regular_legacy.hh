#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_REGULAR_LEGACY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_REGULAR_LEGACY_HH

#include <gcs/constraint.hh>
#include <gcs/extensional.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>
#include <optional>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>
namespace gcs
{
    /**
     * \brief Constrain that the sequence of variables is a member of the
     * language recognised by the given finite automaton, equivalent to a regex
     * expression. The automaton may be non-deterministic: each (state, value)
     * pair maps to a set of next states. "short_reasons" uses aliases for
     * reasons when proof logging is enabled, which can result in shorter
     * proofs.
     *
     * The automaton may instead be given as a regular expression string, which
     * is compiled to an NFA over the constrained variables' domains. The syntax
     * matches MiniZinc/Gecode (see regular/regex.hh).
     *
     * \ingroup Constraints
     */
    class RegularLegacy : public Constraint
    {
        // Regular is the public front-end; it constructs a RegularLegacy through
        // the internal representation constructor below when its proof strategy
        // is proof_strategy::PerCall.
        friend class Regular;

    private:
        const std::vector<IntegerVariableID> _vars;
        long _num_states;
        std::vector<std::unordered_map<Integer, std::set<long>>> _transitions;
        std::vector<long> _final_states;
        bool _short_reasons = true;
        const std::optional<std::string> _regex;
        std::vector<Integer> _symbols;
        std::vector<std::vector<innards::ProofFlag>> _state_at_pos_flags;
        innards::ConstraintStateHandle _graph_idx;
        std::set<Integer> _opb_alphabet;

        // Copy-style constructor used by clone(): takes the internal multi-target
        // representation (and the regex, if any) directly.
        RegularLegacy(std::vector<IntegerVariableID> vars, long num_states, std::vector<std::unordered_map<Integer, std::set<long>>> transitions,
            std::vector<long> final_states, std::vector<Integer> symbols, bool short_reasons, std::optional<std::string> regex);

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit RegularLegacy(std::vector<IntegerVariableID> vars, long num_states, std::vector<std::unordered_map<Integer, long>> transitions,
            std::vector<long> final_states);

        explicit RegularLegacy(
            std::vector<IntegerVariableID> vars, long num_states, std::vector<std::vector<long>> transitions, std::vector<long> final_states);

        /**
         * \brief Constrain that the sequence of variables matches the given
         * regular expression. The expression is compiled to an NFA over the
         * contiguous min..max range of the variables' domains.
         */
        explicit RegularLegacy(std::vector<IntegerVariableID> vars, std::string regex);

        /// Whether to use short reasons in the proof log (default true). Takes a
        /// std::optional<bool> so a runtime flag can be passed directly; nullopt
        /// or no argument leaves it at true.
        auto with_short_reasons(std::optional<bool> short_reasons = true) -> RegularLegacy &;

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
