#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_HH

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
     * matches MiniZinc/Gecode (see regular_regex.hh).
     *
     * \ingroup Constraints
     */
    class Regular : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        long _num_states;
        std::vector<std::unordered_map<Integer, std::set<long>>> _transitions;
        std::vector<long> _final_states;
        const bool _short_reasons;
        const std::optional<std::string> _regex;
        std::vector<Integer> _symbols;
        std::vector<std::vector<innards::ProofFlag>> _state_at_pos_flags;
        innards::ConstraintStateHandle _graph_idx;
        std::set<Integer> _opb_alphabet;

        [[nodiscard]] auto symbols() const -> const std::vector<Integer> &;

        // Copy-style constructor used by clone(): takes the internal multi-target
        // representation (and the regex, if any) directly.
        Regular(std::vector<IntegerVariableID> vars, long num_states,
            std::vector<std::unordered_map<Integer, std::set<long>>> transitions,
            std::vector<long> final_states, std::vector<Integer> symbols,
            bool short_reasons, std::optional<std::string> regex);

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
            std::vector<long> final_states, bool sr = true);

        /**
         * \brief Constrain that the sequence of variables matches the given
         * regular expression. The expression is compiled to an NFA over the
         * contiguous min..max range of the variables' domains.
         */
        explicit Regular(std::vector<IntegerVariableID> vars,
            std::string regex, bool short_reasons = true);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
