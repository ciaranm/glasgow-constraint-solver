#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_HH

#include <gcs/constraint.hh>
#include <gcs/extensional.hh>
#include <gcs/variable_id.hh>
#include <unordered_map>
#include <vector>
namespace gcs
{
    /**
     * \brief Constrain that the sequence of variables is a member of the
     * language recognised by the given Deterministic Finite Automaton,
     * equivalent to a regex expression. "short_reasons" uses aliases for
     * reasons when proof logging is enabled, which can result in shorter
     * proofs.
     *
     * \warning The `symbols` parameter must be exactly `{0_i, 1_i, 2_i, ...}`
     * (zero-indexed integers). The matrix-form constructor stores transitions
     * keyed by symbol index, not symbol value, so a non-zero-based alphabet
     * produces a mismatch between the transition table and the variable values
     * looked up during propagation.
     *
     * \ingroup Constraints
     */
    class Regular : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        const std::vector<Integer> _symbols;
        const long _num_states;
        std::vector<std::unordered_map<Integer, long>> _transitions;
        const std::vector<long> _final_states;
        const bool _short_reasons;

    public:
        explicit Regular(std::vector<IntegerVariableID> vars,
            std::vector<Integer> symbols,
            long num_states,
            std::vector<std::unordered_map<Integer, long>> transitions,
            std::vector<long> final_states, bool short_reasons = true);

        explicit Regular(std::vector<IntegerVariableID> v,
            std::vector<Integer> s,
            long n, std::vector<std::vector<long>> t,
            std::vector<long> f,
            bool sr = true);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
