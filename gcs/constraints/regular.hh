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
     * equivalent to a regex expression.
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
        const bool _print_graph;
        const std::string _GRAPH_OUTPUT_FILE;

    public:
        explicit Regular(std::vector<IntegerVariableID> vars,
            std::vector<Integer> symbols,
            long num_states,
            std::vector<std::unordered_map<Integer, long>> transitions,
            std::vector<long> final_states,
            bool print_graph = false);

        explicit Regular(std::vector<IntegerVariableID> v,
            std::vector<Integer> s,
            long n, std::vector<std::vector<long>> transitions,
            std::vector<long> f,
            bool print_graph = false);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
