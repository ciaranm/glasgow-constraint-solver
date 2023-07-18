

#ifndef GLASGOW_CONSTRAINT_SOLVER_MDD_HH
#define GLASGOW_CONSTRAINT_SOLVER_MDD_HH

class mdd
{
};

#endif // GLASGOW_CONSTRAINT_SOLVER_MDD_HH
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MDD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MDD_HH

#include <gcs/constraint.hh>
#include <gcs/extensional.hh>
#include <gcs/variable_id.hh>
#include <unordered_map>
#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that the sequence of variables is a member of the
     * language recognised by the given multivalued decision diagram (MDD).
     *
     * \ingroup Constraints
     */
    class MDD : public Constraint
    {
    private:
        // This is mostly the same as the MiniZinc predicate, except we start at node 0 (root) and the final node is n-1
        const std::vector<IntegerVariableID> _vars;
        const long _num_nodes;          // Number of nodes (including the root node 0 and "True" final node _num_nodes-1)
        const std::vector<long> _level; // Level of root node must be 0, level of final node is _vars.size()
        const long _num_edges;
        const std::vector<long> _from;                  // _from[i] = j means edge i leaves node j
        const std::vector<std::vector<Integer>> _label; // Labels for each edge
        const std::vector<long> _to;                    // _to[i] = j meand edge i enters node j

    public:
        explicit MDD(std::vector<IntegerVariableID> vars,
            long num_nodes,
            std::vector<long> level,
            long num_edges,
            std::vector<long> from,
            std::vector<std::vector<Integer>> label,
            std::vector<long> to);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
