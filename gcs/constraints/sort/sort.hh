#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_SORT_SORT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_SORT_SORT_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/sort/sortedness.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that `y` is `x` sorted into non-decreasing order: `y`
     * is a multiset-permutation of `x` and `y[0] <= y[1] <= ... <= y[n-1]`.
     *
     * This is the value-sort constraint (MiniZinc `sort`, Gecode `sorted`).
     * Both arrays must have the same length. To recover the sorting
     * permutation as well, use ArgSort.
     *
     * \ingroup Constraints
     * \sa ArgSort
     */
    class Sort : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _x, _y;
        // Proof-only witness, populated by define_proof_model and read by the
        // propagator's justifications. See innards::SortednessWitness.
        innards::SortednessWitness _witness;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Sort(std::vector<IntegerVariableID> x, std::vector<IntegerVariableID> y);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
    };
}

#endif
