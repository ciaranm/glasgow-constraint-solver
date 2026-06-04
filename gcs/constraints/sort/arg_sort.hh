#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_SORT_ARG_SORT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_SORT_ARG_SORT_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/sort/sortedness.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that `p` is the (stable) sorting permutation of `x`:
     * `p` is a permutation of `{offset, ..., offset + n - 1}` such that
     * `x[p[j] - offset] <= x[p[j + 1] - offset]`, with ties broken by original
     * index (`x[p[j] - offset] == x[p[j + 1] - offset]` implies
     * `p[j] < p[j + 1]`).
     *
     * This is the index-sort constraint (MiniZinc `arg_sort`). By default `p`
     * is zero-based; pass `offset` (e.g. `1_i`) for a different index base.
     *
     * \ingroup Constraints
     * \sa Sort
     */
    class ArgSort : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _x, _p;
        // Internal real "sorted value" variables y[j] = x[p[j]]. They are not
        // exposed to the user; ArgSort runs the shared sortedness helpers on
        // {x, y} to reuse the Mehlhorn-Thiel bounds(Z) propagator and certified
        // proof, and channels them to p. Allocated in prepare().
        std::vector<SimpleIntegerVariableID> _y;
        // The sortedness witness from define_sortedness_proof_model, kept so the
        // ArgSort proof model can channel its permutation p to the stable rank
        // pos[k], and the rank-interval propagator can justify p prunings.
        innards::SortednessWitness _witness;
        Integer _offset;
        Integer _lowest_x{0_i}, _highest_x{0_i};

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit ArgSort(std::vector<IntegerVariableID> x, std::vector<IntegerVariableID> p, Integer offset = 0_i);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
