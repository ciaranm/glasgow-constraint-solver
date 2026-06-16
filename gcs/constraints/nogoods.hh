#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_NOGOODS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_NOGOODS_HH

#include <gcs/constraint.hh>
#include <gcs/variable_condition.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief A single nogood: a conjunction of decision literals that together
     * lead to failure, and so must not all hold.
     */
    using Nogood = std::vector<IntegerVariableCondition>;

    /**
     * \brief Forbid each of a set of nogoods --- for every nogood, at least one
     * of its literals must be false.
     *
     * Each nogood is a conjunction of `=` / `≠` / `≥` / `≤` literals (the
     * decisions on a refuted branch); the constraint asserts the negation of each
     * conjunction, i.e. the clause of the negated literals. Propagation is
     * per-clause unit propagation by two watched literals with *entailment-based*
     * watching: a literal `x ≥ 10` counts as held once `lower(x) ≥ 10`, so an
     * `x ≥ 12` bound makes it hold too. The maintained consistency is unit
     * propagation on each clause individually, **not** GAC over the conjunction
     * of clauses (which would be co-NP-hard).
     *
     * This is the engine half of the restart-nogood machinery (issue #315). For
     * now it takes a fixed set of nogoods at construction; feeding it nogoods
     * extracted at restart boundaries is a later step.
     *
     * \ingroup Constraints
     */
    class Nogoods : public Constraint
    {
    private:
        std::vector<Nogood> _nogoods;

        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Nogoods(std::vector<Nogood> nogoods);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
