#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_NOGOODS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_NOGOODS_HH

#include <gcs/constraint.hh>
#include <gcs/variable_condition.hh>

#include <cstddef>
#include <memory>
#include <vector>

namespace gcs
{
    /**
     * \brief A single nogood: a conjunction of decision literals that together
     * lead to failure, and so must not all hold.
     */
    using Nogood = std::vector<IntegerVariableCondition>;

    /**
     * \brief A live, growable set of nogoods, shared between the Nogoods
     * constraint's propagator and whoever appends to it during search (the
     * restart loop). Held by shared_ptr so a nogood can be added mid-search while
     * the propagator reads the same store; the propagator initialises a newly
     * added nogood's watches lazily on its next fire.
     *
     * It is owned by the search driver (or, later, a per-thread parallel worker),
     * never by user code --- restart nogoods are an internal mechanism.
     *
     * \ingroup Constraints
     */
    class NogoodStore
    {
    public:
        /**
         * \brief Append a nogood. Called by the owning search thread between
         * propagations (e.g. at a restart boundary), not concurrently with the
         * propagator.
         */
        auto add(Nogood nogood) -> void;

        [[nodiscard]] auto size() const -> std::size_t;

    private:
        friend class Nogoods;
        std::shared_ptr<std::vector<Nogood>> _nogoods = std::make_shared<std::vector<Nogood>>();
        std::shared_ptr<std::vector<std::vector<IntegerVariableID>>> _vars =
            std::make_shared<std::vector<std::vector<IntegerVariableID>>>();
    };

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
     * It can be built two ways: with a fixed set of nogoods (whose clauses are
     * defined in the proof model up front), or over an externally owned
     * NogoodStore that the restart loop grows during search (those clauses are
     * derived in the proof as they are learned, not declared here).
     *
     * \ingroup Constraints
     */
    class Nogoods : public Constraint
    {
    private:
        std::shared_ptr<NogoodStore> _store;
        std::vector<IntegerVariableID> _trigger_vars;

        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        /**
         * \brief A fixed set of nogoods; the propagator wakes on the variables
         * they mention.
         */
        explicit Nogoods(std::vector<Nogood> nogoods);

        /**
         * \brief An externally owned store, grown during search, with the
         * variables to wake on (the restart loop passes every problem variable,
         * since a later-learned nogood may mention any of them).
         */
        Nogoods(std::shared_ptr<NogoodStore> store, std::vector<IntegerVariableID> trigger_vars);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
