#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_NOGOODS_NOGOODS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_NOGOODS_NOGOODS_HH

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

    class Nogoods;

    namespace innards
    {
        /**
         * \brief A live, growable set of nogoods, shared between the Nogoods
         * constraint's propagator and the search driver that appends to it (the
         * restart loop). Held by shared_ptr so a nogood can be added mid-search
         * while the propagator reads the same store. The scan path initialises a
         * newly added nogood's watches lazily on its next wake; the refined path
         * does so only at its next root re-propagation (normally the next
         * restart; see issue #1390).
         *
         * Internal, and deliberately so (#1393). A nogood added here is
         * enforced only if it is added at a point where the proof already has
         * it and the propagator will next run from a root, which is what the
         * restart loop arranges: it derives each learned clause at `Top`
         * (`emit_learned_nogood`) before adding it, at a restart boundary. A
         * caller adding one anywhere else, from a solution callback say, gets a
         * nogood the refined path never arms and the scan path enforces without
         * a derivation, so VeriPB rejects its first use.
         *
         * \ingroup Innards
         */
        class NogoodStore
        {
        public:
            /**
             * \brief Append a nogood. Called by the owning search thread
             * between propagations (at a restart boundary), not concurrently
             * with the propagator.
             */
            auto add(Nogood nogood) -> void;

            [[nodiscard]] auto size() const -> std::size_t;

        private:
            friend class gcs::Nogoods;
            std::shared_ptr<std::vector<Nogood>> _nogoods = std::make_shared<std::vector<Nogood>>();
            std::shared_ptr<std::vector<std::vector<IntegerVariableID>>> _vars = std::make_shared<std::vector<std::vector<IntegerVariableID>>>();
        };

        /**
         * \brief A Nogoods over a store the search driver grows during search,
         * with the variables to wake on (the restart loop passes every problem
         * variable, since a later-learned nogood may mention any of them).
         *
         * \param refined use refined per-literal watches; false gives the
         * coarse scan path. The restart loop passes true unless
         * GCS_LEARNED_NOGOODS_SCAN is set (stage C-2, issue #335).
         *
         * \ingroup Innards
         */
        [[nodiscard]] auto nogoods_over_learned_store(std::shared_ptr<NogoodStore> store, std::vector<IntegerVariableID> trigger_vars, bool refined)
            -> Nogoods;
    }

    /**
     * \brief Forbid each of a set of nogoods --- for every nogood, at least one
     * of its literals must be false.
     *
     * Each nogood is a conjunction of `=` / `≠` / `≥` / `<` / `∈ [lo, hi]` /
     * `∉ [lo, hi]` literals (the decisions on a refuted branch); the constraint
     * asserts the negation of each conjunction, i.e. the clause of the negated
     * literals. Propagation is
     * per-clause unit propagation by two watched literals with *entailment-based*
     * watching: a literal `x ≥ 10` counts as held once `lower(x) ≥ 10`, so an
     * `x ≥ 12` bound makes it hold too. The maintained consistency is unit
     * propagation on each clause individually, **not** GAC over the conjunction
     * of clauses (which would be co-NP-hard).
     *
     * Posted with a fixed set of nogoods, whose clauses are defined in the
     * proof model up front. The restart loop builds one internally over an
     * innards::NogoodStore that it grows during search, whose clauses are
     * derived in the proof as they are learned rather than declared here
     * (innards::nogoods_over_learned_store).
     *
     * \ingroup Constraints
     */
    class Nogoods : public Constraint
    {
    private:
        std::shared_ptr<innards::NogoodStore> _store;
        std::vector<IntegerVariableID> _trigger_vars;
        // Whether to use refined per-literal watches (true) or the coarse
        // wake-on-every-trigger-var-and-scan-the-whole-store path (false). The
        // fixed-nogoods constructor defaults to refined; the restart loop asks
        // for refined unless GCS_LEARNED_NOGOODS_SCAN is set (issue #335, stage
        // C-2).
        bool _refined;

        Nogoods(std::shared_ptr<innards::NogoodStore> store, std::vector<IntegerVariableID> trigger_vars, bool refined);
        friend auto innards::nogoods_over_learned_store(std::shared_ptr<innards::NogoodStore>, std::vector<IntegerVariableID>, bool) -> Nogoods;

        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        /**
         * \brief A fixed set of nogoods; the propagator wakes on the variables
         * they mention.
         *
         * \param refined use refined per-literal watches (the default); pass
         * false to force the coarse whole-store-scan path (used to compare the
         * two in tests).
         */
        explicit Nogoods(std::vector<Nogood> nogoods, bool refined = true);

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
