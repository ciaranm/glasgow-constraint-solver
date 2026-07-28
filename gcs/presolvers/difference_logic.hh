#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_DIFFERENCE_LOGIC_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_DIFFERENCE_LOGIC_HH

#include <gcs/constraints/difference/difference_incremental.hh>
#include <gcs/constraints/difference/difference_simplify.hh>
#include <gcs/presolver.hh>

#include <cstddef>
#include <memory>

namespace gcs
{
    /**
     * \brief What the difference-logic presolver did, filled in when it runs.
     *
     * The presolver's whole job is invisible from the outside: it adds no OPB
     * content, changes no solution, and leaves proofs verifying whether it fired
     * or not. A presolver that silently lifted nothing --- because, say,
     * Constraint::clone() stopped flattening a posted LinearLessThanEqual to
     * ReifiedLinearInequality --- would pass every solution-equivalence, OPB
     * byte-diff and VeriPB check there is. So the counts are not decoration:
     * they are how the tests, and the measurements, tell "working" from
     * "no-op". \sa DifferenceLogic
     *
     * \ingroup Presolvers
     */
    struct DifferenceLogicStats
    {
        /// Donors turned into graph edges: the number that matters.
        std::size_t edges_lifted = 0;

        /**
         * \brief How many of edges_lifted came from a Comparison donor
         * (`LessThan`, `LessThanEqual`, `GreaterThan`, `GreaterThanEqual` and
         * their `If` forms) rather than from a two-term linear.
         *
         * Broken out because it is a separate detection path over a separate
         * class hierarchy, reading the constraint back through
         * ReifiedCompareLessThanOrMaybeEqual's accessors rather than through a
         * WeightedSum, and because it is the one that can regress silently on
         * its own: a model built entirely out of `x <= y + d` would still lift
         * its linears and still look busy.
         */
        std::size_t comparison_edges_lifted = 0;

        /**
         * \brief How many of edges_lifted came from a half-reified (`reif::If`)
         * donor, and so joined the graph as `cond -> x - y <= d`.
         *
         * Broken out rather than counted separately because these are the edges
         * a disjunctive encoding contributes, which is where the paper's
         * scheduling wins come from --- and because they are the ones whose
         * donors must *not* be retired (see DifferenceLogic::disabling_lifted_donors).
         */
        std::size_t half_reified_edges_lifted = 0;

        /// Distinct variables those edges span.
        std::size_t nodes = 0;

        /// True if a global propagator was actually installed.
        bool propagator_installed = false;

        /// Propagators retired by the donors-off option.
        std::size_t donor_propagators_disabled = 0;

        /**
         * \name Why a candidate was not lifted.
         *
         * Every donor the presolver looked at, of either family, falls into
         * exactly one of edges_lifted or one of these five buckets, so the six
         * numbers together account for every ReifiedLinearInequality *and*
         * every ReifiedCompareLessThanOrMaybeEqual in the model. (The first two
         * only ever fire on a linear: a comparison is two terms with
         * coefficients +1 and -1 by construction.)
         * @{
         */

        /// A linear that is not exactly two terms.
        std::size_t skipped_not_two_terms = 0;

        /// A two-term linear whose coefficients are not exactly +1 and -1.
        std::size_t skipped_coefficients = 0;

        /// A donor whose reification condition is neither reif::MustHold nor
        /// reif::If: MustNotHold, NotIf or Iff. Each of those *is* expressible
        /// as one or two difference edges. Iff cannot be lifted as things
        /// stand, because its halves are labelled with the roles r and f rather
        /// than with the empty role the propagator cites; MustNotHold and NotIf
        /// could be, and are a deliberate gap, to be closed for both donor
        /// families at once rather than for one of them. Counted rather than
        /// guessed at.
        std::size_t skipped_reified = 0;

        /// An operand that is a negated view (`-X + c`), which is not a
        /// difference constraint at all.
        std::size_t skipped_negated_view = 0;

        /// An edge that canonicalises to `0 <= d` (both operands the same
        /// variable, or both constants), or to a plain bound on one variable
        /// (one constant operand). Nothing is gained by lifting these and the
        /// `d < 0` case would need an initialiser, a door that has closed by
        /// the time a presolver runs, so they are left to their own propagator.
        std::size_t skipped_degenerate = 0;

        ///@}
    };

    /**
     * \brief Scan a posted Problem for difference-shaped constraints and install
     * a global difference-logic propagator over them, alongside the constraints'
     * own propagators.
     *
     * A model does not have to be rewritten against DifferenceConstraints to get
     * the global propagation: post `1*x + -1*y <= d` as an ordinary
     * LinearLessThanEqual, or `x <= y + d` as an ordinary LessThanEqual, add
     * this presolver, and the edges are lifted into one Bellman-Ford pass over
     * the whole graph. This is the hybrid of section 4.4
     * of Kletzander, Dekker, Schutt and Stuckey, "Global Difference Constraint
     * Propagation for Constraint Programming" (arXiv:2607.20022) --- and it is
     * what the timing forces in any case, since presolvers run after
     * create_propagators and after the proof model has been finalised, so the
     * donors' propagators cannot be removed and no new OPB content can be added.
     *
     * That timing is not a limitation, it is what makes the proofs trivial. Each
     * donor already emitted its own labelled OPB row; the global propagator
     * simply cites those rows in its `pol`s, and derives nothing that is not a
     * cutting-planes consequence of constraints the model already contains.
     *
     * Off by default: the paper's own MiniZinc-wide result is near-noise, so
     * this is opted into with Problem::add_presolver, not applied automatically.
     *
     * \par What is lifted
     *
     * The paper's "level 1", restricted to what the propagator supports today,
     * from two donor families:
     *
     *  - a two-term LinearLessThanEqual with coefficients exactly `+1` and `-1`
     *    and two distinct variable operands;
     *  - a Comparison --- LessThan, LessThanEqual, GreaterThan,
     *    GreaterThanEqual --- over two distinct variable operands, which is the
     *    same thing written the way a model usually writes it: `x <= y + d` is
     *    a view on one side, not a separate constraint kind.
     *
     * Either operand may carry a `+X + c` view offset, folded into the weight.
     * The reification condition may be unconditional (reif::MustHold), giving a
     * plain edge, or half-reified (reif::If), giving `cond -> x - y <= d`: both
     * families label both forms `@c[<id>]` with no role suffix, so all four are
     * citable, and the `If` form's row is emitted under
     * HalfReifyOnConjunctionOf, which is exactly the shape the propagator's
     * proofs assume. Everything else is skipped and counted --- see
     * DifferenceLogicStats.
     *
     * Equalities (level 2) and disequalities (level 3) are not chased at all;
     * the paper measures both as losing to level 1.
     *
     * \ingroup Presolvers
     */
    class DifferenceLogic : public Presolver
    {
    private:
        std::shared_ptr<DifferenceLogicStats> _stats;
        std::shared_ptr<DifferenceSimplificationStats> _simplification_stats;
        bool _disable_lifted_donors;
        bool _simplify;
        innards::DifferenceIncrementalOptions _incremental;

    public:
        /**
         * \brief Construct the presolver, optionally sharing a stats block that
         * will be filled in when it runs.
         *
         * The block is shared, not copied, so it survives Problem::add_presolver
         * cloning the presolver and can be read after solving.
         */
        explicit DifferenceLogic(std::shared_ptr<DifferenceLogicStats> stats = nullptr);

        /**
         * \brief Also retire the propagators of every *unconditional* donor
         * whose edge was lifted, so only the global propagator runs over them.
         *
         * Ships off, because the hybrid is what the paper measures as best; this
         * exists so the alternative can be measured rather than assumed. It is
         * also a soundness tripwire, and a strong one: the global propagator
         * subsumes every unconditional donor's single-edge bound push, and
         * disabling a propagator changes neither degrees nor adjacency, so the
         * search tree must come out *identical* either way. It differing means
         * the subsumption claim is wrong.
         *
         * Half-reified donors are **never** retired, however many of their edges
         * were lifted. Subsumption fails for them in one direction: a
         * `LinearLessThanEqualIf` also infers `!cond` when its bounds make the
         * inequality impossible, and the global propagator makes no inference
         * about a condition at all (that is the paper's `IncImp`, deliberately
         * not implemented). Retiring one would lose that inference, which is a
         * completeness loss no proof could catch.
         */
        auto disabling_lifted_donors(bool = true) -> DifferenceLogic &;

        /**
         * \brief Run (or do not run) the root simplification stage over the
         * lifted graph.
         *
         * On by default, matching DifferenceConstraints, and for the same
         * reason: the paper's section 6.3 measures the simplification stage as
         * most of the difference-logic win. It is exactly the same code and the
         * same proof shapes from either entry point --- it runs inside the shared
         * propagator, on its first call, precisely because a presolver runs after
         * propagators.initialise() and so has no initialiser available and no way
         * to infer anything itself.
         */
        auto simplifying_at_root(bool = true) -> DifferenceLogic &;

        /**
         * \brief Share a stats block the simplification stage will fill in.
         *
         * Separate from DifferenceLogicStats because the presolver's own counts
         * are known when it runs, whereas the simplification's are only known
         * once the propagator has first fired.
         */
        auto reporting_simplification_to(std::shared_ptr<DifferenceSimplificationStats>) -> DifferenceLogic &;

        /**
         * \brief Propagate the lifted system incrementally (the default), or
         * from scratch on every wake.
         *
         * \sa DifferenceConstraints::incrementally
         */
        auto incrementally(bool = true) -> DifferenceLogic &;

        /**
         * \brief Re-run the from-scratch pass after every incremental call and
         * require the two to agree. For tests.
         *
         * \sa DifferenceConstraints::auditing_incremental_propagation
         */
        auto auditing_incremental_propagation(bool = true) -> DifferenceLogic &;

        [[nodiscard]] virtual auto run(Problem &, innards::Propagators &, innards::State &, innards::ProofLogger * const) -> bool override;
        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Presolver> override;
    };
}

#endif
