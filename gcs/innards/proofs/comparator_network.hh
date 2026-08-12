#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_COMPARATOR_NETWORK_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_COMPARATOR_NETWORK_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/integer.hh>

#include <map>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Deliberate corruptions of a comparator-network refutation, for
     * testing only.
     *
     * The network's arithmetic is long, and every step of it is *sound* in
     * isolation: a proof that merely stops early lands on a weaker line rather
     * than an invalid one. So the corruptions worth having are the ones that
     * make the endgame's sum come up short, or that ask propagation to do a
     * step cutting planes had to do explicitly. All but one of these is
     * rejected by VeriPB, and the one that is not says something worth knowing
     * about which steps propagation can reach on its own.
     *
     * \ingroup Innards
     */
    namespace comparator_network_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Leave the earlier task's `duration >= 1` out of the gap lemma. This
        /// is the fact an equal-duration construction gets for free, the
        /// duration sitting in the degree as a constant; with the duration
        /// muxed through the network instead, the degree drops to zero without
        /// it and a zero-length task can be "before" one it starts level with.
        struct DropPositivity
        {
        };

        /// Cite the *other* input's duration record in each half of the gap
        /// lemma, so the gap is measured against the wrong task's duration.
        /// Invisible at equal durations, which is what makes it the mutation
        /// that says this construction really does unequal ones.
        struct SwapDurations
        {
        };

        /// Ask RUP for the gap lemma rather than deriving it. The interesting
        /// one: it says the case split over the comparator's selector is
        /// load-bearing, and that propagation cannot get from the separation
        /// clause to the gap on its own.
        struct RupGap
        {
        };

        /// Ask RUP for a muxed duration's positivity. Kept although VeriPB
        /// *accepts* it: while every duration is pinned to a constant,
        /// propagation gets from the mux clauses to `d_out >= 1` on its own, so
        /// the case split below is buying predictable cost rather than reach
        /// --- an unhinted RUP is priced against the whole database, and the
        /// split is four lines. The day durations become variables the pins go
        /// and this stops passing, which is the other reason to keep it
        /// runnable.
        struct RupPositivity
        {
        };

        /// Ask RUP for a comparator's sum-preservation lemma.
        struct RupPreservation
        {
        };

        /// Leave the per-comparator sum-preservation rows out of the endgame.
        /// If this still refutes, the endgame never needed to know that the
        /// network permutes the durations rather than losing them.
        struct DropPreservation
        {
        };
    }

    using ComparatorNetworkMutation = std::variant<comparator_network_mutation::None, comparator_network_mutation::DropPositivity,
        comparator_network_mutation::SwapDurations, comparator_network_mutation::RupGap, comparator_network_mutation::RupPositivity,
        comparator_network_mutation::RupPreservation, comparator_network_mutation::DropPreservation>;

    /**
     * \brief A proof-only bit-encoded integer: `width` flags, read as
     * `sum_t 2^t * bits[t]`.
     *
     * A wire is either fresh (ComparatorNetwork::fresh_wire, its bits invented
     * by redundance) or a reading of flags that already exist
     * (ComparatorNetwork::wire_over, which is how a model variable's own bit
     * encoding enters the network). Either way nothing in the model has to
     * change: a fresh wire exists only between the `red` that introduces its
     * bits and the deletion that removes them, which is what lets a propagator
     * sort its tasks inside a proof without the OPB acquiring a sorting network
     * --- or, for that matter, a time index.
     *
     * Bits rather than ProofModel::create_proof_only_integer_variable_in_proof,
     * which is a *model*-side call and so unavailable to a propagator: a wire
     * introduced during search cannot be a model variable, and does not need to
     * be, every step below being cutting planes over the bits.
     *
     * A bit is anything a proof can name: a fresh flag, one bit of a model
     * variable's own encoding (which is how a propagator's tasks enter, without
     * a copy layer and without the model gaining anything), or a constant, which
     * is how a variable narrower than the network is padded up to it.
     *
     * `id` is the network's own handle for the wire, and is what its duration,
     * bounds and separations are filed under.
     *
     * \ingroup Innards
     */
    struct ProofWire
    {
        int id;
        std::vector<ProofLiteralOrFlag> bits;
    };

    /**
     * \brief One comparator's outputs, and the rows saying what they are.
     *
     * `selector` is true exactly when `a <= b`, so `lo` takes `a` and `hi`
     * takes `b`; each output is muxed bitwise on it, as is each output's
     * duration --- a comparator permutes whole tasks, not just their starts.
     * The record rows are the conditional statements the lemmas consume ---
     * `lo_ge_a` is `selector -> lo >= a`, and so on --- each one a `pol`, built
     * by multiplying the bit-`t` mux clause by `2^t` and summing.
     *
     * The guard coefficient on a record row comes out at `span` (the largest
     * value a wire of this width can take) and is deliberately left there:
     * ComparatorNetwork::transfer adds two of them and divides by a separation
     * row's guard coefficient, which is a clean one only while `2 * span` does
     * not exceed it.
     *
     * \ingroup Innards
     */
    struct Comparator
    {
        ProofFlag selector;

        /// The inputs, kept so that a lemma can name them without the caller
        /// having to hold on to them.
        ProofWire a, b, d_a, d_b;

        /// The outputs: the earlier task and the later one.
        ProofWire lo, hi, d_lo, d_hi;

        /// `selector -> b >= a`, and `~selector -> a >= b + 1`.
        ProofLine forward, reverse;

        /// The muxed record rows, `guard -> output (>= or <=) input`.
        ProofLine lo_ge_a, lo_le_a, lo_ge_b, lo_le_b;
        ProofLine hi_ge_b, hi_le_b, hi_ge_a, hi_le_a;
        ProofLine d_lo_ge_a, d_lo_le_a, d_lo_ge_b, d_lo_le_b;
        ProofLine d_hi_ge_b, d_hi_le_b, d_hi_ge_a, d_hi_le_a;
    };

    /**
     * \brief One direction of a pair's separation, as the model states it.
     *
     * `flag` is the model's "x runs before y" flag, `row` the forward half of
     * its reification (`M * ~flag + y - x >= duration(x)`), and
     * `guard_coefficient` the `M` that row carries --- which for a row emitted
     * by ProofModel::add_two_way_reified_constraint is
     * `-NamesAndIDsTracker::reification_shape(...).reif_coefficient`.
     *
     * The coefficient is per direction, not per pair, and asking for it rather
     * than assuming is not ceremony: a reifier sizes the constant from the
     * inequality it is given, so `before_{i,j}` and `before_{j,i}` differ
     * whenever the two tasks' durations or encoding widths do. Raising both by
     * the same amount leaves one of them short of the network's guard
     * coefficient, and every later division by it then rounds instead of
     * cancelling.
     *
     * \ingroup Innards
     */
    struct ModelSeparation
    {
        ProofFlag flag;
        ProofLine row;
        Integer guard_coefficient;
    };

    /**
     * \brief What sorting the tasks leaves behind, and all the endgame needs.
     *
     * \ingroup Innards
     */
    struct SortedTasks
    {
        /// The telescoping rows, each `upper - lower - duration(lower) >= 0`
        /// for one adjacent pair of the sorted order. Summing them collapses to
        /// `largest - smallest - (every duration but the largest's) >= 0`.
        std::vector<ProofLine> chain;

        /// One sum-preservation row per comparator, `d_lo + d_hi >= d_a + d_b`,
        /// which is what turns the sorted durations back into the instance's
        /// own.
        std::vector<ProofLine> preserved;

        /// `window_hi - largest - duration(largest) >= 0`.
        ProofLine top_upper_bound;

        /// `smallest - window_lo >= 0`.
        ProofLine bottom_lower_bound;
    };

    /**
     * \brief Builds proof-only comparator networks over bit-encoded integer
     * wires, and sorts tasks with them.
     *
     * The construction is the one issue #730 verified in simulation: wires
     * introduced by redundance, sorted by a network of comparators, with order
     * facts carried across each comparator and telescoped at the end. Its
     * distinguishing property is that it is *duration-magnitude invariant* ---
     * cost depends on the number of tasks and only logarithmically on their
     * range --- which is what makes it the certificate of choice where a
     * time-indexed re-encoding would be too wide.
     *
     * There are two layers here. The lower one is generic: wires, pins, and
     * comparators that mux a key and a payload on one selector. The upper one
     * sorts *tasks* --- values that are pairwise separated, each by one of the
     * two durations involved --- because that is the thing a disjunctive
     * resource has to sort, and because carrying a separation across a
     * comparator is the whole difficulty. A caller supplies its model's
     * separation rows through \ref add_separation and never has to know how
     * they are moved onto the sorted wires.
     *
     * Every step is emitted at the level the network was built with, so a
     * caller that wants the whole thing gone on backtracking asks for
     * ProofLevel::Temporary and a caller amortising it over many firings asks
     * for ProofLevel::Top.
     *
     * \ingroup Innards
     */
    class ComparatorNetwork
    {
    private:
        /// A separation as the lemmas want it: which row holds when each wire
        /// goes first, and the clause saying one of them does. Both rows carry
        /// \ref big as their guard coefficient, whatever they were derived
        /// from --- which is what \ref add_separation raises a model row to,
        /// and what lets a transfer lemma divide by a constant it knows.
        struct Separation
        {
            std::map<int, ProofLine> first;
            ProofLine clause;
        };

        ProofLogger & _logger;
        int _width;
        Integer _window_lo, _window_hi;
        ProofLevel _level;
        ComparatorNetworkMutation _mutation;
        Integer _span, _big, _div;
        long long _counter = 0;
        int _next_wire_id = 0;

        /// Each start wire's duration wire, and each duration wire's `>= 1` row
        /// and `<= its pinned value` row.
        std::map<int, ProofWire> _duration;
        std::map<int, ProofLine> _positivity, _duration_upper;

        /// What makes a state-dependent row vacuous; see \ref assume.
        WPBSum _guard;

        /// Each start wire's `window_hi - wire - duration(wire) >= 0` and
        /// `wire - window_lo >= 0`.
        std::map<int, ProofLine> _upper, _lower;

        /// Keyed by the pair of wire ids, smaller first.
        std::map<std::pair<int, int>, Separation> _separations;

        [[nodiscard]] auto next_name(const std::string & stem) -> std::string;

        [[nodiscard]] auto separation_between(const ProofWire &, const ProofWire &) const -> const Separation &;

        auto record_separation(const ProofWire &, ProofLine when_first, const ProofWire &, ProofLine when_other_first, ProofLine clause) -> void;

        /// The four `red`s reifying "x runs before y" and "y runs before x" on
        /// a pair of fresh flags, returning the two forward rows and the two
        /// reverse ones.
        struct SeparationFlags
        {
            ProofFlag x_first, y_first;
            ProofLine x_first_row, x_first_reverse, y_first_row, y_first_reverse;
        };

        [[nodiscard]] auto reify_separation(const ProofWire & x, const ProofWire & y, const std::string & stem) -> SeparationFlags;

        [[nodiscard]] auto case_split(const WPBSumLE & goal, const std::vector<ProofLine> & guarded_halves) -> ProofLine;

        auto derive_positivity(const ProofWire & out, const std::vector<std::pair<ProofLine, ProofWire>> & halves) -> void;

        [[nodiscard]] auto derive_preservation(const Comparator &) -> ProofLine;

        [[nodiscard]] auto derive_gap(const Comparator &) -> ProofLine;

        [[nodiscard]] auto derive_dominance(const Comparator &) -> ProofLine;

        [[nodiscard]] auto derive_bound(const Comparator &, const ProofWire & out, const ProofWire & d_out, ProofLine le_a, ProofLine le_b,
            ProofLine d_le_a, ProofLine d_le_b) -> ProofLine;

        [[nodiscard]] auto derive_lower_bound(const Comparator &, const ProofWire & out, ProofLine ge_a, ProofLine ge_b) -> ProofLine;

        auto separate_from_gap(const ProofWire & x, const ProofWire & y, ProofLine gap) -> void;

        auto transfer(const ProofWire & out, const ProofWire & other, const Comparator &, ProofLine le_a, ProofLine ge_a, ProofLine le_b,
            ProofLine ge_b, ProofLine d_le_a, ProofLine d_le_b) -> void;

    public:
        /**
         * `width` bits per wire, which must be enough for every value the
         * caller pins or bounds, and `[window_lo, window_hi)` the window whose
         * tasks are being sorted --- for a whole-problem refutation that is
         * `[0, horizon)`, and for a propagator it is the overloaded window.
         *
         * The guard coefficient every conditional row carries is derived from
         * the width and the window: it has to dominate twice a wire's span, so
         * that a transfer lemma's division comes out at one, and to reach the
         * guard coefficient of the caller's own rows, so that \ref
         * add_separation can raise them to it.
         */
        explicit ComparatorNetwork(ProofLogger &, int width, Integer window_lo, Integer window_hi, ProofLevel,
            ComparatorNetworkMutation = comparator_network_mutation::None{});

        [[nodiscard]] auto width() const -> int;
        [[nodiscard]] auto span() const -> Integer;
        [[nodiscard]] auto big() const -> Integer;

        /// A fresh wire, its bits unconstrained until something pins or defines
        /// them.
        [[nodiscard]] auto fresh_wire(const std::string & stem) -> ProofWire;

        /**
         * A wire reading bits that already exist --- a model variable's own
         * encoding, most often. Nothing is emitted.
         *
         * Fewer bits than the network's width are padded with constant zeroes,
         * so a window's tasks can have been encoded to different widths and
         * still be compared. More is an error: the network's guard coefficients
         * are sized from its width, and a wire that overflows them would make
         * every guarded row it appears in unsound.
         *
         * The bits must read as an unsigned magnitude, least significant first.
         * A two's-complement encoding's sign bit is not that, and a comparator
         * muxing one into an unsigned output would land on the wrong value, so
         * a caller with a possibly-negative variable has to say so some other
         * way --- which for the disjunctive overload check means a window whose
         * tasks all start at or after zero.
         */
        [[nodiscard]] auto wire_over(const std::vector<ProofLiteralOrFlag> & bits) -> ProofWire;

        /// `sign * wire` as pseudo-Boolean terms, for building a row about it.
        [[nodiscard]] auto terms(const ProofWire &, Integer sign) const -> WPBSum;

        /// The same, appended to a sum already under construction, which is
        /// what a row mentioning several wires needs.
        auto add_terms(WPBSum &, const ProofWire &, Integer sign) const -> void;

        /**
         * Fix a fresh wire to a constant, one `red` per bit. The witness is
         * single-variable and the wire is fresh, so both proofgoals autoprove
         * and no subproof is needed.
         */
        auto pin(const ProofWire &, Integer value) -> void;

        /**
         * Give a wire a duration, pinned to a constant, and derive the
         * `duration >= 1` the gap lemma needs. A zero-duration task is exactly
         * the case a non-strict Disjunctive drops from the constraint, so
         * requiring a positive duration costs no generality.
         */
        auto add_task(const ProofWire & start, Integer duration) -> void;

        /**
         * State that every bound below holds only where `guard` is zero.
         *
         * A propagator's window is a fact about the search state, not about the
         * model, so the rows saying a task fits inside it have to be guarded by
         * the inference's reason. That guard cannot simply ride along: the
         * bounds are carried across each comparator by a case split, and a case
         * split works by adding the negated goal to each half and dividing, so
         * a term the halves carry and the goal does not survives the division
         * and the split lands on something sound but not closing.
         *
         * So the guard is declared once and the network puts it on both sides:
         * on the rows it emits for the bounds, and on every goal derived from
         * them. `guard` is a sum of `big() * ~literal`, one per reason literal
         * --- a uniform coefficient, since two rows guarded by the *same*
         * reason at *different* coefficients cancel no better than two rows
         * guarded by different reasons.
         *
         * Left empty (the default) for a whole-problem refutation, where the
         * bounds come from the model and hold outright.
         */
        auto assume(const WPBSum & guard) -> void;

        /**
         * Emit the window's bounds for a task: `start + duration <= window_hi`
         * and `start >= window_lo`, each as one RUP carrying \ref assume's
         * guard.
         *
         * The network emits these rather than taking them, so that the guard on
         * a bound and the guard on the goals derived from it cannot drift
         * apart. Both close by propagation --- from the model's own bound rows
         * for a refutation, and from the reason's order atoms for a propagator.
         *
         * The lower bound is free when the window starts at zero and the wire
         * is a bit vector, and load-bearing otherwise: the endgame telescopes
         * down to the *earliest* task's start, and what makes that a refutation
         * is that it cannot be earlier than the window it was selected for.
         */
        auto set_bounds(const ProofWire & start) -> void;

        /**
         * Take a pair of tasks' separation from the model and put it in the
         * form the lemmas want: `x_first` says x runs before y, `y_first` the
         * other way round, and `clause` says one of them does.
         *
         * The rows are made duration-relative (the pinned duration subtracted,
         * so the network can carry them across a mux) and raised to the
         * network's own guard coefficient, which neither may exceed.
         */
        auto add_separation(
            const ProofWire & x, const ModelSeparation & x_first, const ProofWire & y, const ModelSeparation & y_first, ProofLine clause) -> void;

        /**
         * Introduce a comparator over two tasks already in play: a selector
         * reifying `a <= b` by two `red`s, four bitwise muxes per output bit
         * and per output duration bit, and the conditional record rows those
         * give by `pol`.
         */
        [[nodiscard]] auto compare(const ProofWire & a, const ProofWire & b, const std::string & stem) -> Comparator;

        /**
         * Sort the tasks by selection sort, carrying every separation across
         * every comparator, and return the telescoping chain.
         *
         * Every task must have had \ref add_task, \ref set_upper_bound and a
         * \ref add_separation against each of the others.
         */
        [[nodiscard]] auto sort(const std::vector<ProofWire> & tasks) -> SortedTasks;

        /**
         * The endgame: sum the chain, add the largest task's upper bound, and
         * turn the sorted durations back into the instance's own.
         *
         * The row returned says the window is at least as wide as the total
         * work in it --- so if the tasks do not fit, it is contradictory
         * outright and any RUP closes. Emitting that contradiction is left to the caller, which
         * inside a propagator means `ThenRUP::Yes` under a reason rather than a
         * bare line.
         */
        [[nodiscard]] auto sum_up(const SortedTasks &) -> ProofLine;
    };
}

#endif
