#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EXTENSIONAL_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EXTENSIONAL_UTILS_HH

#include <gcs/extensional.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstdint>
#include <limits>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Cached "residual supports" for gcs::innards::propagate_extensional().
     *
     * For each (variable position, value) the last tuple found to support it. On
     * the next call, if that tuple is still selectable and still matches, the value
     * is known supported in O(1) without re-scanning the table. Non-backtrackable:
     * a stale residue is simply re-sought, and a residue never becomes unsound
     * across backtrack (a relaxed domain can only make more tuples selectable).
     * Indexed [var position][value - base]; \c base and the sizes are captured from
     * the first propagate() call, which happens at the root, so they cover every
     * value the variable can hold during search.
     *
     * \ingroup Innards
     */
    struct ExtensionalResidues
    {
        static constexpr std::uint32_t none = std::numeric_limits<std::uint32_t>::max();
        std::vector<std::vector<std::uint32_t>> support;
        std::vector<long long> base;
        bool initialised = false;
    };

    /**
     * \brief The set of tuples still selectable, owned by the propagator.
     *
     * A sparse set: \c dense[0, size) are the live tuple indices and \c position
     * is its inverse, so membership is a single comparison and removal is a swap
     * with the last live entry. Only \c size is backtrackable, which is what
     * makes this cheap: everything ever removed sits at an index at or above
     * \c size, and every removal at a deeper node swaps within [0, size), so
     * restoring \c size re-admits exactly the tuples dropped since. The order
     * within the live region differs after a backtrack, which changes only which
     * support witness is found first, never which values are supported -- so the
     * inferences, and the proof, are unchanged.
     *
     * This replaces using a selector variable's domain as the live set. That cost
     * 32 trailed IntervalSet edits per useful inference, because a domain shot
     * full of holes splits on every removal; here a removal is two stores and a
     * decrement, and nothing goes through State's inference path at all.
     *
     * \ingroup Innards
     */
    struct ExtensionalLiveTuples
    {
        std::vector<std::uint32_t> dense;
        std::vector<std::uint32_t> position;
        ConstraintStateHandle size_handle{0};

        [[nodiscard]] static auto create(State & initial_state, std::size_t n_tuples) -> std::shared_ptr<ExtensionalLiveTuples>;
    };

    /**
     * \brief The word the extensional propagator's bitsets are built from.
     *
     * Every shift, mask and round-up over those bitsets derives its constants
     * from \c extensional_word_bits, so the width is stated once here rather
     * than spelled 64 at each use.
     *
     * \ingroup Innards
     */
    using ExtensionalWord = std::uint64_t;

    /// \see ExtensionalWord
    /// \ingroup Innards
    constexpr std::size_t extensional_word_bits = std::numeric_limits<ExtensionalWord>::digits;

    /**
     * \brief How many ExtensionalWord words it takes to hold \c n_bits bits.
     *
     * \ingroup Innards
     */
    [[nodiscard]] constexpr auto extensional_words_for(std::size_t n_bits) -> std::size_t
    {
        return (n_bits + extensional_word_bits - 1) / extensional_word_bits;
    }

    /**
     * \brief Dense per-position membership tests for pass 1.
     *
     * Pass 1 asks "is this tuple's entry at position i still in variable i's
     * domain?" once per (live tuple, position). Answering it with
     * State::in_domain() means an out-of-line call that re-resolves the
     * variable's domain out of State and then walks an interval list -- 40% of
     * total runtime on a binary random instance, 59% on Crossword, measured.
     * The resolution is loop-invariant: only the value changes.
     *
     * So each position's domain is rasterised once per call into a bitmap over
     * that position's *table* value range (not the variable's, which can be
     * wider), and the test becomes a bounds check, a shift and a mask. The
     * number of membership tests is identical, and so are the tuples dropped --
     * this is only a cheaper way to ask the same question.
     *
     * The range comes from the tuples, so every value a tuple can hold is
     * addressable by construction, and a value outside it is not in the table
     * at all. A position whose range is wider than \c max_words words, or which
     * holds a wildcard, keeps the State::in_domain() path.
     *
     * \ingroup Innards
     */
    struct ExtensionalDomainBitmaps
    {
        /// Beyond this many words per position, rasterising costs more than
        /// the scans it saves, and the fallback is used instead. A measured
        /// word count, unrelated to extensional_word_bits happening to match.
        static constexpr std::size_t max_words = 64;

        /// Below this many live tuples, rasterising costs more than the
        /// in_domain() calls it replaces.
        static constexpr std::size_t min_live = 8;

        struct Position
        {
            long long base = 0;
            std::size_t n_values = 0;
            std::size_t offset = 0;
            bool usable = false;

            /// So that a constraint adopting another's support masks can check
            /// the layout they were built against is the one it computed for
            /// itself, rather than assume it. \see ExtensionalSupportMasks
            [[nodiscard]] auto operator==(const Position &) const -> bool = default;
        };

        std::vector<Position> positions;
        std::vector<ExtensionalWord> words;
        bool initialised = false;
    };

    /**
     * \brief The support masks a compact table filters with: one bitset of
     * \c n_words per (position, value), holding the tuples whose entry at that
     * position is that value.
     *
     * A separate object from the rest of ExtensionalCompactTable because it is
     * the only part that several constraints can share, and it is by far the
     * largest. It is a pure function of the tuples alone: every position's value
     * range is read off the table (see ExtensionalDomainBitmaps), never off a
     * variable's domain, so two constraints over the same tupleset lay out
     * byte-identical masks however different their scopes are. Everything else
     * the compact table owns -- the live words, the index over them, the
     * previous domains, the trail -- is per constraint and stays there.
     *
     * Crossword is why: twenty Table constraints over one 4 591-word dictionary,
     * which unshared is twenty copies of the same 146 KB. 2.9 MB does not fit in
     * a 512 KB L2 and one copy does, and mask loads in the filter pass are half
     * of that propagator's L2 misses and a third of the whole program's.
     *
     * Shared through Propagators::shared_derived_data(), keyed on the tuples'
     * address, which is what makes the sharing last exactly one solve. Built
     * lazily, by whichever of the sharers first decides it wants masks, and
     * read-only from then on -- so the only thing sharing it needs is that the
     * build happens once, and it is guarded by \c status rather than by a lock,
     * on the same single-threaded-per-solve footing as the rest of the
     * propagator's mutable scratch.
     *
     * \sa ExtensionalCompactTable
     * \ingroup Innards
     */
    struct ExtensionalSupportMasks
    {
        /**
         * Whether the masks have been built, and if so whether they can be used.
         * The build declines a table it cannot rasterise or that wants more
         * memory than the cap allows, and that verdict belongs to the tuples
         * rather than to the constraint that happened to ask first -- so it is
         * recorded here and the next sharer does not try again.
         */
        enum class Status
        {
            Unbuilt,
            Built,
            Declined
        };

        Status status = Status::Unbuilt;

        std::vector<ExtensionalWord> masks;
        std::vector<std::size_t> mask_at;
        std::size_t n_words = 0;

        /// The rasterisation the masks are indexed by. Kept so an adopting
        /// constraint can check it against its own: they must agree, since both
        /// come from the same tuples, and a mismatch would otherwise be a silent
        /// misread rather than a loud one.
        std::vector<ExtensionalDomainBitmaps::Position> positions;
    };

    /**
     * \brief Compact-table state for gcs::innards::propagate_extensional().
     *
     * The live-set algorithm re-tests every live tuple against every position on
     * every wake, so pass 1 costs what is *live*. Compact table makes it cost
     * what *changed*: the live set is a bitset over tuple indices, and for each
     * value removed from a variable's domain one word-wise `live &= ~support`
     * takes out every tuple that used it. Measured over this project's suite,
     * that is 2-13x fewer pass-1 operations, each of them a word AND rather than
     * a membership test.
     *
     * The set of tuples this leaves live, and therefore every inference pass 2
     * draws from it, is identical to what the live-set algorithm computes: both
     * end up with the tuples all of whose entries are still in domain. The
     * proof is unchanged.
     *
     * \sa ExtensionalLiveTuples
     * \ingroup Innards
     */
    struct ExtensionalCompactTable
    {
        /// Do not build masks larger than this, in words, per tupleset.
        /// The suite's largest is Renault-big at 755 623 words over 332 tables;
        /// a single table wanting more than this is better served by the
        /// live-set algorithm than by the memory.
        static constexpr std::size_t max_mask_words = 16 * 1024 * 1024;

        /**
         * How long table::Auto watches before deciding, and what it
         * looks for. Every threshold here is read off the measured suite:
         *
         *  - \c decide_after separates the instances that never amortise a mask
         *    build from the ones that do, and it is counted per propagator, not
         *    per search. Kakuro wakes a table one to three times in the whole
         *    search and Renault-megane about four; Crossword wakes one 1 898
         *    times, srch_k5 3 146, srch_bin_d20 19 068. Nothing sits between, so
         *    the threshold only has to be small enough that the wait itself does
         *    not cost anything: at 512 it left srch_k5 running 16% of its calls
         *    on the slower path, which was worth 36%.
         *  - \c min_mean_live is where a call starts doing enough work to cover
         *    the fixed cost of an update. Below it the compact table measured
         *    0.74-0.96x: Dubois at 2.3 live, enum_shared at 3.0, enum_func at
         *    12.8. Above it, 1.4x and upwards. It is a mean over the first
         *    \c decide_after wakes, which early in a search overestimates the
         *    steady state: srch_bin_d10_n20_s2 settles at 7.7 live but does not
         *    look like it yet at wake 32, and is the one instance where Auto
         *    loses (0.96x).
         *  - the density test is the one that is easy to miss. A bitset is only
         *    a good shape for the live set if its words are full: the support
         *    test costs a word per live word, where the live-set scan costs a
         *    step per tuple until it finds a witness. enum_single_k10_t200k
         *    keeps 46 tuples live in a 200 000-tuple table -- one per word --
         *    and measured 1.00x. Requiring \c extensional_word_bits * mean live >=
         *    tuples asks for at
         *    least one live tuple per word on average.
         */
        static constexpr unsigned long long decide_after = 32;
        static constexpr std::size_t min_mean_live = 16;

        /// A table whose tuples all fit in one word cannot pay for the compact
        /// table's per-call bookkeeping -- rasterising the domains twice,
        /// counting bits, keeping a trail -- however many times it is woken, so
        /// it does not even get the state that would let it try.
        static constexpr std::size_t min_tuples = extensional_word_bits;

        /**
         * The support masks, and the layout they are indexed by, copied out of
         * \c supports once it has been built. Values are indexed from the
         * position's ExtensionalDomainBitmaps::Position, so a value the table
         * never uses at that position is outside the range and is unsupported
         * without a lookup.
         *
         * A raw pointer plus its own copy of the small layout, rather than
         * reaching through \c supports, because both are read in the filter
         * loop's innermost test: that keeps it exactly the loads it was before
         * the masks moved out of here. \c supports below owns the storage the
         * pointer names, so it is valid for as long as this object is.
         */
        const ExtensionalWord * masks = nullptr;
        std::vector<std::size_t> mask_at;
        std::size_t n_words = 0;

        /**
         * The live tuples, as a sparse bitset: \c words holds the bits, and
         * \c index[0, limit) names the words that still have any set. Only
         * \c limit backtracks, by the same argument ExtensionalLiveTuples uses
         * for its size: a word only ever leaves the live region by swapping with
         * \c index[limit - 1], so restoring \c limit re-admits exactly the words
         * dropped below this node.
         */
        std::vector<ExtensionalWord> words;
        std::vector<std::uint32_t> index;
        std::size_t limit = 0;

        /**
         * What each position's domain held when this instance last ran on this
         * path, rasterised exactly as ExtensionalDomainBitmaps rasterises the
         * current one, so that the difference of the two is the set of values to
         * react to. It has to backtrack: a stale copy from a deeper node is a
         * subset of the truth, which would make the update miss removals.
         */
        std::vector<ExtensionalWord> previous_domain;

        /// Accumulates the union of the support masks being applied, so that the
        /// live words are written once per position rather than once per value.
        std::vector<ExtensionalWord> scratch;

        /**
         * The undo trail for \c words and \c previous_domain, which are the two
         * things that change value rather than merely membership.
         * State::on_backtrack is not reachable from a propagator's
         * `const State &`, so this follows the difference-logic propagator's
         * pattern: the trail itself is propagator-owned and never backtracked,
         * and a single trailed number says how much of it belongs to the current
         * epoch. It is unwound lazily at the top of the next call, which is safe
         * because nothing reads either array in between, and what is restored is
         * exact rather than reconstructed from the current domains.
         *
         * \c where indexes \c words below \c n_words and \c previous_domain
         * above it, so one trail covers both.
         */
        struct Undo
        {
            std::uint32_t where;
            ExtensionalWord was;
        };

        std::vector<Undo> trail;

        /// Sentinel \c where for a trail entry that carries the old \c limit
        /// rather than a word. Restoring the limit through the trail rather than
        /// through a second constraint state matters more than it looks: every
        /// slot is deep-copied into every search node, so a table that never
        /// ends up using the compact table would still pay for it at each node.
        /// Two slots cost Dubois 14% and enum_shared 24% before this.
        static constexpr std::uint32_t limit_marker = ~std::uint32_t{0};

        /// How much of \c trail belongs to the current epoch. A plain integer,
        /// which std::any holds without allocating.
        ConstraintStateHandle trail_mark_handle{0};

        /**
         * The masks, shared with every other constraint over the same tuples,
         * or private to this one where there is nothing to share with. Whoever
         * decides to build first builds; the rest adopt what is there.
         *
         * Down here with the cold fields on purpose: it is read once, when the
         * decision is made, and never again during propagation.
         */
        std::shared_ptr<ExtensionalSupportMasks> supports;

        /// table::Auto watches this many wakes before deciding; table::CompactTable
        /// builds at the first one. Once \c decided is set the answer never changes.
        bool forced = true;
        unsigned long long wakes = 0;
        unsigned long long total_live = 0;
        bool decided = false;
        bool built = false;

        /**
         * \param supports the masks to share, from
         * Propagators::shared_derived_data(); null for a caller with no other
         * constraint to share them with, which gets a private set.
         */
        [[nodiscard]] static auto create(State & initial_state, bool forced, std::shared_ptr<ExtensionalSupportMasks> supports = {})
            -> std::shared_ptr<ExtensionalCompactTable>;

        /**
         * \brief create() for a caller with no user-facing algorithm choice:
         * Auto, and null below \c min_tuples.
         *
         * The tabulated constraints and the AutoTable presolver build their own
         * ExtensionalData, so there is no TableAlgorithm to honour -- but the
         * \c min_tuples test still has to be applied, and for the same reason
         * `Table::prepare` applies it: a table that fits in one word cannot pay
         * for the bookkeeping, and every constraint state is deep-copied into
         * every search node whether the propagator uses it or not.
         */
        [[nodiscard]] static auto create_for_auto(State & initial_state, std::size_t n_tuples, std::shared_ptr<ExtensionalSupportMasks> supports = {})
            -> std::shared_ptr<ExtensionalCompactTable>;
    };

    /**
     * \brief Data for gcs::innards::propagate_extensional().
     *
     * \ingroup Innards
     */
    struct ExtensionalData
    {
        std::vector<IntegerVariableID> vars;
        ExtensionalTuples tuples;
        std::shared_ptr<ExtensionalResidues> residues = std::make_shared<ExtensionalResidues>();

        /**
         * Scratch for the pass-1 membership tests, rebuilt at the top of every
         * call. Held by shared_ptr like the residues, and for the same reason:
         * the propagator is called through a const reference, and propagators
         * are per-thread under parallel search, so a per-instance mutable
         * buffer is sound and needs no locking.
         */
        std::shared_ptr<ExtensionalDomainBitmaps> bitmaps = std::make_shared<ExtensionalDomainBitmaps>();

        /**
         * The reason for every inference this table makes, built once here rather
         * than by calling generic_reason(vars) at each inference site.
         *
         * Sound to hoist because the scope is fixed and Reason is declarative: it
         * captures the variables and defers reading their domains to
         * materialise(). The factories take their scope by value, so a per-site
         * call copies the whole scope vector into a fresh shared_ptr on every
         * inference -- and does it even with proofs off, where the reason is
         * never materialised at all.
         */
        Reason reason;

        /**
         * The live-tuple set. There is deliberately no selector variable here: the
         * selector exists only so that the OPB encoding has something to name, so
         * it is a proof-only variable owned by define_proof_model and the
         * propagator never sees it. Nothing this propagator infers mentions it --
         * the selector prunings were always NoJustificationNeeded, and VeriPB
         * re-derives them by unit propagation when it checks a `var != val` RUP.
         */
        std::shared_ptr<ExtensionalLiveTuples> live;

        /**
         * Non-null when this instance may use the compact-table algorithm: the
         * caller asked for it, or asked for Auto and the table is big enough to
         * be worth watching. Deliberately the last member, so that adding it
         * moves nothing the live-set path's hot loops touch -- placed before
         * \c reason it cost srch_k5 9% and Crossword 13% on the live-set path.
         */
        std::shared_ptr<ExtensionalCompactTable> compact = {};

        ExtensionalData(std::vector<IntegerVariableID> vars, ExtensionalTuples tuples, std::shared_ptr<ExtensionalLiveTuples> live,
            std::shared_ptr<ExtensionalCompactTable> compact = {});
    };

    /**
     * \brief Propagator for extensional constraints.
     *
     * This function performs propagation for the Table constraint, but also for
     * various other constraints that end up producing something table-like.
     *
     * The optional \c hint is the typed assertion hint carried on the
     * (RUP-derivable) prunings and contradictions: a constraint that owns its
     * propagation -- Table, the GAC linear encoding -- passes its own hint so the
     * assertions name it; a caller with no single owning constraint (e.g. the
     * AutoTable presolver, installed unnamed) omits it and the default \c NoHint
     * keeps the wire empty. Carried here rather than inside ExtensionalData since
     * it is a proof-only concern, orthogonal to the table data.
     *
     * \sa Table
     */
    template <typename Hint_ = NoHint>
    auto propagate_extensional(
        const ExtensionalData &, const State &, auto & inference_tracker, innards::ProofLogger * const, const Hint_ & hint = {}) -> PropagatorState;
}

#endif
