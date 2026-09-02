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
        };

        std::vector<Position> positions;
        std::vector<ExtensionalWord> words;
        bool initialised = false;
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

        ExtensionalData(std::vector<IntegerVariableID> vars, ExtensionalTuples tuples, std::shared_ptr<ExtensionalLiveTuples> live);
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
