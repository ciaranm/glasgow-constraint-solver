#include <algorithm>
#include <any>
#include <bit>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <gcs/constraints/divide_modulus/hints.hh>
#include <gcs/constraints/extensional_utils.hh>
#include <gcs/constraints/linear/hints.hh>
#include <gcs/constraints/multiply/hints.hh>
#include <gcs/constraints/plus_minus/hints.hh>
#include <gcs/constraints/power/hints.hh>
#include <gcs/constraints/table/hints.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/innards/state.hh>
#include <gcs/proof.hh>
#include <limits>
#include <optional>
#include <utility>

using std::any_cast;
using std::make_shared;
using std::shared_ptr;
using std::size_t;
using std::uint32_t;
using std::vector;
using std::visit;

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::ExtensionalLiveTuples::create(State & initial_state, size_t n_tuples) -> shared_ptr<ExtensionalLiveTuples>
{
    auto result = make_shared<ExtensionalLiveTuples>();
    result->dense.resize(n_tuples);
    result->position.resize(n_tuples);
    for (size_t i = 0; i < n_tuples; ++i)
        result->dense[i] = result->position[i] = static_cast<uint32_t>(i);
    // Only the count backtracks: see the class comment for why restoring it is
    // enough to re-admit exactly the tuples dropped below this node.
    result->size_handle = initial_state.add_constraint_state(n_tuples);
    return result;
}

auto gcs::innards::ExtensionalCompactTable::create(State & initial_state, bool forced) -> shared_ptr<ExtensionalCompactTable>
{
    auto result = make_shared<ExtensionalCompactTable>();
    result->forced = forced;
    // One plain integer, which std::any holds without allocating. Everything
    // else the compact table owns is restored by unwinding the trail down to
    // it: the words, the previous domains, and the limit.
    result->trail_mark_handle = initial_state.add_constraint_state(size_t{0});
    return result;
}

gcs::innards::ExtensionalData::ExtensionalData(
    vector<IntegerVariableID> vars, ExtensionalTuples tuples, shared_ptr<ExtensionalLiveTuples> live, shared_ptr<ExtensionalCompactTable> compact) :
    vars(move(vars)), tuples(move(tuples)), reason(generic_reason(this->vars)), live(move(live)), compact(move(compact))
{
}

namespace
{
    auto match(const Integer & a, const Integer & b) -> bool
    {
        return a == b;
    }

    auto match(const Wildcard &, const Integer &) -> bool
    {
        return true;
    }

    auto match(const IntegerOrWildcard & a, const Integer & b) -> bool
    {
        return visit([&](auto & a) { return match(a, b); }, a);
    }

    template <typename T_>
    auto get_tuple_value(const vector<T_> & t, unsigned tuple_idx, unsigned entry)
    {
        return t[tuple_idx][entry];
    }

    template <typename T_>
    auto get_tuple_value(const ArrayParam<T_> & t, unsigned tuple_idx, unsigned entry)
    {
        return get_tuple_value(*t, tuple_idx, entry);
    }

    // The value range a position can take across the whole table. nullopt if any
    // tuple has a wildcard there, since then no membership test happens at all.
    auto tuple_value_range(const Integer & v, std::optional<std::pair<long long, long long>> & range) -> bool
    {
        if (! range)
            range = std::pair{v.raw_value, v.raw_value};
        else {
            range->first = std::min(range->first, v.raw_value);
            range->second = std::max(range->second, v.raw_value);
        }
        return true;
    }

    auto tuple_value_range(const Wildcard &, std::optional<std::pair<long long, long long>> &) -> bool
    {
        return false;
    }

    auto tuple_value_range(const IntegerOrWildcard & v, std::optional<std::pair<long long, long long>> & range) -> bool
    {
        return visit([&](auto & v) { return tuple_value_range(v, range); }, v);
    }

    // Membership against a rasterised domain, given the position is usable. The
    // caller has already established that the entry is an Integer.
    //
    // always_inline rather than inline: this is pass 1's inner test, and once
    // propagate_extensional grew the compact-table dispatch GCC stopped
    // inlining it -- 25% more instructions and 10% of the runtime on srch_k5,
    // on the live-set path, which runs none of the new code.
    [[nodiscard]] [[gnu::always_inline]] inline auto bitmap_contains(
        const ExtensionalDomainBitmaps & bitmaps, const ExtensionalDomainBitmaps::Position & p, const Integer val) -> bool
    {
        auto off = static_cast<unsigned long long>(val.raw_value - p.base);
        if (off >= p.n_values)
            return false;
        return 0 != (bitmaps.words[p.offset + off / extensional_word_bits] & (ExtensionalWord{1} << (off % extensional_word_bits)));
    }

    [[nodiscard]] [[gnu::always_inline]] inline auto bitmap_feasible(const ExtensionalDomainBitmaps & bitmaps,
        const ExtensionalDomainBitmaps::Position & p, const bool use_bitmaps, const State & state, const IntegerVariableID & var, const Integer val)
        -> bool
    {
        return (use_bitmaps && p.usable) ? bitmap_contains(bitmaps, p, val) : state.in_domain(var, val);
    }

    [[nodiscard]] [[gnu::always_inline]] inline auto bitmap_feasible(const ExtensionalDomainBitmaps &, const ExtensionalDomainBitmaps::Position &,
        const bool, const State &, const IntegerVariableID &, const Wildcard &) -> bool
    {
        return true;
    }

    [[nodiscard]] [[gnu::always_inline]] inline auto bitmap_feasible(const ExtensionalDomainBitmaps & bitmaps,
        const ExtensionalDomainBitmaps::Position & p, const bool use_bitmaps, const State & state, const IntegerVariableID & var,
        const IntegerOrWildcard & v) -> bool
    {
        return visit([&](auto & v) { return bitmap_feasible(bitmaps, p, use_bitmaps, state, var, v); }, v);
    }

    // The value a tuple holds at a position, for building the support masks.
    // Only reached once every position has a usable rasterisation, which rules
    // out wildcards, so the Wildcard arm cannot be taken.
    [[nodiscard]] inline auto compact_value(const Integer & v) -> long long
    {
        return v.raw_value;
    }

    [[nodiscard]] inline auto compact_value(const Wildcard &) -> long long
    {
        throw NonExhaustiveSwitch{};
    }

    [[nodiscard]] inline auto compact_value(const IntegerOrWildcard & v) -> long long
    {
        return visit([](const auto & v) { return compact_value(v); }, v);
    }

    /**
     * Lay out and fill the support masks: one bitset of n_words per (position,
     * value), holding the tuples whose entry at that position is that value.
     * Returns false, leaving the compact table unusable, if any position could
     * not be rasterised (a wildcard, or a value range too wide) or if the masks
     * would be larger than the cap -- in either case the live-set algorithm
     * runs instead.
     */
    auto build_compact_table(
        ExtensionalCompactTable & ct, const ExtensionalDomainBitmaps & bitmaps, const ExtensionalData & table, const std::size_t n_tuples) -> bool
    {
        auto n_vars = table.vars.size();
        for (unsigned idx = 0; idx < n_vars; ++idx)
            if (! bitmaps.positions[idx].usable)
                return false;

        ct.n_words = extensional_words_for(n_tuples);
        ct.mask_at.assign(n_vars, 0);
        std::size_t total = 0;
        for (unsigned idx = 0; idx < n_vars; ++idx) {
            ct.mask_at[idx] = total;
            auto here = bitmaps.positions[idx].n_values * ct.n_words;
            if (here > ExtensionalCompactTable::max_mask_words - total)
                return false;
            total += here;
        }
        if (total > ExtensionalCompactTable::max_mask_words)
            return false;

        ct.masks.assign(total, ExtensionalWord{});
        ct.index.resize(ct.n_words);
        ct.scratch.assign(ct.n_words, ExtensionalWord{});
        ct.words.assign(ct.n_words, ExtensionalWord{});
        ct.previous_domain.assign(bitmaps.words.size(), ExtensionalWord{});
        visit(
            [&](const auto & tuples) {
                const auto & rows = *tuples;
                for (std::size_t t = 0; t < n_tuples; ++t) {
                    const auto & row = rows[t];
                    auto word = t / extensional_word_bits;
                    auto bit = ExtensionalWord{1} << (t % extensional_word_bits);
                    for (unsigned idx = 0; idx < n_vars; ++idx) {
                        const auto & p = bitmaps.positions[idx];
                        auto off = static_cast<std::size_t>(compact_value(row[idx]) - p.base);
                        ct.masks[ct.mask_at[idx] + off * ct.n_words + word] |= bit;
                    }
                }
            },
            table.tuples);

        return true;
    }

    /// Set every position's previous domain to everything the table uses there,
    /// so that the next update filters against the current domains from scratch
    /// rather than against a delta it has no record of.
    auto seed_compact_previous_domain(ExtensionalCompactTable & ct, const ExtensionalDomainBitmaps & bitmaps, const std::size_t n_vars) -> void
    {
        std::fill(ct.previous_domain.begin(), ct.previous_domain.end(), ExtensionalWord{});
        for (unsigned idx = 0; idx < n_vars; ++idx) {
            const auto & p = bitmaps.positions[idx];
            for (std::size_t v = 0; v < p.n_values; ++v)
                ct.previous_domain[p.offset + v / extensional_word_bits] |= ExtensionalWord{1} << (v % extensional_word_bits);
        }
    }

    /// Rebuild the index over whichever words \c words now has bits in.
    auto reindex_compact_table(ExtensionalCompactTable & ct) -> void
    {
        ct.limit = 0;
        for (std::size_t w = 0; w < ct.n_words; ++w)
            if (0 != ct.words[w])
                ct.index[ct.limit++] = static_cast<std::uint32_t>(w);
        for (std::size_t w = 0, at = ct.limit; w < ct.n_words; ++w)
            if (0 == ct.words[w])
                ct.index[at++] = static_cast<std::uint32_t>(w);
    }

    /**
     * Take the live set over from the sparse set, at whatever node the decision
     * to switch was made.
     *
     * The sparse set holds what was feasible when the live-set path last ran,
     * and domains have only shrunk since, so it is a superset of the truth --
     * which is why the previous domains are seeded wide rather than from the
     * current ones. Seeding them from the current domains would make the first
     * update see no change at all and leave the stale tuples in: a loss of
     * propagation rather than an unsoundness, and it showed up as 3 366 nodes
     * where the live-set path takes 3 340.
     */
    auto seed_compact_table_from_live_set(ExtensionalCompactTable & ct, const ExtensionalDomainBitmaps & bitmaps, const ExtensionalLiveTuples & live,
        const std::size_t live_count, const std::size_t n_vars) -> void
    {
        std::fill(ct.words.begin(), ct.words.end(), ExtensionalWord{});
        for (std::size_t i = 0; i < live_count; ++i) {
            auto t = live.dense[i];
            ct.words[t / extensional_word_bits] |= ExtensionalWord{1} << (t % extensional_word_bits);
        }
        reindex_compact_table(ct);
        seed_compact_previous_domain(ct, bitmaps, n_vars);
        ct.trail.clear();
        // So that the published mark is never zero at or below this node: zero
        // is what says the search has climbed above it.
        ct.trail.push_back({ExtensionalCompactTable::limit_marker, ct.limit});
    }

    /**
     * Start again from the whole table, for when the search has backtracked
     * above the node the switch happened at. The sparse set stopped being
     * maintained then, so there is nothing to take the live set over from, and
     * the update that follows re-derives it by filtering everything against the
     * current domains -- which is what a first call would have done anyway.
     */
    auto seed_compact_table_from_scratch(
        ExtensionalCompactTable & ct, const ExtensionalDomainBitmaps & bitmaps, const std::size_t n_vars, const std::size_t n_tuples) -> void
    {
        std::fill(ct.words.begin(), ct.words.end(), std::numeric_limits<ExtensionalWord>::max());
        // The tail of the last word holds no tuple, so it must stay clear or an
        // empty live set would never look empty.
        if (auto tail = n_tuples % extensional_word_bits)
            ct.words.back() = (ExtensionalWord{1} << tail) - 1;
        ct.limit = ct.n_words;
        for (std::size_t w = 0; w < ct.n_words; ++w)
            ct.index[w] = static_cast<std::uint32_t>(w);

        seed_compact_previous_domain(ct, bitmaps, n_vars);
        ct.trail.clear();
        ct.trail.push_back({ExtensionalCompactTable::limit_marker, ct.limit});
    }
}

namespace
{
    /**
     * The compact-table pass, kept out of line from the live-set one on purpose.
     * Inlined into the same function it cost the live-set path 7% on Dubois and
     * 14% on Crossword purely in instruction footprint, on instances that never
     * run a line of it.
     */
    template <typename Hint_, typename Inference_>
    [[gnu::noinline]] auto propagate_compact_table(const ExtensionalData & table, ExtensionalCompactTable & ct, const State & state,
        Inference_ & inference, ProofLogger * const logger, const Hint_ & hint, ExtensionalDomainBitmaps & bitmaps,
        const ExtensionalLiveTuples & live, const std::size_t live_count, const bool just_built) -> void
    {
        auto & trail_mark = any_cast<size_t &>(state.get_constraint_state(ct.trail_mark_handle));
        const auto n_vars = static_cast<unsigned>(table.vars.size());

        // Undo everything written at an epoch we have since left. Lazily here
        // rather than from a backtrack callback, because a propagator's
        // `const State &` cannot register one -- and lazily is exact, because
        // nothing reads the words or the previous domains in between and what
        // goes back is the saved value rather than a reconstruction. Before the
        // seeding below, not after: the seed leaves a sentinel entry so that the
        // mark it publishes cannot be zero, and unwinding would take it away
        // again.
        while (ct.trail.size() > trail_mark) {
            const auto & entry = ct.trail.back();
            if (ExtensionalCompactTable::limit_marker == entry.where)
                ct.limit = static_cast<std::size_t>(entry.was);
            else if (entry.where < ct.n_words)
                ct.words[entry.where] = entry.was;
            else
                ct.previous_domain[entry.where - ct.n_words] = entry.was;
            ct.trail.pop_back();
        }

        // Climbing back above the node the switch happened at empties the trail,
        // because nothing below it was recorded at a shallower epoch. The sparse
        // set stopped being maintained there, so there is nothing to take the
        // live set over from: start again from the whole table and let the
        // update below filter it against the current domains, which is what a
        // first call would have done anyway.
        if (just_built)
            seed_compact_table_from_live_set(ct, bitmaps, live, live_count, n_vars);
        else if (0 == trail_mark)
            seed_compact_table_from_scratch(ct, bitmaps, n_vars, live.dense.size());

        auto save_word = [&](std::size_t where, ExtensionalWord was) { ct.trail.push_back({static_cast<std::uint32_t>(where), was}); };

        // The limit goes on the trail too, but once per call: unwinding pops
        // from the back, so the oldest saved value is the one that survives, and
        // that is the limit as this call found it.
        bool limit_saved = false;

        // Update: react to what changed, rather than re-testing what is live.
        // For each position whose domain has lost values, take the union of the
        // support masks of either the values that went or the values that
        // remain -- whichever is the smaller set to walk -- and apply it to the
        // live words in one pass, so each word is written and trailed at most
        // once per position.
        for (unsigned idx = 0; idx < n_vars; ++idx) {
            const auto & p = bitmaps.positions[idx];
            const auto domain_words = extensional_words_for(p.n_values);
            const auto * const cur = bitmaps.words.data() + p.offset;
            auto * const prev = ct.previous_domain.data() + p.offset;

            std::size_t n_removed = 0, n_kept = 0;
            for (std::size_t k = 0; k < domain_words; ++k) {
                n_removed += static_cast<std::size_t>(std::popcount(prev[k] & ~cur[k]));
                n_kept += static_cast<std::size_t>(std::popcount(cur[k]));
            }
            if (0 == n_removed)
                continue;

            const bool by_removals = n_removed <= n_kept;
            const auto * const masks_here = ct.masks.data() + ct.mask_at[idx];
            bool any = false;
            for (std::size_t k = 0; k < domain_words; ++k) {
                auto bits = by_removals ? (prev[k] & ~cur[k]) : cur[k];
                while (bits) {
                    auto v = k * extensional_word_bits + static_cast<std::size_t>(std::countr_zero(bits));
                    bits &= bits - 1;
                    const auto * const m = masks_here + v * ct.n_words;
                    if (! any) {
                        for (std::size_t i = 0; i < ct.limit; ++i)
                            ct.scratch[ct.index[i]] = m[ct.index[i]];
                        any = true;
                    }
                    else
                        for (std::size_t i = 0; i < ct.limit; ++i)
                            ct.scratch[ct.index[i]] |= m[ct.index[i]];
                }
            }
            if (! any)
                for (std::size_t i = 0; i < ct.limit; ++i)
                    ct.scratch[ct.index[i]] = ExtensionalWord{};

            // Downwards, so that swapping an emptied word out to the end never
            // moves an unvisited one into a slot already passed.
            for (auto i = ct.limit; i-- > 0;) {
                auto w = ct.index[i];
                auto was = ct.words[w];
                auto now = by_removals ? (was & ~ct.scratch[w]) : (was & ct.scratch[w]);
                if (now != was) {
                    save_word(w, was);
                    ct.words[w] = now;
                    if (0 == now) {
                        if (! limit_saved) {
                            ct.trail.push_back({ExtensionalCompactTable::limit_marker, ct.limit});
                            limit_saved = true;
                        }
                        ct.index[i] = ct.index[ct.limit - 1];
                        ct.index[ct.limit - 1] = w;
                        --ct.limit;
                    }
                }
            }

            for (std::size_t k = 0; k < domain_words; ++k)
                if (prev[k] != cur[k]) {
                    save_word(ct.n_words + p.offset + k, prev[k]);
                    prev[k] = cur[k];
                }
        }

        if (0 == ct.limit) {
            // The same two spellings as the live-set path below, and for the
            // same reason: the dom/wdeg conflict observer reads the reason of a
            // no-justification contradiction.
            if (logger && logger->get_assertion_level() != AssertionLevel::Off)
                inference.contradiction(logger, JustifyUsingRUP{hint}, table.reason);
            else
                inference.contradiction(logger, NoJustificationNeeded{}, NoReason{});
        }

        // Filter: a value survives iff some live tuple supports it. Same
        // positions in the same order, same values in ascending order, so the
        // inferences and hence the proof are exactly those the live-set path
        // would have made.
        for (unsigned idx = 0; idx < n_vars; ++idx) {
            const auto & p = bitmaps.positions[idx];
            const auto * const masks_here = ct.masks.data() + ct.mask_at[idx];
            state.for_each_value_mutable(table.vars[idx], [&](Integer val) {
                auto off = static_cast<unsigned long long>(val.raw_value - p.base);
                bool supported = false;
                if (off < p.n_values) {
                    const auto * const m = masks_here + off * ct.n_words;
                    for (std::size_t i = 0; i < ct.limit; ++i) {
                        auto w = ct.index[i];
                        if (0 != (ct.words[w] & m[w])) {
                            supported = true;
                            break;
                        }
                    }
                }

                if (! supported) {
                    // Take it out of the rasterised domain as well, so that the
                    // record below is what the domain looks like *after* this
                    // call rather than before it. Otherwise the next call reacts
                    // to this call's own prunings -- which are already out of
                    // the live set, so the work is pure waste.
                    if (off < p.n_values)
                        bitmaps.words[p.offset + off / extensional_word_bits] &= ~(ExtensionalWord{1} << (off % extensional_word_bits));
                    inference.infer(logger, table.vars[idx] != val, JustifyUsingRUP{hint}, table.reason);
                }
            });
        }

        // Record the domains as this call leaves them, so the next call reacts only
        // to what other propagators, or the next decision, take away. Rasterising
        // them a second time here would be simpler, and cost enum_func 9%: the
        // filter above already knows every value it removed.
        for (unsigned idx = 0; idx < n_vars; ++idx) {
            const auto & p = bitmaps.positions[idx];
            const auto domain_words = extensional_words_for(p.n_values);
            const auto * const cur = bitmaps.words.data() + p.offset;
            auto * const prev = ct.previous_domain.data() + p.offset;
            for (std::size_t k = 0; k < domain_words; ++k)
                if (prev[k] != cur[k]) {
                    save_word(ct.n_words + p.offset + k, prev[k]);
                    prev[k] = cur[k];
                }
        }

        // Publish last, so that a contradiction or a failing inference above
        // leaves this call's entries on the trail to be undone rather than
        // committed as if they belonged to an epoch that survived.
        trail_mark = ct.trail.size();
    }
}

template <typename Hint_>
auto gcs::innards::propagate_extensional(
    const ExtensionalData & table, const State & state, auto & inference, ProofLogger * const logger, const Hint_ & hint) -> PropagatorState
{
    auto & live = *table.live;
    auto & live_count = any_cast<size_t &>(state.get_constraint_state(live.size_handle));

    // Rasterise each position's domain once, so pass 1's inner test is a shift
    // and a mask rather than a call back into State for every (tuple, position)
    // pair. Laid out on the first call, which is at the root, from the values
    // the *table* holds at that position: a value outside that range is not in
    // any tuple, so it can never be asked about.
    auto & bitmaps = *table.bitmaps;
    if (! bitmaps.initialised) {
        bitmaps.positions.assign(table.vars.size(), ExtensionalDomainBitmaps::Position{});
        size_t next_offset = 0;
        visit(
            [&](const auto & tuples) {
                auto n_tuples = live.dense.size();
                for (unsigned idx = 0; idx < table.vars.size(); ++idx) {
                    std::optional<std::pair<long long, long long>> range;
                    bool all_integers = true;
                    for (size_t t = 0; t < n_tuples; ++t)
                        if (! tuple_value_range(get_tuple_value(tuples, static_cast<unsigned>(t), idx), range)) {
                            all_integers = false;
                            break;
                        }

                    if (! all_integers || ! range)
                        continue;

                    auto n_values = static_cast<size_t>(range->second - range->first) + 1;
                    auto n_words = extensional_words_for(n_values);
                    if (n_words > ExtensionalDomainBitmaps::max_words)
                        continue;

                    bitmaps.positions[idx] = ExtensionalDomainBitmaps::Position{range->first, n_values, next_offset, true};
                    next_offset += n_words;
                }
            },
            table.tuples);
        bitmaps.words.resize(next_offset);
        bitmaps.initialised = true;
    }

    // The compact table is laid out on the first call, which is at the root, for
    // the same reason the residues are: everything it indexes is fixed for the
    // life of the propagator, and the domains it starts from are the widest they
    // will ever be. A table it cannot rasterise falls back to the live set.
    // Decide, once, whether this instance runs the compact table. Auto watches
    // for a while first: the masks are cheap to build but not free, and a table
    // that is woken 429 times in a whole search -- which is what Renault does --
    // never gets that back. The three thresholds are read off the measured
    // suite; see ExtensionalCompactTable.
    bool just_built = false;
    if (table.compact && ! table.compact->decided) {
        auto & ct = *table.compact;
        ++ct.wakes;
        ct.total_live += live_count;
        const bool forced = ct.forced;
        if (forced || ct.wakes >= ExtensionalCompactTable::decide_after) {
            ct.decided = true;
            auto n_tuples = live.dense.size();
            auto mean_live = static_cast<std::size_t>(ct.total_live / ct.wakes);
            bool worth_it = forced || (mean_live >= ExtensionalCompactTable::min_mean_live && extensional_word_bits * mean_live >= n_tuples);
            if (worth_it && build_compact_table(ct, bitmaps, table, n_tuples)) {
                ct.built = true;
                just_built = true;
            }
        }
    }
    const bool compact = table.compact && table.compact->built;

    // Rasterising position idx costs a word-clear plus one bit-set per value in
    // its domain, and saves roughly one in_domain() call per live tuple. On a
    // four-tuple table with two live entries that trade loses -- it read 0.9x on
    // enum_bin_d2_n14 and enum_shared_k2_n12 before this gate -- so only do it
    // when the live set is big enough to amortise it. The compact table has no
    // choice: the rasterised domain is what it takes the difference against.
    //
    // Spelled as two conditions rather than one because the second is what pass
    // 1 tests per (tuple, position), and GCC only unswitches that loop on it
    // while it stays this simple.
    const bool use_bitmaps = live_count >= ExtensionalDomainBitmaps::min_live;
    for (unsigned idx = 0; (compact || use_bitmaps) && idx < table.vars.size(); ++idx) {
        const auto & p = bitmaps.positions[idx];
        if (! p.usable)
            continue;
        auto n_words = extensional_words_for(p.n_values);
        std::fill_n(bitmaps.words.begin() + static_cast<std::ptrdiff_t>(p.offset), n_words, ExtensionalWord{});
        state.for_each_value_immutable(table.vars[idx], [&](Integer val) {
            auto off = static_cast<unsigned long long>(val.raw_value - p.base);
            if (off < p.n_values)
                bitmaps.words[p.offset + off / extensional_word_bits] |= ExtensionalWord{1} << (off % extensional_word_bits);
        });
    }

    if (compact) {
        propagate_compact_table(table, *table.compact, state, inference, logger, hint, bitmaps, live, live_count, just_built);
        return PropagatorState::EnableButIdempotent;
    }

    // Pass 1: drop tuples that are no longer feasible, by swapping them past the
    // live count. Nothing here goes through State, so a dropped tuple costs two
    // stores rather than an inference plus an IntervalSet edit.
    //
    // Everything loop-invariant is spelled as a local first. Reaching one tuple
    // entry is four dependent loads -- the ArrayParam's shared_ptr, the outer
    // vector's buffer, the row's buffer, the value -- and GCC hoists none of
    // them out of the inner loop on its own, so `perf annotate` showed the first
    // two being redone for every (tuple, position) pair. Naming them costs
    // nothing and leaves two loads: the row, once per tuple, and the value.
    visit(
        [&](const auto & tuples) {
            const auto & rows = *tuples;
            const auto n_vars = static_cast<unsigned>(table.vars.size());
            const auto * const positions = bitmaps.positions.data();
            const auto * const vars = table.vars.data();
            for (size_t i = 0; i < live_count;) {
                auto tuple_idx = live.dense[i];
                const auto & row = rows[tuple_idx];
                bool is_feasible = true;
                for (unsigned idx = 0; idx < n_vars; ++idx)
                    if (! bitmap_feasible(bitmaps, positions[idx], use_bitmaps, state, vars[idx], row[idx])) {
                        is_feasible = false;
                        break;
                    }

                if (is_feasible)
                    ++i;
                else {
                    auto last = live_count - 1;
                    auto moved = live.dense[last];
                    live.dense[i] = moved;
                    live.position[moved] = static_cast<uint32_t>(i);
                    live.dense[last] = tuple_idx;
                    live.position[tuple_idx] = static_cast<uint32_t>(last);
                    live_count = last;
                }
            }
        },
        table.tuples);

    if (0 == live_count) {
        // The two spellings the selector used to give us for free, kept exactly:
        // at higher assertion levels the contradiction must be explicit because
        // there is no table to derive it from, and otherwise it must carry no
        // justification and no reason, because that is what emptying the
        // selector's domain used to report -- and the conflict observer behind
        // dom/wdeg reads that reason.
        if (logger && logger->get_assertion_level() != AssertionLevel::Off)
            inference.contradiction(logger, JustifyUsingRUP{hint}, table.reason);
        else
            inference.contradiction(logger, NoJustificationNeeded{}, NoReason{});
    }

    // check for supports in selectable tuples, using residual supports: for each
    // (variable position, value) we remember the last selectable tuple that
    // supported it, and only re-scan the table when that residue has gone stale.
    // The value is supported iff some still-selectable tuple matches it, so the
    // set of removed values -- and hence the inferences and the proof -- is exactly
    // the same as a full scan; only the search for a witness is incremental.
    auto & residues = *table.residues;
    if (! residues.initialised) {
        residues.support.resize(table.vars.size());
        residues.base.resize(table.vars.size());
        for (unsigned idx = 0; idx < table.vars.size(); ++idx) {
            auto [lo, hi] = state.bounds(table.vars[idx]);
            residues.base[idx] = lo.raw_value;
            residues.support[idx].assign(static_cast<std::size_t>((hi - lo).raw_value + 1), ExtensionalResidues::none);
        }
        residues.initialised = true;
    }

    visit(
        [&](const auto & tuples) {
            // Same hoisting as pass 1: the support scan reaches one tuple entry
            // per step, and the loads that get there are loop-invariant.
            const auto & rows = *tuples;
            for (unsigned idx = 0; idx < table.vars.size(); ++idx) {
                auto * const residue_row = residues.support[idx].data();
                const auto residue_row_size = residues.support[idx].size();
                const auto base = residues.base[idx];
                const auto * const dense = live.dense.data();
                const auto * const position = live.position.data();
                state.for_each_value_mutable(table.vars[idx], [&](Integer val) {
                    auto off = static_cast<std::size_t>(val.raw_value - base);
                    bool have_row = off < residue_row_size;

                    // O(1) fast path: last witness still selectable and still matching.
                    if (have_row) {
                        auto cached = residue_row[off];
                        if (cached != ExtensionalResidues::none && position[cached] < live_count && match(rows[cached][idx], val))
                            return;
                    }

                    bool supported = false;
                    for (size_t i = 0; i < live_count; ++i) {
                        auto tuple_idx = dense[i];
                        if (match(rows[tuple_idx][idx], val)) {
                            supported = true;
                            if (have_row)
                                residue_row[off] = tuple_idx;
                            break;
                        }
                    }

                    if (! supported) {
                        inference.infer(logger, table.vars[idx] != val, JustifyUsingRUP{hint}, table.reason);
                    }
                });
            }
        },
        table.tuples);

    // Idempotent when the vars are distinct: this call prunes to the closure.
    // A value survives the support pass only if some still-selectable tuple
    // matches it, and a selectable tuple's own entries are therefore all still
    // in domain (wildcards match everything), so a re-run finds every
    // selectable tuple still feasible and every remaining value still
    // supported. A repeated variable breaks exactly this self-witnessing (a
    // tuple can be feasible per-position yet killed by a removal at the other
    // occurrence, noticed only on the next run) -- that is the motivating case
    // for the install-time downgrade, which every caller's 1:1 triggers make
    // detectable. The claim rides the shared helper because, unlike the
    // non-GAC alldifferent helper, every caller's run is exactly this call.
    return PropagatorState::EnableButIdempotent;
}

// One instantiation per (inference tracker, hint) pair actually used: NoHint for
// the unnamed AutoTable presolver, hints::Table for Table, hints::LinearEquality
// for the GAC linear encoding. A new caller with its own hint adds a line here.
#define GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(hint)                                                                                                  \
    template auto gcs::innards::propagate_extensional(                                                                                               \
        const ExtensionalData &, const State &, SimpleInferenceTracker &, ProofLogger * const, const hint &) -> PropagatorState;                     \
    template auto gcs::innards::propagate_extensional(                                                                                               \
        const ExtensionalData &, const State &, EagerProofLoggingInferenceTracker &, ProofLogger * const, const hint &) -> PropagatorState;

GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(NoHint)
GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(hints::Table)
GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(hints::LinearEquality)
GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(hints::Multiply)
GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(hints::Divide)
GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(hints::Modulus)
GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(hints::Power)
GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(hints::Plus)
GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(hints::Minus)

#undef GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL
