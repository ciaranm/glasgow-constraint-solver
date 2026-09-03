#include <algorithm>
#include <any>
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
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/innards/state.hh>
#include <gcs/proof.hh>
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

gcs::innards::ExtensionalData::ExtensionalData(vector<IntegerVariableID> vars, ExtensionalTuples tuples, shared_ptr<ExtensionalLiveTuples> live) :
    vars(move(vars)), tuples(move(tuples)), reason(generic_reason(this->vars)), live(move(live))
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
    [[nodiscard]] inline auto bitmap_contains(
        const ExtensionalDomainBitmaps & bitmaps, const ExtensionalDomainBitmaps::Position & p, const Integer val) -> bool
    {
        auto off = static_cast<unsigned long long>(val.raw_value - p.base);
        if (off >= p.n_values)
            return false;
        return 0 != (bitmaps.words[p.offset + off / extensional_word_bits] & (ExtensionalWord{1} << (off % extensional_word_bits)));
    }

    [[nodiscard]] inline auto bitmap_feasible(const ExtensionalDomainBitmaps & bitmaps, const ExtensionalDomainBitmaps::Position & p,
        const bool use_bitmaps, const State & state, const IntegerVariableID & var, const Integer val) -> bool
    {
        return (use_bitmaps && p.usable) ? bitmap_contains(bitmaps, p, val) : state.in_domain(var, val);
    }

    [[nodiscard]] inline auto bitmap_feasible(const ExtensionalDomainBitmaps &, const ExtensionalDomainBitmaps::Position &, const bool, const State &,
        const IntegerVariableID &, const Wildcard &) -> bool
    {
        return true;
    }

    [[nodiscard]] inline auto bitmap_feasible(const ExtensionalDomainBitmaps & bitmaps, const ExtensionalDomainBitmaps::Position & p,
        const bool use_bitmaps, const State & state, const IntegerVariableID & var, const IntegerOrWildcard & v) -> bool
    {
        return visit([&](auto & v) { return bitmap_feasible(bitmaps, p, use_bitmaps, state, var, v); }, v);
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

    // Rasterising position idx costs a word-clear plus one bit-set per value in
    // its domain, and saves roughly one in_domain() call per live tuple. On a
    // four-tuple table with two live entries that trade loses -- it read 0.9x on
    // enum_bin_d2_n14 and enum_shared_k2_n12 before this gate -- so only do it
    // when the live set is big enough to amortise it.
    const bool use_bitmaps = live_count >= ExtensionalDomainBitmaps::min_live;
    for (unsigned idx = 0; use_bitmaps && idx < table.vars.size(); ++idx) {
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
