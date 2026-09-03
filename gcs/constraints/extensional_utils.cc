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
    auto feasible(const State & state, const IntegerVariableID & var, const Integer val) -> bool
    {
        return state.in_domain(var, val);
    }

    auto feasible(const State &, const IntegerVariableID &, const Wildcard &) -> bool
    {
        return true;
    }

    auto feasible(const State & state, const IntegerVariableID & var, const IntegerOrWildcard & v) -> bool
    {
        return visit([&](auto & v) { return feasible(state, var, v); }, v);
    }

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
}

template <typename Hint_>
auto gcs::innards::propagate_extensional(
    const ExtensionalData & table, const State & state, auto & inference, ProofLogger * const logger, const Hint_ & hint) -> PropagatorState
{
    auto & live = *table.live;
    auto & live_count = any_cast<size_t &>(state.get_constraint_state(live.size_handle));

    // Pass 1: drop tuples that are no longer feasible, by swapping them past the
    // live count. Nothing here goes through State, so a dropped tuple costs two
    // stores rather than an inference plus an IntervalSet edit.
    visit(
        [&](const auto & tuples) {
            for (size_t i = 0; i < live_count;) {
                auto tuple_idx = live.dense[i];
                bool is_feasible = true;
                for (unsigned idx = 0; idx < table.vars.size(); ++idx)
                    if (! feasible(state, table.vars[idx], get_tuple_value(tuples, tuple_idx, idx))) {
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
            for (unsigned idx = 0; idx < table.vars.size(); ++idx) {
                auto & residue_row = residues.support[idx];
                auto base = residues.base[idx];
                state.for_each_value_mutable(table.vars[idx], [&](Integer val) {
                    auto off = static_cast<std::size_t>(val.raw_value - base);
                    bool have_row = off < residue_row.size();

                    // O(1) fast path: last witness still selectable and still matching.
                    if (have_row) {
                        auto cached = residue_row[off];
                        if (cached != ExtensionalResidues::none && live.position[cached] < live_count &&
                            match(get_tuple_value(tuples, cached, idx), val))
                            return;
                    }

                    bool supported = false;
                    for (size_t i = 0; i < live_count; ++i) {
                        auto tuple_idx = live.dense[i];
                        if (match(get_tuple_value(tuples, tuple_idx, idx), val)) {
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
