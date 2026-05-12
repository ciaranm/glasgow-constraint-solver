#include <gcs/constraints/disjunctive.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <sstream>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::size_t;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

Disjunctive::Disjunctive(vector<IntegerVariableID> starts, vector<Integer> lengths, bool strict) :
    _starts(move(starts)),
    _lengths(move(lengths)),
    _strict(strict)
{
    if (_starts.size() != _lengths.size())
        throw UnexpectedException{"Disjunctive: starts and lengths must have the same size"};
    for (auto & l : _lengths)
        if (l < 0_i)
            throw UnexpectedException{"Disjunctive: lengths must be non-negative"};
}

auto Disjunctive::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Disjunctive>(_starts, _lengths, _strict);
}

auto Disjunctive::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Disjunctive::prepare(Propagators &, State &, ProofModel * const) -> bool
{
    // In non-strict mode, zero-length tasks are dropped: they cannot constrain
    // any other task. In strict mode, every task participates (a zero-length
    // task at time t is forbidden from sitting strictly inside any other
    // task's active interval). Because lengths are constant, the distinction
    // is fully resolved here.
    auto n = _starts.size();
    _active_tasks.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        if (! _strict && _lengths[i] == 0_i)
            continue;
        _active_tasks.push_back(i);
    }

    // With fewer than two participating tasks there is no pair, hence nothing
    // to encode and nothing to check.
    return _active_tasks.size() >= 2;
}

auto Disjunctive::define_proof_model(ProofModel & model) -> void
{
    // Declarative pairwise OPB encoding:
    //   for each unordered pair (i, j) of participating tasks:
    //     before_{i,j} ⇔  starts[i] + lengths[i] ≤ starts[j]
    //     before_{j,i} ⇔  starts[j] + lengths[j] ≤ starts[i]
    //   then one clause per pair:
    //     before_{i,j} ∨ before_{j,i}
    //
    // This reflects the constraint's declarative meaning rather than the
    // time-table reasoning a stronger propagator would do. The bridge to
    // active/before/after-at-time flags is introduced lazily inside the
    // propagator's justifications (see follow-up stages on issue 146).
    auto emit_before = [&](size_t i, size_t j) -> ProofFlag {
        return model.create_proof_flag_fully_reifying(
            "disjbefore", "Disjunctive", "first task finishes before second starts",
            WPBSum{} + 1_i * _starts[i] + -1_i * _starts[j] <= -_lengths[i]);
    };
    for (size_t a = 0; a < _active_tasks.size(); ++a) {
        auto i = _active_tasks[a];
        for (size_t b = a + 1; b < _active_tasks.size(); ++b) {
            auto j = _active_tasks[b];
            auto before_ij = emit_before(i, j);
            auto before_ji = emit_before(j, i);
            model.add_constraint("Disjunctive", "one task must finish first",
                WPBSum{} + 1_i * before_ij + 1_i * before_ji >= 1_i);
        }
    }
}

auto Disjunctive::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (auto i : _active_tasks)
        triggers.on_bounds.emplace_back(_starts[i]);

    propagators.install(
        [starts = move(_starts), lengths = move(_lengths),
            active_tasks = move(_active_tasks)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Time-table consistency, specialised to heights = 1 and
            // capacity = 1. Mandatory part of task i is [lst_i, eet_i)
            // where lst_i = ub(s_i) and eet_i = lb(s_i) + l_i: the slice it
            // must occupy regardless of where it starts. Two tasks whose
            // mandatory parts overlap is infeasible, and any per-task start
            // that would force a mandatory-part collision is excluded.
            //
            // Zero-length tasks contribute nothing to the profile but in
            // strict mode are still constrained: a zero-length task's
            // point may not sit strictly inside any other task's open
            // active interval. The TT pass misses that case; we catch it
            // below with an all-fixed pairwise check.
            //
            // Justifications are stubbed with AssertRatherThanJustifying:
            // real proof logging arrives once the bridge to time-indexed
            // before/after/active flags is in place.
            bool any = false;
            Integer t_lo = 0_i, t_hi = -1_i;
            for (auto i : active_tasks) {
                if (lengths[i] == 0_i)
                    continue;
                auto [s_lo, s_hi] = state.bounds(starts[i]);
                auto lo = s_lo, hi = s_hi + lengths[i] - 1_i;
                if (! any || lo < t_lo) t_lo = lo;
                if (! any || hi > t_hi) t_hi = hi;
                any = true;
            }

            if (any) {
                auto range = (t_hi - t_lo + 1_i).raw_value;
                vector<int> mand_load(range, 0);

                for (auto i : active_tasks) {
                    if (lengths[i] == 0_i)
                        continue;
                    auto lst = state.upper_bound(starts[i]);
                    auto eet = state.lower_bound(starts[i]) + lengths[i];
                    if (lst < eet)
                        for (Integer t = lst; t < eet; ++t)
                            ++mand_load[(t - t_lo).raw_value];
                }

                for (auto idx = 0; idx < range; ++idx)
                    if (mand_load[idx] > 1) {
                        inference.contradiction(logger, AssertRatherThanJustifying{},
                            generic_reason(state, starts));
                        return PropagatorState::DisableUntilBacktrack;
                    }

                for (auto j : active_tasks) {
                    if (lengths[j] == 0_i)
                        continue;
                    auto [cur_lb, cur_ub] = state.bounds(starts[j]);
                    if (cur_lb == cur_ub)
                        continue;

                    auto lst_j = cur_ub, eet_j = cur_lb + lengths[j];
                    auto fits_at = [&](Integer s) -> bool {
                        for (Integer t = s; t < s + lengths[j]; ++t) {
                            auto load = mand_load[(t - t_lo).raw_value];
                            if (lst_j < eet_j && t >= lst_j && t < eet_j)
                                --load;
                            if (load >= 1)
                                return false;
                        }
                        return true;
                    };

                    auto new_lb = cur_lb;
                    while (new_lb <= cur_ub && ! fits_at(new_lb))
                        ++new_lb;
                    if (new_lb > cur_lb)
                        inference.infer_greater_than_or_equal(logger, starts[j], new_lb,
                            AssertRatherThanJustifying{},
                            generic_reason(state, starts));

                    auto new_ub = cur_ub;
                    while (new_ub >= cur_lb && ! fits_at(new_ub))
                        --new_ub;
                    if (new_ub < cur_ub)
                        inference.infer_less_than(logger, starts[j], new_ub + 1_i,
                            AssertRatherThanJustifying{},
                            generic_reason(state, starts));
                }
            }

            // Strict-mode zero-length tasks: check that no fixed zero-length
            // task sits strictly inside a fixed positive-length task's open
            // active interval. (Non-strict mode never sees zero-length tasks
            // in active_tasks — they were dropped at prepare() time.)
            for (auto z : active_tasks) {
                if (lengths[z] > 0_i)
                    continue;
                if (! state.has_single_value(starts[z]))
                    continue;
                auto vz = state.lower_bound(starts[z]);
                for (auto k : active_tasks) {
                    if (k == z || lengths[k] == 0_i)
                        continue;
                    if (! state.has_single_value(starts[k]))
                        continue;
                    auto vk = state.lower_bound(starts[k]);
                    if (vk < vz && vz < vk + lengths[k]) {
                        inference.contradiction(logger, AssertRatherThanJustifying{},
                            generic_reason(state, starts));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Disjunctive::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;
    print(s, "{} disjunctive{} (", _name, _strict ? "_strict" : "");
    for (const auto & v : _starts)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, " ) ( ");
    for (const auto & l : _lengths)
        print(s, " {}", l);
    print(s, " )");
    return s.str();
}
