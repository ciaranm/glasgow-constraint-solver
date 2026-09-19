#include <gcs/constraints/all_different/bc_all_different.hh>
#include <gcs/constraints/all_different/hints.hh>
#include <gcs/constraints/all_different/justify.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>

#include <algorithm>
#include <cstddef>
#include <map>
#include <memory>
#include <optional>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::map;
using std::nullopt;
using std::optional;
using std::shared_ptr;
using std::size_t;
using std::vector;
using std::ranges::sort;

namespace
{
    // One variable's bounds for a sweep, and where they sit among the sorted
    // distinct bounds: minrank indexes its lower bound, maxrank its upper bound
    // plus one.
    struct Interval
    {
        Integer lb = 0_i, ub = 0_i;
        size_t minrank = 0, maxrank = 0;
    };

    // A bound one of the sweeps moved, in the order the sweeps moved them.
    struct Update
    {
        size_t var = 0;
        bool lower = true;
        Integer bound = 0_i;
    };
}

struct gcs::innards::BcAllDifferentScratch
{
    vector<Interval> intervals;
    vector<size_t> minsorted, maxsorted;
    vector<Integer> bounds, d;
    vector<size_t> t, h;
    vector<Update> updates;
};

auto gcs::innards::make_bc_all_different_scratch() -> shared_ptr<BcAllDifferentScratch>
{
    return make_shared<BcAllDifferentScratch>();
}

namespace
{
    // The union-find over bound positions that both sweeps use. A tree t
    // points each position at a later (pathmax) or earlier (pathmin) one, and
    // pathset compresses the path it walked.
    auto pathmax(const vector<size_t> & t, size_t i) -> size_t
    {
        while (t[i] > i)
            i = t[i];
        return i;
    }

    auto pathmin(const vector<size_t> & t, size_t i) -> size_t
    {
        while (t[i] < i)
            i = t[i];
        return i;
    }

    auto pathset(vector<size_t> & t, size_t start, size_t end, size_t to) -> void
    {
        auto prev = start;
        while (prev != end) {
            auto next = t[prev];
            t[prev] = to;
            prev = next;
        }
    }

    // Read every variable's bounds and rank them among the sorted distinct
    // values of the lower bounds and the upper bounds plus one, with a
    // sentinel either side.
    auto sort_bounds(const vector<IntegerVariableID> & vars, const State & state, BcAllDifferentScratch & s) -> size_t
    {
        auto n = vars.size();
        if (s.minsorted.size() != n) {
            s.intervals.resize(n);
            s.minsorted.resize(n);
            s.maxsorted.resize(n);
            for (size_t i = 0; i < n; ++i)
                s.minsorted[i] = s.maxsorted[i] = i;
        }
        for (size_t i = 0; i < n; ++i) {
            auto [lb, ub] = state.bounds(vars[i]);
            s.intervals[i].lb = lb;
            s.intervals[i].ub = ub;
        }
        // Any permutation is a valid starting point, and the previous call's
        // order is usually nearly sorted still, so insertion sort from it.
        auto insertion_sort = [&](vector<size_t> & order, auto key) {
            for (size_t i = 1; i < n; ++i) {
                auto v = order[i];
                auto k = key(v);
                auto j = i;
                for (; j > 0 && k < key(order[j - 1]); --j)
                    order[j] = order[j - 1];
                order[j] = v;
            }
        };
        insertion_sort(s.minsorted, [&](size_t v) { return s.intervals[v].lb; });
        insertion_sort(s.maxsorted, [&](size_t v) { return s.intervals[v].ub; });

        s.bounds.resize(2 * n + 2, 0_i);
        auto min = s.intervals[s.minsorted[0]].lb;
        auto max = s.intervals[s.maxsorted[0]].ub + 1_i;
        auto last = min - 2_i;
        size_t nb = 0;
        s.bounds[0] = last;
        size_t i = 0, j = 0;
        while (true) {
            if (i < n && min <= max) {
                if (min != last)
                    s.bounds[++nb] = last = min;
                s.intervals[s.minsorted[i]].minrank = nb;
                if (++i < n)
                    min = s.intervals[s.minsorted[i]].lb;
            }
            else {
                if (max != last)
                    s.bounds[++nb] = last = max;
                s.intervals[s.maxsorted[j]].maxrank = nb;
                if (++j == n)
                    break;
                max = s.intervals[s.maxsorted[j]].ub + 1_i;
            }
        }
        s.bounds[nb + 1] = s.bounds[nb] + 2_i;
        return nb;
    }

    // The lower bound sweep: variables in increasing order of upper bound,
    // each placed into the leftmost free capacity at or above its lower bound.
    // A run of positions whose capacity is exactly used up is a Hall interval,
    // and a variable whose lower bound lies in one moves past it. Returns false
    // if some interval holds more variables than values.
    auto filter_lower(BcAllDifferentScratch & s, size_t nb) -> bool
    {
        s.t.resize(nb + 2);
        s.h.resize(nb + 2);
        s.d.resize(nb + 2, 0_i);
        for (size_t i = 1; i <= nb + 1; ++i) {
            s.t[i] = s.h[i] = i - 1;
            s.d[i] = s.bounds[i] - s.bounds[i - 1];
        }
        for (auto v : s.maxsorted) {
            auto x = s.intervals[v].minrank, y = s.intervals[v].maxrank;
            auto z = pathmax(s.t, x + 1);
            auto j = s.t[z];
            if (--s.d[z] == 0_i) {
                s.t[z] = z + 1;
                z = pathmax(s.t, s.t[z]);
                s.t[z] = j;
            }
            pathset(s.t, x + 1, z, z);
            if (s.d[z] < s.bounds[z] - s.bounds[y])
                return false;
            if (s.h[x] > x) {
                auto w = pathmax(s.h, s.h[x]);
                s.updates.push_back(Update{v, true, s.bounds[w]});
                pathset(s.h, x, w, w);
            }
            if (s.d[z] == s.bounds[z] - s.bounds[y]) {
                pathset(s.h, s.h[y], j - 1, y);
                s.h[y] = j - 1;
            }
        }
        return true;
    }

    // The mirror image, for upper bounds: variables in decreasing order of
    // lower bound, placed into the rightmost free capacity.
    auto filter_upper(BcAllDifferentScratch & s, size_t nb) -> bool
    {
        for (size_t i = 0; i <= nb; ++i) {
            s.t[i] = s.h[i] = i + 1;
            s.d[i] = s.bounds[i + 1] - s.bounds[i];
        }
        for (auto it = s.minsorted.rbegin(); it != s.minsorted.rend(); ++it) {
            auto v = *it;
            auto x = s.intervals[v].maxrank, y = s.intervals[v].minrank;
            auto z = pathmin(s.t, x - 1);
            auto j = s.t[z];
            if (--s.d[z] == 0_i) {
                s.t[z] = z - 1;
                z = pathmin(s.t, s.t[z]);
                s.t[z] = j;
            }
            pathset(s.t, x - 1, z, z);
            if (s.d[z] < s.bounds[y] - s.bounds[z])
                return false;
            if (s.h[x] < x) {
                auto w = pathmin(s.h, s.h[x]);
                s.updates.push_back(Update{v, false, s.bounds[w] - 1_i});
                pathset(s.h, x, w, w);
            }
            if (s.d[z] == s.bounds[y] - s.bounds[z]) {
                pathset(s.h, s.h[y], j + 1, y);
                s.h[y] = j + 1;
            }
        }
        return true;
    }

    // The variables, other than `excluding`, whose bounds lie inside [lo, hi],
    // skipping constants: a constant's value is accounted for by the
    // at-most-ones, which name every variable, and it has no at-least-one of
    // its own to contribute.
    auto confined_to(const vector<IntegerVariableID> & vars, const State & state, Integer lo, Integer hi, optional<size_t> excluding,
        vector<IntegerVariableID> & out, Integer & count) -> void
    {
        out.clear();
        count = 0_i;
        for (size_t i = 0; i < vars.size(); ++i) {
            if (excluding == optional<size_t>{i})
                continue;
            auto [lb, ub] = state.bounds(vars[i]);
            if (lo <= lb && ub <= hi) {
                ++count;
                if (! is_constant_variable(vars[i]))
                    out.push_back(vars[i]);
            }
        }
    }

    // A Hall interval, or a violator, found against the current state: at
    // least as many variables confined to [lo, hi] as there are values in it.
    struct HallInterval
    {
        Integer lo = 0_i, hi = 0_i;
        vector<IntegerVariableID> hall_vars;
    };

    // The interval behind moving `var`'s lower bound up to `new_lb`: some
    // [lo, new_lb - 1] with lo at or below var's lower bound. The sweep found
    // one against the bounds it read, and bounds only tighten, so it is still
    // there; the narrowest such is the cheapest to write down.
    auto find_lower_hall(const vector<IntegerVariableID> & vars, const State & state, size_t var, Integer new_lb) -> HallInterval
    {
        auto hi = new_lb - 1_i;
        auto var_lb = state.lower_bound(vars[var]);
        vector<Integer> candidates;
        for (size_t i = 0; i < vars.size(); ++i)
            if (auto lb = state.lower_bound(vars[i]); i != var && lb <= var_lb)
                candidates.push_back(lb);
        sort(candidates, [](Integer a, Integer b) { return a > b; });
        HallInterval result{0_i, hi, {}};
        Integer count = 0_i;
        for (auto lo : candidates) {
            confined_to(vars, state, lo, hi, var, result.hall_vars, count);
            if (count >= hi - lo + 1_i) {
                result.lo = lo;
                return result;
            }
        }
        throw UnexpectedException{"bc all_different: no Hall interval behind a lower bound it moved"};
    }

    auto find_upper_hall(const vector<IntegerVariableID> & vars, const State & state, size_t var, Integer new_ub) -> HallInterval
    {
        auto lo = new_ub + 1_i;
        auto var_ub = state.upper_bound(vars[var]);
        vector<Integer> candidates;
        for (size_t i = 0; i < vars.size(); ++i)
            if (auto ub = state.upper_bound(vars[i]); i != var && ub >= var_ub)
                candidates.push_back(ub);
        sort(candidates);
        HallInterval result{lo, 0_i, {}};
        Integer count = 0_i;
        for (auto hi : candidates) {
            confined_to(vars, state, lo, hi, var, result.hall_vars, count);
            if (count >= hi - lo + 1_i) {
                result.hi = hi;
                return result;
            }
        }
        throw UnexpectedException{"bc all_different: no Hall interval behind an upper bound it moved"};
    }

    // An interval holding more variables than values, behind a failed sweep.
    auto find_violator(const vector<IntegerVariableID> & vars, const State & state) -> HallInterval
    {
        vector<Integer> los, his;
        for (const auto & var : vars) {
            auto [lb, ub] = state.bounds(var);
            los.push_back(lb);
            his.push_back(ub);
        }
        HallInterval result{0_i, 0_i, {}};
        Integer count = 0_i;
        for (auto lo : los)
            for (auto hi : his)
                if (lo <= hi) {
                    confined_to(vars, state, lo, hi, nullopt, result.hall_vars, count);
                    if (count > hi - lo + 1_i) {
                        result.lo = lo;
                        result.hi = hi;
                        return result;
                    }
                }
        throw UnexpectedException{"bc all_different: no violating interval behind a failed sweep"};
    }

    // Each Hall variable's bounds, which with the constraint's at-most-ones
    // are the whole of why nothing else can use the interval; plus, for a
    // moved bound, the moved variable's other side of the interval, so that
    // RUP can walk it past every value the Hall interval takes.
    auto hall_reason(const State & state, const HallInterval & hall, optional<IntegerVariableCondition> extra) -> ReasonLiterals
    {
        ReasonLiterals result;
        for (const auto & var : hall.hall_vars) {
            auto [lb, ub] = state.bounds(var);
            result.emplace_back(var >= lb);
            result.emplace_back(var < ub + 1_i);
        }
        if (extra)
            result.emplace_back(*extra);
        return result;
    }
}

auto gcs::innards::propagate_bc_all_different(const ConstraintID & constraint_id, const vector<IntegerVariableID> & vars,
    map<Integer, ProofLine> & value_am1_constraint_numbers, BcAllDifferentScratch & scratch, const State & state, auto & inference,
    ProofLogger * const logger) -> PropagatorState
{
    if (vars.size() < 2)
        return PropagatorState::EnableButIdempotent;

    // One lower pass and one upper pass reach the bounds(Z) fixpoint of the
    // bounds they read, so a single sweep is a fixpoint unless a bound it wrote
    // landed in a hole: the state then moves it on past the hole, and the next
    // sweep, which reads the bounds afresh, may find more.
    while (true) {
        scratch.updates.clear();
        auto nb = sort_bounds(vars, state, scratch);
        bool feasible = filter_lower(scratch, nb) && filter_upper(scratch, nb);

        if (! feasible) {
            auto hall = logger ? find_violator(vars, state) : HallInterval{};
            inference.contradiction(logger,
                JustifyExplicitly{[&](const ReasonLiterals &) {
                                      justify_all_different_hall_interval(
                                          *logger, state, vars, hall.hall_vars, hall.lo, hall.hi, value_am1_constraint_numbers);
                                  },
                    ThenRUP::Yes, hints::AllDifferentHallInterval{{constraint_id}, hall.lo, hall.hi}},
                logger ? Reason{ExplicitReason{hall_reason(state, hall, nullopt)}} : Reason{});
            return PropagatorState::Enable;
        }

        bool snapped = false;
        for (const auto & update : scratch.updates) {
            const auto & var = vars[update.var];
            auto [lb, ub] = state.bounds(var);
            if (update.lower ? update.bound <= lb : update.bound >= ub)
                continue;

            auto lit = update.lower ? var >= update.bound : var < update.bound + 1_i;
            // Only a proof, or something recording reasons, wants to know which
            // interval it was, so only they pay to find it.
            if (logger || inference.want_reasons()) {
                auto hall =
                    update.lower ? find_lower_hall(vars, state, update.var, update.bound) : find_upper_hall(vars, state, update.var, update.bound);
                auto reason = hall_reason(state, hall, update.lower ? var >= lb : var < ub + 1_i);
                inference.infer(logger, lit,
                    JustifyExplicitly{[&, hall = std::move(hall)](const ReasonLiterals &) {
                                          justify_all_different_hall_interval(
                                              *logger, state, vars, hall.hall_vars, hall.lo, hall.hi, value_am1_constraint_numbers);
                                      },
                        ThenRUP::Yes, hints::AllDifferentHallInterval{{constraint_id}, hall.lo, hall.hi}},
                    Reason{ExplicitReason{std::move(reason)}});
            }
            else
                inference.infer(logger, lit, NoJustificationNeeded{}, NoReason{});

            if (inference.contradicted())
                return PropagatorState::Enable;

            if (update.lower ? state.lower_bound(var) != update.bound : state.upper_bound(var) != update.bound)
                snapped = true;
        }

        if (! snapped)
            break;
    }

    // Idempotent: the loop only stops after a sweep whose every bound landed
    // exactly where the sweep put it, which is a fixpoint. Duplicate scope variables never reach here (prepare
    // rejects them), and the triggers are 1:1 with the scope, so view aliasing
    // is caught by the install-time downgrade.
    return PropagatorState::EnableButIdempotent;
}

template auto gcs::innards::propagate_bc_all_different(const ConstraintID & constraint_id, const vector<IntegerVariableID> & vars,
    map<Integer, ProofLine> & value_am1_constraint_numbers, BcAllDifferentScratch & scratch, const State & state, SimpleInferenceTracker & inference,
    ProofLogger * const logger) -> PropagatorState;

template auto gcs::innards::propagate_bc_all_different(const ConstraintID & constraint_id, const vector<IntegerVariableID> & vars,
    map<Integer, ProofLine> & value_am1_constraint_numbers, BcAllDifferentScratch & scratch, const State & state,
    EagerProofLoggingInferenceTracker & inference, ProofLogger * const logger) -> PropagatorState;
