#include <gcs/constraints/all_different/gac_all_different.hh>
#include <gcs/constraints/sort/arg_sort.hh>
#include <gcs/constraints/sort/sortedness.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <map>
#include <memory>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::cmp_greater;
using std::cmp_less;
using std::make_shared;
using std::make_unique;
using std::map;
using std::move;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

ArgSort::ArgSort(vector<IntegerVariableID> x, vector<IntegerVariableID> p, Integer offset) :
    _x(move(x)),
    _p(move(p)),
    _offset(offset)
{
}

auto ArgSort::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ArgSort>(_x, _p, _offset);
}

auto ArgSort::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    // Set up the internal sorted-value variables in the proof, then run the
    // shared sortedness helpers on {x, y} to reuse the Mehlhorn-Thiel bounds(Z)
    // propagator and its fully-certified proof of y = sort(x). Keeping the
    // witness lets ArgSort channel its permutation p to the stable rank pos.
    vector<IntegerVariableID> y_ids{_y.begin(), _y.end()};
    if (optional_model) {
        for (size_t j = 0; j < _y.size(); ++j)
            optional_model->set_up_integer_variable(_y[j], _lowest_x, _highest_x,
                "argsort_y_" + std::to_string(j), IntegerVariableProofRepresentation::Bits);
        _witness = define_sortedness_proof_model(*optional_model, _x, y_ids);
    }

    install_sortedness_propagator(propagators, _x, y_ids, _witness);

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto ArgSort::prepare(Propagators & propagators, State & initial_state, ProofModel * const optional_model) -> bool
{
    if (_x.size() != _p.size())
        throw InvalidProblemDefinitionException{"ArgSort constraint on different sized arrays"};

    if (_x.empty())
        return false;

    // The permutation values live in [offset, offset + n - 1]; pin those bounds
    // so the index arithmetic (and the OPB index range) is sound.
    for (const auto & v : _p) {
        propagators.define_bound(initial_state, optional_model, v, Bound::Lower, _offset, "ArgSort", "permutation range");
        propagators.define_bound(initial_state, optional_model, v, Bound::Upper, _offset + Integer(_x.size()) - 1_i, "ArgSort", "permutation range");
    }

    // Record the value range of x, used as the domain of the sorted-value
    // variables y.
    bool first = true;
    for (const auto & v : _x) {
        auto [lo, hi] = initial_state.bounds(v);
        if (first) {
            _lowest_x = lo;
            _highest_x = hi;
            first = false;
        }
        else {
            _lowest_x = std::min(_lowest_x, lo);
            _highest_x = std::max(_highest_x, hi);
        }
    }

    // Internal sorted-value variables, one per position, spanning the x range.
    // These carry the y = sort(x) relation (via the inner Sort) and channel to p.
    _y.clear();
    for (size_t j = 0; j < _x.size(); ++j)
        _y.push_back(initial_state.allocate_integer_variable_with_state(_lowest_x, _highest_x));

    return true;
}

auto ArgSort::define_proof_model(ProofModel & model) -> void
{
    auto n = _x.size();

    // p is a permutation of {offset, ..., offset + n - 1}: at most one position
    // can take each value (with the range bounds above, this forces a bijection).
    for (Integer v = _offset; v < _offset + Integer(n); ++v) {
        WPBSum at_most_one;
        for (const auto & p_j : _p)
            at_most_one += 1_i * (p_j == v);
        model.add_constraint("ArgSort", "permutation", move(at_most_one) <= 1_i);
    }

    // y[j] is the value at sorted position j, i.e. y[j] = x[p[j] - offset].
    // Channel it in via the permutation literals. (y is the inner Sort's real
    // sorted-value variable, already constrained to be sort(x).)
    for (size_t j = 0; j < n; ++j)
        for (size_t k = 0; k < n; ++k)
            model.add_constraint("ArgSort", "value channel",
                WPBSum{} + 1_i * _y[j] + -1_i * _x[k] == 0_i,
                HalfReifyOnConjunctionOf{{_p[j] == _offset + Integer(k)}});

    // Inverse channel to the stable rank: position j holds element k exactly
    // when element k's stable rank pos[k] is j. This is definitionally true
    // (p[j] = offset + k <-> pos[k] = j) and lets the rank-interval propagator
    // turn pos[k]'s provable bounds (from the inner Sort's "before" counting)
    // into prunings of p.
    for (size_t j = 0; j < n; ++j)
        for (size_t k = 0; k < n; ++k)
            model.add_constraint("ArgSort", "rank channel",
                WPBSum{} + 1_i * _witness.pos[k] == Integer(static_cast<long long>(j)),
                HalfReifyOnConjunctionOf{{_p[j] == _offset + Integer(k)}});

    // Stable tie-break. The inner Sort already constrains y[j] <= y[j+1], so an
    // eq flag fully reifying y[j] >= y[j+1] captures exactly the ties:
    //   eq_j <-> y[j] >= y[j+1]   (given y non-decreasing, this means equality)
    //   eq_j -> p[j] + 1 <= p[j+1]   (ties broken by original index)
    for (size_t j = 0; j + 1 < n; ++j) {
        auto eq = model.create_proof_flag_fully_reifying("argsort_eq",
            "ArgSort", "tie value",
            WPBSum{} + 1_i * _y[j] + -1_i * _y[j + 1] >= 0_i);

        model.add_constraint("ArgSort", "stable tie-break",
            WPBSum{} + 1_i * _p[j] + -1_i * _p[j + 1] <= -1_i,
            HalfReifyOnConjunctionOf{{eq}});
    }
}

auto ArgSort::install_propagators(Propagators & propagators) -> void
{
    auto n = _x.size();
    vector<IntegerVariableID> y_ids{_y.begin(), _y.end()};

    // Channel-consistency propagator linking the permutation p to the source x
    // and the inner Sort's sorted values y, via y[j] = x[p[j] - offset]:
    //   (1) if dom(x[k]) and dom(y[j]) are disjoint, then p[j] != offset + k;
    //   (2) once p[j] = offset + k is fixed, x[k] and y[j] hold equal values,
    //       so intersect their bounds.
    // The inner Sort already keeps x and y bounds(Z)-consistent; this pass turns
    // those tightened bounds into permutation prunings (and back). The
    // achievable-rank-set propagator below brings p all the way to bounds(Z)
    // consistency (full GAC on p is NP-hard).
    Triggers channel_triggers;
    channel_triggers.on_bounds.insert(channel_triggers.on_bounds.end(), _x.begin(), _x.end());
    channel_triggers.on_bounds.insert(channel_triggers.on_bounds.end(), y_ids.begin(), y_ids.end());
    channel_triggers.on_change.insert(channel_triggers.on_change.end(), _p.begin(), _p.end());

    propagators.install([x = _x, y = y_ids, p = _p, offset = _offset, n](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        for (size_t j = 0; j < n; ++j) {
            auto [ylo, yhi] = state.bounds(y[j]);

            for (size_t k = 0; k < n; ++k) {
                auto pv = offset + Integer(static_cast<long long>(k));
                if (! state.in_domain(p[j], pv))
                    continue;

                auto [xlo, xhi] = state.bounds(x[k]);

                // (1) Disjoint domains rule out position j taking original index k.
                if (xhi < ylo || xlo > yhi) {
                    inference.infer_not_equal(logger, p[j], pv, JustifyUsingRUP{},
                        bounds_reason(state, {x[k], y[j]}));
                }
            }

            // (2) If p[j] is fixed to some index k, x[k] and y[j] are equal:
            // intersect their bounds in both directions.
            if (auto pj = state.optional_single_value(p[j])) {
                auto k = (*pj - offset).as_index();
                auto [xlo, xhi] = state.bounds(x[k]);
                auto extra = p[j] == *pj;
                if (xlo > ylo)
                    inference.infer_greater_than_or_equal(logger, y[j], xlo, JustifyUsingRUP{},
                        bounds_reason(state, {x[k]}, extra));
                if (xhi < yhi)
                    inference.infer_less_than(logger, y[j], xhi + 1_i, JustifyUsingRUP{},
                        bounds_reason(state, {x[k]}, extra));
                if (ylo > xlo)
                    inference.infer_greater_than_or_equal(logger, x[k], ylo, JustifyUsingRUP{},
                        bounds_reason(state, {y[j]}, extra));
                if (yhi < xhi)
                    inference.infer_less_than(logger, x[k], yhi + 1_i, JustifyUsingRUP{},
                        bounds_reason(state, {y[j]}, extra));
            }
        }

        return PropagatorState::Enable;
    },
        channel_triggers);

    // Achievable-rank-set propagator: gives bounds(Z) consistency on p. Element
    // k's stable rank pos[k] (the number of elements before it) lies in
    // [a_k, b_k] (must-precede .. can-precede counts), but ties among the other
    // elements can leave HOLES in that interval. We compute k's exact reachable
    // rank set and, since p[j]=offset+k <-> pos[k]=j, prune p[j] != offset+k for
    // every unreachable position j. (If j is reachable, some x-assignment puts k
    // at rank j and is a full solution, so this is exactly BC on p.)
    Triggers rank_triggers;
    rank_triggers.on_bounds.insert(rank_triggers.on_bounds.end(), _x.begin(), _x.end());
    rank_triggers.on_change.insert(rank_triggers.on_change.end(), _p.begin(), _p.end());

    propagators.install([x = _x, p = _p, offset = _offset, n, witness = _witness](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        for (size_t k = 0; k < n; ++k) {
            auto [lk, uk] = state.bounds(x[k]);

            // must_precede[i]: i comes before k in EVERY assignment; can_precede:
            // in SOME assignment. Stable order: i<k ties to i (use <=), i>k ties
            // to k (use <). a_k = #must, b_k = #can; pos[k] (the stable rank of k)
            // lies in [a_k, b_k].
            vector<bool> must_precede(n, false), can_precede(n, false);
            long long a_k = 0, b_k = 0;
            for (size_t i = 0; i < n; ++i) {
                if (i == k)
                    continue;
                auto [li, ui] = state.bounds(x[i]);
                must_precede[i] = (i < k) ? (ui <= lk) : (ui < lk);
                can_precede[i] = (i < k) ? (li <= uk) : (li < uk);
                if (must_precede[i])
                    ++a_k;
                if (can_precede[i])
                    ++b_k;
            }

            // The achievable rank SET of element k can be a strict subset of the
            // interval [a_k, b_k]: ties among the other elements make the "number
            // below k" jump as x[k] crosses their values, leaving holes. For each
            // candidate value vk of x[k], the count of elements before k can be
            // any integer in [#forced(vk), #possible(vk)]; the union over vk (it
            // suffices to sample the O(n) regime breakpoints) is the reachable
            // set. Position j can hold element k only if j is reachable.
            vector<bool> reachable(n, false);
            {
                vector<long long> cands{lk.raw_value, uk.raw_value};
                for (size_t i = 0; i < n; ++i) {
                    if (i == k)
                        continue;
                    auto [li, ui] = state.bounds(x[i]);
                    for (long long t : {li.raw_value, ui.raw_value, li.raw_value + 1, ui.raw_value + 1,
                             li.raw_value - 1, ui.raw_value - 1})
                        if (t >= lk.raw_value && t <= uk.raw_value)
                            cands.push_back(t);
                }
                for (long long vk : cands) {
                    long long forced = 0, possible = 0;
                    for (size_t i = 0; i < n; ++i) {
                        if (i == k)
                            continue;
                        auto [li, ui] = state.bounds(x[i]);
                        bool f = (i < k) ? (ui.raw_value <= vk) : (ui.raw_value < vk);
                        bool c = (i < k) ? (li.raw_value <= vk) : (li.raw_value < vk);
                        if (f)
                            ++forced;
                        if (c)
                            ++possible;
                    }
                    for (long long r = forced; r <= possible; ++r)
                        if (r >= 0 && cmp_less(r, n))
                            reachable[r] = true;
                }
            }

            for (size_t j = 0; j < n; ++j) {
                if (reachable[j])
                    continue;
                auto pv = offset + Integer(static_cast<long long>(k));
                if (! state.in_domain(p[j], pv))
                    continue;

                bool below = cmp_less(j, a_k);
                bool above = cmp_greater(j, b_k);
                if (below || above) {
                    // Outside the rank interval: the cross-variable rank deduction
                    // is not plain RUP, so derive the rank bound by an explicit
                    // pol, mirroring the Sort propagator. below: pos[k] >= a_k via
                    // rank_ge[k] + the forced "before[i][k] >= 1" lines; above:
                    // pos[k] <= b_k via rank_le[k] + the forced "!before[i][k]"
                    // lines. The inverse channel (p[j]=offset+k -> pos[k]=j) then
                    // makes p[j] != offset+k RUP.
                    inference.infer_not_equal(logger, p[j], pv,
                        JustifyExplicitlyThenRUP{[&, k, j, below](const ReasonFunction & reason_fn) -> void {
                            PolBuilder pol;
                            if (below) {
                                pol.add(witness.rank_ge[k]);
                                for (size_t i = 0; i < n; ++i)
                                    if (i != k && must_precede[i])
                                        pol.add(logger->emit_rup_proof_line_under_reason(reason_fn,
                                            WPBSum{} + 1_i * witness.before[i][k] >= 1_i, ProofLevel::Temporary));
                            }
                            else {
                                pol.add(witness.rank_le[k]);
                                for (size_t i = 0; i < n; ++i)
                                    if (i != k && ! can_precede[i])
                                        pol.add(logger->emit_rup_proof_line_under_reason(reason_fn,
                                            WPBSum{} + 1_i * ! witness.before[i][k] >= 1_i, ProofLevel::Temporary));
                            }
                            pol.emit(*logger, ProofLevel::Temporary);
                        }},
                        bounds_reason(state, x));
                }
                else {
                    // Hole inside [a_k, b_k]: rank j is unreachable because of a
                    // tie-jump in the "number below k". There is a threshold value
                    // U with #possible(U) <= j-1 and #forced(U+1) >= j+1, so
                    //   x[k] <= U   => pos[k] <= #possible(U) <= j-1, and
                    //   x[k] >= U+1 => pos[k] >= #forced(U+1) >= j+1,
                    // both excluding pos[k] = j. Prove each side by a pol (mirror
                    // of the interval case, but pivoting on the constant U instead
                    // of x[k]'s own bound), then the inverse channel makes
                    // p[j] != offset+k RUP via the case split on [x[k] >= U+1].
                    auto possible_at = [&](long long v) {
                        long long c = 0;
                        for (size_t i = 0; i < n; ++i) {
                            if (i == k)
                                continue;
                            auto [li, ui] = state.bounds(x[i]);
                            if ((i < k) ? (li.raw_value <= v) : (li.raw_value < v))
                                ++c;
                        }
                        return c;
                    };
                    // U = largest value with #possible(U) <= j-1 (exists: a hole
                    // has #possible(lk) <= j-1 and #possible(uk) = b_k >= j).
                    long long U = lk.raw_value;
                    for (long long v = lk.raw_value; v < uk.raw_value; ++v) {
                        if (cmp_less(possible_at(v + 1), j))
                            U = v + 1;
                        else
                            break;
                    }

                    inference.infer_not_equal(logger, p[j], pv,
                        JustifyExplicitlyThenRUP{[&, k, j, U](const ReasonFunction & reason_fn) -> void {
                            // Line A: x[k] <= U => pos[k] <= #possible(U).
                            // For each i that cannot precede k at x[k]=U, the clause
                            // (x[k] >= U+1) v !before[i][k] is RUP from before_fwd +
                            // the bound on x[i]; rank_le[k] folds them in.
                            PolBuilder polA;
                            polA.add(witness.rank_le[k]);
                            for (size_t i = 0; i < n; ++i) {
                                if (i == k)
                                    continue;
                                auto [li, ui] = state.bounds(x[i]);
                                bool cannot = (i < k) ? (li.raw_value > U) : (li.raw_value >= U);
                                if (cannot)
                                    polA.add(logger->emit_rup_proof_line_under_reason(reason_fn,
                                        WPBSum{} + 1_i * (x[k] >= Integer{U + 1}) + 1_i * ! witness.before[i][k] >= 1_i,
                                        ProofLevel::Temporary));
                            }
                            polA.emit(*logger, ProofLevel::Temporary);

                            // Line B: x[k] >= U+1 => pos[k] >= #forced(U+1).
                            // For each i forced to precede k at x[k]=U+1, the clause
                            // (x[k] <= U) v before[i][k] is RUP from before_rev +
                            // the bound on x[i]; rank_ge[k] folds them in.
                            PolBuilder polB;
                            polB.add(witness.rank_ge[k]);
                            for (size_t i = 0; i < n; ++i) {
                                if (i == k)
                                    continue;
                                auto [li, ui] = state.bounds(x[i]);
                                bool forced = (i < k) ? (ui.raw_value <= U + 1) : (ui.raw_value <= U);
                                if (forced)
                                    polB.add(logger->emit_rup_proof_line_under_reason(reason_fn,
                                        WPBSum{} + 1_i * (x[k] < Integer{U + 1}) + 1_i * witness.before[i][k] >= 1_i,
                                        ProofLevel::Temporary));
                            }
                            polB.emit(*logger, ProofLevel::Temporary);
                        }},
                        bounds_reason(state, x));
                }
            }
        }

        return PropagatorState::Enable;
    },
        rank_triggers);

    // GAC on the all_different aspect of p (it is a permutation of the n
    // positions). Reuses the framework's matching/Hall propagator and its
    // certified justifications; the per-value at-most-one lines the proof model
    // emits make the pairwise not-equals clauses RUP, so the (initially empty)
    // am1 line cache fills itself lazily.
    vector<Integer> p_vals;
    for (Integer v = _offset; v < _offset + Integer(static_cast<long long>(n)); ++v)
        p_vals.push_back(v);
    auto am1_lines = make_shared<map<Integer, ProofLine>>();

    Triggers ad_triggers;
    ad_triggers.on_change.insert(ad_triggers.on_change.end(), _p.begin(), _p.end());

    propagators.install([p = _p, vals = move(p_vals), am1_lines](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        propagate_gac_all_different(p, vals, vector<Integer>{}, *am1_lines, state, inference, logger);
        return PropagatorState::Enable;
    },
        ad_triggers);

    // No leaf-checking propagator is needed: once every x is fixed, each
    // element k's reachable-rank set collapses to the single stable rank, so the
    // achievable-rank-set propagator (with GAC all_different) prunes p down to
    // the one correct permutation -- any wrong p is a domain wipeout before a
    // leaf is reached. A former checking-only propagator here was confirmed dead
    // (full enumeration + BC consistency + VeriPB all unchanged when removed).
}

auto ArgSort::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} arg_sort\n          (", _name);
    for (const auto & v : _x)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, ")\n          (");
    for (const auto & v : _p)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, ")\n          {})", _offset);

    return s.str();
}
