#include <gcs/constraints/global_cardinality/bounds_global_cardinality.hh>
#include <gcs/constraints/global_cardinality/hints.hh>
#include <gcs/constraints/in.hh>
#include <gcs/constraints/innards/recover_am1.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <sstream>
#include <string>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::binary_search;
using std::holds_alternative;
using std::make_unique;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::sort;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

auto gcs::innards::propagate_bounds_global_cardinality(const vector<IntegerVariableID> & vars, const ConstraintID & owner,
    const vector<Integer> & values, const vector<IntegerVariableID> & counts,
    const vector<pair<optional<ProofLine>, optional<ProofLine>>> & count_lines, const vector<IntegerVariableID> & all_vars, const State & state,
    auto & inference, ProofLogger * const logger) -> PropagatorState
{
    auto m = values.size();

    // Part 1: per-value (singleton Hall) reasoning, with real RUP
    // justifications. For each cover value this gives the count variable
    // its must-occur lower bound and can-occur upper bound, removes a
    // value whose upper capacity is saturated by the variables fixed to
    // it, and forces the variables into a value whose lower demand can
    // only just be met.
    // Counting comes first; the reason literals are only gathered -- in the
    // same variable order, from the same state (nothing this loop infers
    // changes which variables are fixed to or excluded from `value`) -- when
    // an inference actually fires.
    for (const auto & [j, value] : enumerate(values)) {
        Integer must = 0_i, can = 0_i;
        for (const auto & var : vars)
            if (state.in_domain(var, value)) {
                ++can;
                if (state.has_single_value(var))
                    ++must;
            }

        auto gather_fixed_eq = [&](ReasonLiterals & out) {
            out.clear();
            for (const auto & var : vars)
                if (state.in_domain(var, value) && state.has_single_value(var))
                    out.emplace_back(var == value);
        };
        auto gather_absent_ne = [&](ReasonLiterals & out) {
            out.clear();
            for (const auto & var : vars)
                if (! state.in_domain(var, value))
                    out.emplace_back(var != value);
        };

        auto [lb_j, ub_j] = state.bounds(counts[j]);

        // c_j >= must: the fixed variables alone force the count up.
        if (must > lb_j) {
            ReasonLiterals fixed_eq;
            gather_fixed_eq(fixed_eq);
            inference.infer(logger, counts[j] >= must, JustifyUsingRUP{hints::GlobalCardinality{owner}}, ExplicitReason{fixed_eq});
        }

        // c_j <= can: only the variables that can still take value may
        // contribute to the count.
        if (can < ub_j) {
            ReasonLiterals absent_ne;
            gather_absent_ne(absent_ne);
            inference.infer(logger, counts[j] <= can, JustifyUsingRUP{hints::GlobalCardinality{owner}}, ExplicitReason{absent_ne});
        }

        // Saturated capacity: if as many variables are already fixed to
        // value as the count's upper bound allows, no other variable may
        // take it.
        if (must == ub_j) {
            ReasonLiterals sat;
            bool have_sat = false;
            for (const auto & var : vars)
                if (state.in_domain(var, value) && ! state.has_single_value(var)) {
                    if (! have_sat) {
                        have_sat = true;
                        gather_fixed_eq(sat);
                        sat.emplace_back(counts[j] <= ub_j);
                    }
                    inference.infer(logger, var != value, JustifyUsingRUP{hints::GlobalCardinality{owner}}, ExplicitReason{sat});
                }
        }

        // Just-met demand: if only `can` variables can take value and the
        // count's lower bound needs all of them, each is forced to value.
        if (can == lb_j && can > 0_i) {
            ReasonLiterals force;
            bool have_force = false;
            for (const auto & var : vars)
                if (state.in_domain(var, value) && ! state.has_single_value(var)) {
                    if (! have_force) {
                        have_force = true;
                        gather_absent_ne(force);
                        force.emplace_back(counts[j] >= lb_j);
                    }
                    for (const auto & w : state.each_value_mutable(var))
                        if (w != value)
                            inference.infer(logger, var != w, JustifyUsingRUP{hints::GlobalCardinality{owner}}, ExplicitReason{force});
                }
        }
    }

    // Part 2: multi-value Hall intervals over contiguous runs of the
    // (sorted, distinct) cover values. This is the genuine cross-value
    // strengthening beyond per-value reasoning: count-variable bound
    // tightening, variable-domain pruning in both Hall directions, and
    // infeasibility. All have real pol justifications.
    // The hall set for a pair (a, b) is the contiguous slice values[a..b] of
    // the sorted, distinct cover, so membership is a binary search over that
    // slice and iteration is the slice itself, in the same ascending order
    // the set gave -- no per-pair set, and the confined/potential vectors are
    // hoisted out of the pair loops and reused.
    vector<IntegerVariableID> confined, potential;
    for (std::size_t a = 0; a < m; ++a) {
        Integer cap = 0_i, demand = 0_i;
        {
            auto [c_lo, c_hi] = state.bounds(counts[a]);
            cap += c_hi;
            demand += c_lo;
        }
        for (std::size_t b = a + 1; b < m; ++b) {
            auto hall_contains = [&, a = a, b = b](Integer val) -> bool {
                return binary_search(values.begin() + static_cast<std::ptrdiff_t>(a), values.begin() + static_cast<std::ptrdiff_t>(b) + 1, val);
            };
            {
                auto [c_lo, c_hi] = state.bounds(counts[b]);
                cap += c_hi;
                demand += c_lo;
            }

            auto domain_subset_of_hall = [&](const IntegerVariableID & var) -> bool {
                bool subset = true;
                state.for_each_value_immutable(var, [&](Integer val) -> bool {
                    if (! hall_contains(val)) {
                        subset = false;
                        return false;
                    }
                    return true;
                });
                return subset;
            };
            auto domain_meets_hall = [&](const IntegerVariableID & var) -> bool {
                for (std::size_t v = a; v <= b; ++v)
                    if (state.in_domain(var, values[v]))
                        return true;
                return false;
            };

            confined.clear();
            potential.clear();
            for (const auto & var : vars) {
                if (domain_subset_of_hall(var))
                    confined.push_back(var);
                if (domain_meets_hall(var))
                    potential.push_back(var);
            }
            auto confined_count = Integer(confined.size());
            auto potential_count = Integer(potential.size());

            // The capacity aggregate: summing the per-value count upper
            // lines (Sum_i x_{i=v} <= c_v), the count upper bounds
            // (c_v <= ub_v), and an at-least-one over the hall set for
            // each confined variable yields
            //   Sum_{i not confined, v in H} x_{i=v} <= cap - confined.
            // When confined == cap this is <= 0, RUP-closing each removal;
            // when confined > cap it is already contradictory. Passing a
            // `keep` index suppresses that value's c_v <= ub_v step so its
            // count variable survives uncancelled, which RUP-closes the
            // count lower bound c_keep >= confined - (cap - ub_keep).
            auto emit_capacity_pol = [&, a = a, b = b](optional<std::size_t> keep) {
                auto & tracker = logger->names_and_ids_tracker();
                PolBuilder pb;
                for (std::size_t v = a; v <= b; ++v) {
                    pb.add(*count_lines[v].first);
                    // A constant count already folds its bound into the
                    // count line; only a real variable needs c_v <= ub_v.
                    if (keep != optional<std::size_t>{v} && ! holds_alternative<ConstantIntegerVariableID>(counts[v]))
                        pb.add_for_literal(tracker, counts[v] <= state.bounds(counts[v]).second);
                }
                for (const auto & var : confined)
                    pb.add(tracker.need_constraint_saying_variable_takes_at_least_one_value(var));
                pb.emit(*logger, ProofLevel::Temporary);
            };

            auto capacity_reason = [&, a = a, b = b](optional<std::size_t> exclude) -> ReasonLiterals {
                ReasonLiterals r;
                for (const auto & var : confined) {
                    auto [v_lo, v_hi] = state.bounds(var);
                    for (Integer s = v_lo; s <= v_hi; ++s)
                        if (! hall_contains(s) && ! state.in_domain(var, s))
                            r.emplace_back(var != s);
                    r.emplace_back(var >= v_lo);
                    r.emplace_back(var <= v_hi);
                }
                for (std::size_t v = a; v <= b; ++v)
                    if (exclude != optional<std::size_t>{v} && ! holds_alternative<ConstantIntegerVariableID>(counts[v]))
                        r.emplace_back(counts[v] <= state.bounds(counts[v]).second);
                return r;
            };

            // The per-value capacity lines Sum_i x_{i=v} <= ub_v and
            // Sum_i x_{i=v} >= lb_v. Each is a direct consequence of the
            // count line (Sum_i x_{i=v} = c_v) and the count bound, but
            // combining them in a pol is blocked because the count line
            // carries c_v in its bit encoding while the bound is an
            // order-encoding atom (and is vacuous at the bit-width
            // boundary). These two true facts are asserted; everything
            // built on top of them is real, so the surrounding Hall
            // combinatorics is genuinely checked.
            auto demand_reason = [&, a = a, b = b](optional<std::size_t> exclude) -> ReasonLiterals {
                ReasonLiterals r;
                for (const auto & var : vars)
                    if (! domain_meets_hall(var))
                        for (std::size_t v = a; v <= b; ++v)
                            r.emplace_back(var != values[v]);
                for (std::size_t v = a; v <= b; ++v)
                    if (exclude != optional<std::size_t>{v} && ! holds_alternative<ConstantIntegerVariableID>(counts[v]))
                        r.emplace_back(counts[v] >= state.bounds(counts[v]).first);
                return r;
            };

            for (std::size_t j = a; j <= b; ++j) {
                auto [lb_j, ub_j] = state.bounds(counts[j]);
                auto lower = confined_count - (cap - ub_j);
                if (lower > lb_j)
                    // For each v != j sum the count line LE_v with the
                    // defining implication of c_v <= ub_v (add_for_literal,
                    // which resolves the order-encoded bound against
                    // BinEnc(c_v) so the bits cancel, leaving Sum_i x_{i=v}
                    // <= ub_v reified by the gevar). Add an at-least-one
                    // over H per confined variable and the j count line
                    // LE_j; this yields c_j - Sum_{i not confined} x >= L.
                    // The final RUP closes c_j >= L; its reason supplies
                    // c_v <= ub_v (v != j), discharging the gevars.
                    inference.infer(logger, counts[j] >= lower,
                        JustifyExplicitly{//
                            [&, a = a, b = b, j = j](const ReasonLiterals &) {
                                auto & tracker = logger->names_and_ids_tracker();
                                PolBuilder pb;
                                for (std::size_t v = a; v <= b; ++v)
                                    if (v != j) {
                                        pb.add(*count_lines[v].first);
                                        if (! holds_alternative<ConstantIntegerVariableID>(counts[v]))
                                            pb.add_for_literal(tracker, counts[v] <= state.bounds(counts[v]).second);
                                    }
                                for (const auto & var : confined)
                                    pb.add(tracker.need_constraint_saying_variable_takes_at_least_one_value(var));
                                pb.add(*count_lines[j].first);
                                pb.emit(*logger, ProofLevel::Temporary);
                            },
                            ThenRUP::Yes, hints::GlobalCardinality{owner}},
                        LazyReasonOver{vars, [&, j = j](const State &, ReasonLiterals & out) { out = capacity_reason(j); }});
                auto upper = potential_count - (demand - lb_j);
                if (upper < ub_j)
                    // Dual: at-most-one over H per potential variable, the
                    // count lines GE_v with the defining implication of
                    // c_v >= lb_v for v != j, and the j count line GE_j;
                    // RUP-closes c_j <= U, the reason discharging the gevars.
                    inference.infer(logger, counts[j] <= upper,
                        JustifyExplicitly{//
                            [&, a = a, b = b, j = j](const ReasonLiterals &) {
                                auto & tracker = logger->names_and_ids_tracker();
                                PolBuilder pb;
                                for (const auto & var : potential) {
                                    vector<IntegerVariableCondition> atoms;
                                    for (std::size_t v = a; v <= b; ++v)
                                        atoms.push_back(var == values[v]);
                                    pb.add(recover_am1<IntegerVariableCondition>(*logger, ProofLevel::Temporary, atoms,
                                        [&](const IntegerVariableCondition & p, const IntegerVariableCondition & q) {
                                            return logger->emit(RUPProofRule{}, WPBSum{} + 1_i * ! p + 1_i * ! q >= 1_i, ProofLevel::Temporary);
                                        }));
                                }
                                for (std::size_t v = a; v <= b; ++v)
                                    if (v != j) {
                                        pb.add(*count_lines[v].second);
                                        if (! holds_alternative<ConstantIntegerVariableID>(counts[v]))
                                            pb.add_for_literal(tracker, counts[v] >= state.bounds(counts[v]).first);
                                    }
                                pb.add(*count_lines[j].second);
                                pb.emit(*logger, ProofLevel::Temporary);
                            },
                            ThenRUP::Yes, hints::GlobalCardinality{owner}},
                        LazyReasonOver{vars, [&, j = j](const State &, ReasonLiterals & out) { out = demand_reason(j); }});
            }

            if (confined_count > cap) {
                inference.contradiction(logger,
                    JustifyExplicitly{[&](const ReasonLiterals &) { emit_capacity_pol(nullopt); }, ThenRUP::Yes, hints::GlobalCardinality{owner}},
                    LazyReasonOver{vars, [&](const State &, ReasonLiterals & out) { out = capacity_reason(nullopt); }});
            }
            else if (confined_count == cap) {
                for (const auto & var : vars) {
                    if (domain_subset_of_hall(var))
                        continue;
                    for (std::size_t v = a; v <= b; ++v)
                        if (Integer val = values[v]; state.in_domain(var, val))
                            inference.infer(logger, var != val,
                                JustifyExplicitly{
                                    [&](const ReasonLiterals &) { emit_capacity_pol(nullopt); }, ThenRUP::Yes, hints::GlobalCardinality{owner}},
                                LazyReasonOver{vars, [&](const State &, ReasonLiterals & out) { out = capacity_reason(nullopt); }});
                }
            }

            // The demand aggregate (dual of the capacity one): summing
            // the per-value count lower lines (Sum_i x_{i=v} >= c_v), the
            // count lower bounds (c_v >= lb_v), and an at-most-one over
            // the hall set for each potential variable yields
            //   Sum_{i not potential, v in H} x_{i=v} >= demand - potential.
            // When demand > potential this is contradictory; when
            // demand == potential, giving one potential variable an
            // at-most-one over H u {w} instead RUP-closes its removal of
            // the outside value w.
            auto emit_demand_pol = [&, a = a, b = b](optional<IntegerVariableID> kvar, Integer kw) {
                auto & tracker = logger->names_and_ids_tracker();
                PolBuilder pb;
                for (std::size_t v = a; v <= b; ++v) {
                    pb.add(*count_lines[v].second);
                    if (! holds_alternative<ConstantIntegerVariableID>(counts[v]))
                        pb.add_for_literal(tracker, counts[v] >= state.bounds(counts[v]).first);
                }
                for (const auto & var : potential) {
                    vector<IntegerVariableCondition> atoms;
                    for (std::size_t v = a; v <= b; ++v)
                        atoms.push_back(var == values[v]);
                    if (kvar == optional<IntegerVariableID>{var})
                        atoms.push_back(var == kw);
                    pb.add(recover_am1<IntegerVariableCondition>(
                        *logger, ProofLevel::Temporary, atoms, [&](const IntegerVariableCondition & p, const IntegerVariableCondition & q) {
                            return logger->emit(RUPProofRule{}, WPBSum{} + 1_i * ! p + 1_i * ! q >= 1_i, ProofLevel::Temporary);
                        }));
                }
                pb.emit(*logger, ProofLevel::Temporary);
            };

            if (potential_count < demand) {
                inference.contradiction(logger,
                    JustifyExplicitly{[&](const ReasonLiterals &) { emit_demand_pol(nullopt, 0_i); }, ThenRUP::Yes, hints::GlobalCardinality{owner}},
                    LazyReasonOver{vars, [&](const State &, ReasonLiterals & out) { out = demand_reason(nullopt); }});
            }
            else if (potential_count == demand) {
                for (const auto & var : potential)
                    for (const auto & val : state.each_value_mutable(var))
                        if (! hall_contains(val))
                            inference.infer(logger, var != val,
                                JustifyExplicitly{[&, var = var, val = val](const ReasonLiterals &) { emit_demand_pol(var, val); }, ThenRUP::Yes,
                                    hints::GlobalCardinality{owner}},
                                LazyReasonOver{vars, [&](const State &, ReasonLiterals & out) { out = demand_reason(nullopt); }});
            }
        }
    }

    return PropagatorState::Enable;
}

template auto gcs::innards::propagate_bounds_global_cardinality(const std::vector<IntegerVariableID> & vars, const ConstraintID & owner,
    const std::vector<Integer> & values, const std::vector<IntegerVariableID> & counts,
    const std::vector<std::pair<std::optional<ProofLine>, std::optional<ProofLine>>> & count_lines, const std::vector<IntegerVariableID> & all_vars,
    const State & state, SimpleInferenceTracker & inference, ProofLogger * const logger) -> PropagatorState;

template auto gcs::innards::propagate_bounds_global_cardinality(const std::vector<IntegerVariableID> & vars, const ConstraintID & owner,
    const std::vector<Integer> & values, const std::vector<IntegerVariableID> & counts,
    const std::vector<std::pair<std::optional<ProofLine>, std::optional<ProofLine>>> & count_lines, const std::vector<IntegerVariableID> & all_vars,
    const State & state, EagerProofLoggingInferenceTracker & inference, ProofLogger * const logger) -> PropagatorState;
