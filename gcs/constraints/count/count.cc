#include <gcs/constraints/count/count.hh>
#include <gcs/constraints/count/hints.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <optional>
#include <sstream>
#include <string>
#include <tuple>

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::string;
using std::stringstream;
using std::tuple;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

Count::Count(std::vector<IntegerVariableID> vars, const IntegerVariableID & value_of_interest, const IntegerVariableID & how_many) :
    _vars(move(vars)), _value_of_interest(value_of_interest), _how_many(how_many)
{
}

auto Count::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Count>(_vars, _value_of_interest, _how_many);
}

auto Count::define_proof_model(ProofModel & model, const State &) -> void
{
    // Conform to cake_pb_cp's count encoding (#354): per position i, the
    // flags x[id][i][ge] ⇔ var ≥ val, x[id][i][le] ⇔ var ≤ val, and
    // x[id][i][eq] ⇔ (ge ∧ le) ⇔ var = val. (The solver previously used
    // strict gt/lt and eq ⇔ ¬gt ∧ ¬lt; the equality flag means the same
    // thing — var = val — which is all the propagator references.)
    for (const auto & [i, var] : enumerate(_vars)) {
        vector<long long> pos{static_cast<long long>(i)};

        auto ge = model.create_proof_flag_fully_reifying(_constraint_id, pos, "ge", WPBSum{} + 1_i * var + -1_i * _value_of_interest >= 0_i);

        auto le = model.create_proof_flag_fully_reifying(_constraint_id, pos, "le", WPBSum{} + 1_i * var + -1_i * _value_of_interest <= 0_i);

        auto eq = model.create_proof_flag_fully_reifying(_constraint_id, pos, "eq", WPBSum{} + 1_i * ge + 1_i * le >= 2_i);

        _flags.emplace_back(eq, ge, le);
    }

    // sum of equal flags == how_many, as cake's c[id][le] / c[id][ge] halves
    WPBSum how_many_sum;
    for (auto & [eq, _1, _2] : _flags)
        how_many_sum += 1_i * eq;
    how_many_sum += -1_i * _how_many;

    model.add_labelled_constraint(_constraint_id, "le", "ge", how_many_sum == 0_i);
}

auto Count::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());
    triggers.on_change.emplace_back(_value_of_interest);
    // Not only how_many's bounds: the value-of-interest support test below asks
    // whether each achievable count is still in how_many's domain, so a hole in
    // how_many can leave a value of interest with no support (issue #966).
    triggers.on_change.emplace_back(_how_many);

    vector<IntegerVariableID> all_vars = _vars;
    all_vars.push_back(_value_of_interest);
    all_vars.push_back(_how_many);

    // The reason ranges over the whole (fixed) variable scope, so build it once
    // here and reuse it at every inference site rather than reconstructing it —
    // and re-copying the scope into a fresh shared_ptr — on each inference. See
    // dev_docs/propagator-performance.md.
    auto all_vars_reason = generic_reason(all_vars);

    propagators.install(
        constraint_id(),
        [vars = _vars, value_of_interest = _value_of_interest, how_many = _how_many, flags = _flags, reason = std::move(all_vars_reason),
            owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // check support for how many by seeing how many array values
            // intersect with a potential value of interest
            int how_many_definitely_do_not = 0;
            auto viable_places = 0_i;
            for (auto & var : vars) {
                if (state.domains_intersect(value_of_interest, var))
                    ++viable_places;
                else
                    ++how_many_definitely_do_not;
            }

            // can't have more that this many occurrences of the value of interest
            auto how_many_is_less_than = Integer(vars.size() - how_many_definitely_do_not) + 1_i;
            auto justf = [&](const ReasonLiterals & reason) -> void {
                for (const auto & [idx, var] : enumerate(vars)) {
                    if (! state.domains_intersect(var, value_of_interest)) {
                        for (const auto & val : state.each_value_immutable(value_of_interest))
                            logger->emit_rup_proof_line_under_reason(
                                reason, WPBSum{} + 1_i * (value_of_interest != val) + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                    }
                }
            };
            // The _or_stop family throughout this propagator, rather than the
            // throwing infer: Count is the failure detector at a large share of
            // the nodes of the rostering and puzzle models that use it -- 6.0M
            // unwinds over seven MiniZinc Challenge models in the throw survey,
            // where the unwinder is 11-15% of the run. Same inference, same
            // proof step, same reason; only the way out of the propagator
            // differs, and [[nodiscard]] makes forgetting to take it an error.
            if (! inference.infer_less_than_or_stop(
                    logger, how_many, how_many_is_less_than, JustifyExplicitly{justf, ThenRUP::Yes, hints::Count{owner}}, reason))
                return PropagatorState::DisableUntilBacktrack;

            // must have at least this many occurrences of the value of interest
            int how_many_must = 0;
            auto voi = state.optional_single_value(value_of_interest);
            if (voi) {
                for (auto & v : vars)
                    if (state.optional_single_value(v) == voi)
                        ++how_many_must;
            }
            if (! inference.infer_greater_than_or_equal_or_stop(
                    logger, how_many, Integer(how_many_must), JustifyUsingRUP{hints::Count{owner}}, reason))
                return PropagatorState::DisableUntilBacktrack;

            // is each value of interest supported? also track how_many bounds supports
            // whilst we're here
            optional<Integer> lowest_how_many_must, highest_how_many_might;
            // Does how_many's domain hold any count in [lo, hi]? Usually an end of
            // the range does, so try those before walking the domain.
            auto some_count_between = [&](Integer lo, Integer hi) -> bool {
                if (lo > hi)
                    return false;
                if (state.in_domain(how_many, lo) || state.in_domain(how_many, hi))
                    return true;
                return lo + 1_i <= hi - 1_i && state.domain_intersects_with(how_many, IntervalSet<Integer>{lo + 1_i, hi - 1_i});
            };
            // For the array pruning after the loop (issue #996). A surviving value of
            // interest v "takes every candidate" when the only count how_many allows
            // it is how_many_might, so that if value_of_interest is v then every
            // variable that can be v must be. The pruning looks at the survivors that
            // do not: with two or more of them nothing can be pruned, and with one it
            // matters whether that one leaves room for any further matches.
            int survivors_not_taking_every_candidate = 0;
            Integer lone_survivor_not_taking_every_candidate = 0_i;
            bool lone_survivor_allows_no_further_matches = false;
            // Set when a pruning below empties value_of_interest's domain, so the
            // loop leaves and the propagator returns rather than carrying on
            // reading a state that has already failed.
            bool stop = false;
            for (const auto & voi : state.each_value_mutable(value_of_interest)) {
                Integer how_many_must = 0_i, how_many_might = 0_i;
                for (const auto & var : vars) {
                    if (auto sv = state.optional_single_value(var)) {
                        if (*sv == voi) {
                            ++how_many_must;
                            ++how_many_might;
                        }
                    }
                    else if (state.in_domain(var, voi))
                        ++how_many_might;
                }

                if (how_many_might < state.lower_bound(how_many)) {
                    auto justf = [&](const ReasonLiterals & reason) -> void {
                        for (const auto & [idx, var] : enumerate(vars)) {
                            if (! state.in_domain(var, voi)) {
                                // need to help the checker see that the equality flag must be zero
                                logger->emit_rup_proof_line(
                                    WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (var != voi) + 1_i * (get<0>(flags[idx])) >= 1_i,
                                    ProofLevel::Temporary);
                                logger->emit_rup_proof_line_under_reason(
                                    reason, WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                            }
                        }
                    };
                    if (! inference.infer_not_equal_or_stop(
                            logger, value_of_interest, voi, JustifyExplicitly{justf, ThenRUP::Yes, hints::Count{owner}}, reason)) {
                        stop = true;
                        break;
                    }
                }
                else if (how_many_must > state.upper_bound(how_many)) {
                    // unlike above, we don't need to help, because the equality flag will propagate
                    // from the fixed assignment
                    if (! inference.infer_not_equal_or_stop(logger, value_of_interest, voi, JustifyUsingRUP{hints::Count{owner}}, reason)) {
                        stop = true;
                        break;
                    }
                }
                else {
                    // [how_many_must, how_many_might] is the range of counts
                    // achievable for this voi, and every count in it is reachable
                    // (turn the "might but not must" vars to voi one at a time).
                    // The two checks above only reject voi when that range lies
                    // wholly below how_many's lower bound or above its upper bound;
                    // for true GAC, voi is supported iff some count in the range is
                    // actually in how_many's domain. If the whole range falls into
                    // an interior hole of how_many, voi has no support.
                    if (! some_count_between(how_many_must, how_many_might)) {
                        auto justf = [&](const ReasonLiterals & reason) -> void {
                            // Materialise both conditional count bounds for this
                            // voi, then value_of_interest != voi follows because
                            // how_many is pinned into [must, might] while its
                            // domain (in the reason) excludes that whole range.
                            //
                            // Upper bound (value_of_interest == voi => how_many <=
                            // might): zero the eq flag of every var that cannot be
                            // voi, exactly as the highest_how_many_might proof
                            // below does.
                            for (const auto & [idx, var] : enumerate(vars)) {
                                if (! state.in_domain(var, voi)) {
                                    logger->emit_rup_proof_line_under_reason(reason,
                                        WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                                    logger->emit_rup_proof_line_under_reason(
                                        reason, WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (var != voi) >= 1_i, ProofLevel::Temporary);
                                }
                            }
                            logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (how_many < how_many_might + 1_i) >= 1_i, ProofLevel::Temporary);
                            // Lower bound (value_of_interest == voi => how_many >=
                            // must): the must vars are fixed to voi, so their eq
                            // flags propagate on their own (cf. the lowest_must
                            // proof below).
                            logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (how_many >= how_many_must) >= 1_i, ProofLevel::Temporary);
                        };
                        if (! inference.infer_not_equal_or_stop(
                                logger, value_of_interest, voi, JustifyExplicitly{justf, ThenRUP::Yes, hints::Count{owner}}, reason)) {
                            stop = true;
                            break;
                        }
                    }
                    else {
                        if ((! lowest_how_many_must) || (how_many_must < *lowest_how_many_must))
                            lowest_how_many_must = how_many_must;
                        if ((! highest_how_many_might) || (how_many_might > *highest_how_many_might))
                            highest_how_many_might = how_many_might;

                        // Past two, the answer cannot change, so stop asking.
                        if (survivors_not_taking_every_candidate < 2 && some_count_between(how_many_must, how_many_might - 1_i)) {
                            ++survivors_not_taking_every_candidate;
                            lone_survivor_not_taking_every_candidate = voi;
                            lone_survivor_allows_no_further_matches = ! some_count_between(how_many_must + 1_i, how_many_might);
                        }
                    }
                }
            }

            if (stop)
                return PropagatorState::DisableUntilBacktrack;

            // what are the supports on possible values we've seen?
            if (lowest_how_many_must) {
                auto emit = [&](const ReasonLiterals & reason) -> void {
                    for (const auto & voi : state.each_value_immutable(value_of_interest))
                        logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (how_many >= *lowest_how_many_must) >= 1_i, ProofLevel::Temporary);
                };
                auto just = JustifyExplicitly{emit, ThenRUP::Yes, hints::Count{owner}};
                if (! inference.infer_greater_than_or_equal_or_stop(logger, how_many, *lowest_how_many_must, just, reason))
                    return PropagatorState::DisableUntilBacktrack;
            }

            if (highest_how_many_might) {
                auto emit = [&](const ReasonLiterals & reason) -> void {
                    // Per-(voi, var) conditional pairs: emit when voi is
                    // in value_of_interest's domain but not var's. Outer
                    // loop is over var so we can call each_interval_minus
                    // once per var; the (A, B) pair for one (voi, var) is
                    // order-sensitive but the (voi, var) iterations
                    // themselves are not.
                    auto voi_set = state.copy_of_values(value_of_interest);
                    for (const auto & [idx, var] : enumerate(vars)) {
                        auto var_set = state.copy_of_values(var);
                        for (auto [lo, hi] : voi_set.each_interval_minus(var_set))
                            for (Integer voi = lo; voi <= hi; ++voi) {
                                logger->emit_rup_proof_line_under_reason(
                                    reason, WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                                logger->emit_rup_proof_line_under_reason(
                                    reason, WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (var != voi) >= 1_i, ProofLevel::Temporary);
                            }
                    }

                    // Per-voi unconditional lines: emit after all the
                    // conditionals so they have the full set of pairwise
                    // facts to RUP-derive against.
                    for (const auto & voi : voi_set.each())
                        logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (how_many < *highest_how_many_might + 1_i) >= 1_i,
                            ProofLevel::Temporary);
                };
                auto just = JustifyExplicitly{emit, ThenRUP::Yes, hints::Count{owner}};
                if (! inference.infer_less_than_or_stop(logger, how_many, *highest_how_many_might + 1_i, just, reason))
                    return PropagatorState::DisableUntilBacktrack;
            }

            // Now the array (issue #996). With value_of_interest = v, a variable
            // that can be v but is not yet fixed is supported at v iff how_many
            // allows a count above how_many_must, and at every other value iff
            // it allows one below how_many_might. So var = a has no support
            // exactly when every value of interest other than a takes every
            // candidate and var can take it, and a is either not a value of
            // interest or leaves no room for another match. If two or more
            // survivors do not take every candidate, between them they support
            // every value, and nothing goes. If exactly one, w, does not, only w
            // can go, and only if it allows no further matches. If they all do,
            // everything outside value_of_interest's domain goes. Either way a
            // variable loses values only if it is unfixed and can take every
            // value of interest, which it keeps, so nothing here can empty a
            // domain.
            bool removing_lone_survivor = survivors_not_taking_every_candidate == 1;
            if (survivors_not_taking_every_candidate == 0 || (removing_lone_survivor && lone_survivor_allows_no_further_matches)) {
                auto voi_values = state.copy_of_values(value_of_interest);
                auto voi_single = state.optional_single_value(value_of_interest);

                // Each pruning as a range of values: the lone survivor, or one gap
                // between values of interest, which var loses; or, when fixing,
                // the fixed value of interest, which var is fixed to.
                bool fixing = voi_single && ! removing_lone_survivor;
                vector<Literal> prunings;
                vector<tuple<std::size_t, Integer, Integer>> pruned_ranges;
                for (const auto & [idx, var] : enumerate(vars)) {
                    if (state.has_single_value(var))
                        continue;
                    if (voi_single) {
                        if (! state.in_domain(var, *voi_single))
                            continue;
                        prunings.push_back(fixing ? var == *voi_single : var != *voi_single);
                        pruned_ranges.emplace_back(idx, *voi_single, *voi_single);
                    }
                    else {
                        auto var_values = state.copy_of_values(var);
                        if (! var_values.contains_all_of(voi_values))
                            continue;
                        if (removing_lone_survivor) {
                            prunings.push_back(var != lone_survivor_not_taking_every_candidate);
                            pruned_ranges.emplace_back(idx, lone_survivor_not_taking_every_candidate, lone_survivor_not_taking_every_candidate);
                        }
                        else
                            // Both sets are named locals, as each_interval_minus()
                            // borrows them (see IntervalSet's class documentation).
                            for (auto [lo, hi] : var_values.each_interval_minus(voi_values)) {
                                prunings.push_back(not_in_range(var, lo, hi));
                                pruned_ranges.emplace_back(idx, lo, hi);
                            }
                    }
                }

                if (! prunings.empty()) {
                    auto emit = [&](const ReasonLiterals & reason) -> void {
                        // infer_all runs this once, before it applies any of the
                        // prunings, so the state here is the one they were
                        // decided on. For each value of interest v, and each
                        // pruning, show that value_of_interest = v and var in
                        // the pruned range together pin the count into a range
                        // how_many cannot take, exactly as the unsupported-voi
                        // proof above does without the pruning; then the
                        // pruning itself is RUP over value_of_interest's domain.
                        auto [how_many_lo, how_many_hi] = state.bounds(how_many);
                        for (const auto & v : voi_values.each()) {
                            Integer must = 0_i, might = 0_i;
                            for (const auto & var : vars) {
                                if (auto sv = state.optional_single_value(var)) {
                                    if (*sv == v) {
                                        ++must;
                                        ++might;
                                    }
                                }
                                else if (state.in_domain(var, v))
                                    ++might;
                            }

                            // The equality flags of the variables that cannot be v
                            // are zero when value_of_interest is; wanted only when
                            // an upper bound on the count is.
                            bool zeroed_flags = false;
                            auto zero_flags_of_variables_without_v = [&]() -> void {
                                if (zeroed_flags)
                                    return;
                                zeroed_flags = true;
                                for (const auto & [idx, var] : enumerate(vars))
                                    if (! state.in_domain(var, v))
                                        logger->emit_rup_proof_line_under_reason(reason,
                                            WPBSum{} + 1_i * (value_of_interest != v) + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                            };

                            for (const auto & [idx, lo, hi] : pruned_ranges) {
                                const auto & var = vars[idx];
                                // value_of_interest != v, or the pruning holds.
                                auto unless_v_then_pruned = [&]() -> WPBSum {
                                    auto result = WPBSum{} + 1_i * (value_of_interest != v);
                                    if (fixing)
                                        result += 1_i * (var == lo);
                                    else if (lo == hi)
                                        result += 1_i * (var != lo);
                                    else {
                                        result += 1_i * (var < lo);
                                        result += 1_i * (var >= hi + 1_i);
                                    }
                                    return result;
                                };
                                // var is unfixed and can be v, so it counts towards
                                // might but not must. Where the pruning fails it is v
                                // only when it would keep the lone survivor, v.
                                bool var_is_v = removing_lone_survivor && v == lo;
                                auto count_lo = var_is_v ? must + 1_i : must;
                                auto count_hi = var_is_v ? might : might - 1_i;

                                // The fixed variables' equality flags propagate on
                                // their own, as does var's when it is pinned to v,
                                // so a count_lo above how_many needs nothing more.
                                // Anything else needs the count's upper bound, for
                                // which var's flag needs no help either: RUP zeroes
                                // it from value_of_interest = v and the failed
                                // pruning, which keeps var off v.
                                if (count_lo <= how_many_hi) {
                                    zero_flags_of_variables_without_v();
                                    // Both bounds, when the count falls in a hole of
                                    // how_many rather than off one of its ends.
                                    if (count_hi >= how_many_lo) {
                                        logger->emit_rup_proof_line_under_reason(
                                            reason, unless_v_then_pruned() + 1_i * (how_many < count_hi + 1_i) >= 1_i, ProofLevel::Temporary);
                                        logger->emit_rup_proof_line_under_reason(
                                            reason, unless_v_then_pruned() + 1_i * (how_many >= count_lo) >= 1_i, ProofLevel::Temporary);
                                    }
                                }

                                // With value_of_interest fixed, this is the pruning
                                // itself, which infer_all RUPs next.
                                if (! voi_single)
                                    logger->emit_rup_proof_line_under_reason(reason, unless_v_then_pruned() >= 1_i, ProofLevel::Temporary);
                            }
                        }
                    };
                    inference.infer_all(logger, prunings, JustifyExplicitly{emit, ThenRUP::Yes, hints::Count{owner}}, reason);
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Count::constraint_type() const -> std::string
{
    return "count";
}

auto Count::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    std::vector<SExpr> vars;
    for (const auto & v : _vars)
        vars.push_back(tracker.s_expr_term_of(v));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(vars)),
        tracker.s_expr_term_of(_value_of_interest), tracker.s_expr_term_of(_how_many)});
}
