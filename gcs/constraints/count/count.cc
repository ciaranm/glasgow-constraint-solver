#include <gcs/constraints/count/count.hh>
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
    _vars(move(vars)),
    _value_of_interest(value_of_interest),
    _how_many(how_many)
{
}

auto Count::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Count>(_vars, _value_of_interest, _how_many);
}

auto Count::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Count::define_proof_model(ProofModel & model) -> void
{
    // Conform to cake_pb_cp's count encoding (#354): per position i, the
    // flags x[id][i][ge] ⇔ var ≥ val, x[id][i][le] ⇔ var ≤ val, and
    // x[id][i][eq] ⇔ (ge ∧ le) ⇔ var = val. (The solver previously used
    // strict gt/lt and eq ⇔ ¬gt ∧ ¬lt; the equality flag means the same
    // thing — var = val — which is all the propagator references.)
    for (const auto & [i, var] : enumerate(_vars)) {
        vector<long long> pos{static_cast<long long>(i)};

        auto ge = model.create_proof_flag_fully_reifying(_constraint_id, pos, "ge",
            WPBSum{} + 1_i * var + -1_i * _value_of_interest >= 0_i);

        auto le = model.create_proof_flag_fully_reifying(_constraint_id, pos, "le",
            WPBSum{} + 1_i * var + -1_i * _value_of_interest <= 0_i);

        auto eq = model.create_proof_flag_fully_reifying(_constraint_id, pos, "eq",
            WPBSum{} + 1_i * ge + 1_i * le >= 2_i);

        _flags.emplace_back(eq, ge, le);
    }

    // sum of equal flags == how_many, as cake's c[id][le] / c[id][ge] halves
    WPBSum how_many_sum;
    for (auto & [eq, _1, _2] : _flags)
        how_many_sum += 1_i * eq;
    how_many_sum += -1_i * _how_many;

    model.add_labelled_constraint(as_string(_constraint_id), "le", "ge",
        "Count", "sum of flags", how_many_sum == 0_i);
}

auto Count::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());
    triggers.on_change.emplace_back(_value_of_interest);
    triggers.on_bounds.emplace_back(_how_many);

    vector<IntegerVariableID> all_vars = _vars;
    all_vars.push_back(_value_of_interest);
    all_vars.push_back(_how_many);

    propagators.install(
        constraint_id(),
        [vars = _vars, value_of_interest = _value_of_interest, how_many = _how_many, flags = _flags, all_vars = move(all_vars)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
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
                            logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * (value_of_interest != val) + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                        logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                    }
                }
            };
            inference.infer(logger, how_many < how_many_is_less_than,
                JustifyExplicitly{justf, ThenRUP::Yes},
                generic_reason(state, all_vars));

            // must have at least this many occurrences of the value of interest
            int how_many_must = 0;
            auto voi = state.optional_single_value(value_of_interest);
            if (voi) {
                for (auto & v : vars)
                    if (state.optional_single_value(v) == voi)
                        ++how_many_must;
            }
            inference.infer(logger, how_many >= Integer(how_many_must), JustifyUsingRUP{}, generic_reason(state, all_vars));

            // is each value of interest supported? also track how_many bounds supports
            // whilst we're here
            optional<Integer> lowest_how_many_must, highest_how_many_might;
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
                                    WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (var != voi) + 1_i * (get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                                logger->emit_rup_proof_line_under_reason(reason,
                                    WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                            }
                        }
                    };
                    inference.infer(logger, value_of_interest != voi, JustifyExplicitly{justf, ThenRUP::Yes}, generic_reason(state, all_vars));
                }
                else if (how_many_must > state.upper_bound(how_many)) {
                    // unlike above, we don't need to help, because the equality flag will propagate
                    // from the fixed assignment
                    inference.infer(logger, value_of_interest != voi, JustifyUsingRUP{}, generic_reason(state, all_vars));
                }
                else {
                    if ((! lowest_how_many_must) || (how_many_must < *lowest_how_many_must))
                        lowest_how_many_must = how_many_must;
                    if ((! highest_how_many_might) || (how_many_might > *highest_how_many_might))
                        highest_how_many_might = how_many_might;
                }
            }

            // what are the supports on possible values we've seen?
            if (lowest_how_many_must) {
                auto just = JustifyExplicitly{[&](const ReasonLiterals & reason) -> void {
                                                  for (const auto & voi : state.each_value_immutable(value_of_interest))
                                                      logger->emit_rup_proof_line_under_reason(reason,
                                                          WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (how_many >= *lowest_how_many_must) >= 1_i,
                                                          ProofLevel::Temporary);
                                              },
                    ThenRUP::Yes};
                inference.infer(logger, how_many >= *lowest_how_many_must, just, generic_reason(state, all_vars));
            }

            if (highest_how_many_might) {
                auto just = JustifyExplicitly{[&](const ReasonLiterals & reason) -> void {
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
                                                              logger->emit_rup_proof_line_under_reason(reason,
                                                                  WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (! get<0>(flags[idx])) >= 1_i,
                                                                  ProofLevel::Temporary);
                                                              logger->emit_rup_proof_line_under_reason(reason,
                                                                  WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (var != voi) >= 1_i,
                                                                  ProofLevel::Temporary);
                                                          }
                                                  }

                                                  // Per-voi unconditional lines: emit after all the
                                                  // conditionals so they have the full set of pairwise
                                                  // facts to RUP-derive against.
                                                  for (const auto & voi : voi_set.each())
                                                      logger->emit_rup_proof_line_under_reason(reason,
                                                          WPBSum{} + 1_i * (value_of_interest != voi) + 1_i * (how_many < *highest_how_many_might + 1_i) >= 1_i,
                                                          ProofLevel::Temporary);
                                              },
                    ThenRUP::Yes};
                inference.infer(logger, how_many < *highest_how_many_might + 1_i, just, generic_reason(state, all_vars));
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Count::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    std::vector<SExpr> vars;
    for (const auto & v : _vars)
        vars.push_back(tracker.s_expr_term_of(v));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("count"),
        SExpr::list(std::move(vars)),
        tracker.s_expr_term_of(_value_of_interest),
        tracker.s_expr_term_of(_how_many)});
}
