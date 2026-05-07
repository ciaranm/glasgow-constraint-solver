#include <gcs/constraints/in.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <algorithm>
#include <optional>
#include <sstream>
#include <string>
#include <utility>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::erase_if;
using std::make_unique;
using std::move;
using std::optional;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;
using std::ranges::any_of;
using std::ranges::binary_search;
using std::ranges::sort;
using std::ranges::unique;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

In::In(IntegerVariableID var, vector<IntegerVariableID> vars, vector<Integer> vals) :
    _var(var),
    _var_vals(move(vars)),
    _val_vals(move(vals))
{
}

In::In(IntegerVariableID var, vector<IntegerVariableID> vals) :
    _var(var),
    _var_vals(move(vals))
{
}

In::In(IntegerVariableID var, vector<Integer> vals) :
    _var(var),
    _val_vals(move(vals))
{
}

auto In::clone() const -> unique_ptr<Constraint>
{
    return make_unique<In>(_var, _var_vals, _val_vals);
}

auto In::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto In::prepare(Propagators & propagators, State & initial_state, ProofModel * const optional_model) -> bool
{
    erase_if(_var_vals, [&](const IntegerVariableID & v) -> bool {
        auto const_val = initial_state.optional_single_value(v);
        if (const_val)
            _val_vals.push_back(*const_val);
        return const_val.has_value();
    });

    sort(_val_vals);
    _val_vals.erase(unique(_val_vals).begin(), _val_vals.end());

    if (_var_vals.empty() && _val_vals.empty()) {
        propagators.model_contradiction(initial_state, optional_model,
            "No values or variables present for an 'In' constraint");
        return false;
    }

    return true;
}

auto In::define_proof_model(ProofModel & model) -> void
{
    WPBSum sum;

    for (const auto & v : _val_vals)
        if (! is_literally_false(_var == v))
            sum += 1_i * (_var == v);

    // For each non-constant V_i, fully reify three flags:
    //   lt_i ⇔ var < V_i
    //   gt_i ⇔ var > V_i
    //   sel_i ⇔ ¬lt_i ∧ ¬gt_i  (i.e. sel_i ⇔ var = V_i)
    // Mirrors the encoding used by Count. Full reification of every
    // proof flag is the project rule for new OPB encodings.
    for (const auto & [idx, V] : enumerate(_var_vals)) {
        auto lt = model.create_proof_flag(format("inlt{}", idx));
        auto gt = model.create_proof_flag(format("ingt{}", idx));
        auto sel = model.create_proof_flag(format("in{}", idx));
        _selectors.push_back(sel);

        // gt ⇔ var > V_i
        model.add_constraint("In", "var greater than",
            WPBSum{} + 1_i * _var + -1_i * V >= 1_i, {{gt}});
        model.add_constraint("In", "var not greater than",
            WPBSum{} + 1_i * _var + -1_i * V <= 0_i, {{! gt}});

        // lt ⇔ var < V_i
        model.add_constraint("In", "var less than",
            WPBSum{} + 1_i * _var + -1_i * V <= -1_i, {{lt}});
        model.add_constraint("In", "var not less than",
            WPBSum{} + 1_i * _var + -1_i * V >= 0_i, {{! lt}});

        // sel ⇔ ¬lt ∧ ¬gt
        model.add_constraint("In", "selector implies var equals",
            WPBSum{} + 1_i * ! lt + 1_i * ! gt >= 2_i, {{sel}});
        model.add_constraint("In", "var unequal implies not selector",
            WPBSum{} + 1_i * lt + 1_i * gt >= 1_i, {{! sel}});

        sum += 1_i * sel;
    }

    model.add_constraint("In", "var is one of these", sum >= 1_i);
}

auto In::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change.emplace_back(_var);
    for (const auto & V : _var_vals)
        triggers.on_change.emplace_back(V);

    propagators.install(
        [var = _var, var_vals = _var_vals, val_vals = _val_vals, selectors = _selectors](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Step 1: filter dom(var) — drop any value that no source supports.
            for (auto v : state.each_value_mutable(var)) {
                if (binary_search(val_vals, v))
                    continue;

                bool supported_by_var = false;
                for (const auto & V : var_vals) {
                    if (state.in_domain(V, v)) {
                        supported_by_var = true;
                        break;
                    }
                }
                if (supported_by_var)
                    continue;

                Reason reason;
                for (const auto & V : var_vals)
                    reason.emplace_back(V != v);

                if (selectors.empty()) {
                    inference.infer_not_equal(logger, var, v, JustifyUsingRUP{},
                        ReasonFunction{[=]() { return reason; }});
                }
                else {
                    inference.infer_not_equal(logger, var, v,
                        JustifyExplicitlyThenRUP{[logger, var, v, &selectors](const ReasonFunction & reason) {
                            for (const auto & sel : selectors)
                                logger->emit_rup_proof_line_under_reason(reason,
                                    WPBSum{} + 1_i * ! sel + 1_i * (var != v) >= 1_i,
                                    ProofLevel::Temporary);
                        }},
                        ReasonFunction{[=]() { return reason; }});
                }
            }

            // Step 2: identify which V_i's still have any value in dom(var).
            optional<size_t> support_1, support_2;
            for (const auto & [i, V] : enumerate(var_vals)) {
                bool overlaps = any_of(state.each_value_immutable(V),
                    [&](Integer w) { return state.in_domain(var, w); });
                if (overlaps) {
                    if (! support_1)
                        support_1 = i;
                    else {
                        support_2 = i;
                        break;
                    }
                }
            }

            // Does any constant in val_vals lie in dom(var)?
            bool const_supports = any_of(val_vals,
                [&](Integer c) { return state.in_domain(var, c); });

            // Step 3: if no constant supports and exactly one V_i supports, that V_i must
            // equal var, so prune V_i to dom(var).
            if (! const_supports && support_1 && ! support_2) {
                size_t i = *support_1;
                const auto & V = var_vals[i];

                for (auto val : state.each_value_mutable(V)) {
                    if (state.in_domain(var, val))
                        continue;

                    Reason reason = generic_reason(state, vector{var})();
                    for (const auto & [j, V_j] : enumerate(var_vals)) {
                        if (j == i)
                            continue;
                        for (const auto & w : state.each_value_immutable(var))
                            reason.emplace_back(V_j != w);
                    }

                    inference.infer_not_equal(logger, V, val,
                        JustifyExplicitlyThenRUP{[logger, &state, &var_vals, &selectors, var, i](const ReasonFunction & reason) {
                            // When var is fixed, dom(var) is a single value and the inner-loop
                            // scaffolding line `! sel_j + (var != w)` collapses (under the reason's
                            // `var = w` literal) to the same constraint as the outer `! sel_j`, so
                            // skip the inner loop entirely.
                            bool var_fixed = state.has_single_value(var);
                            for (const auto & [j, V_j] : enumerate(var_vals)) {
                                if (j == i)
                                    continue;
                                if (! var_fixed)
                                    for (const auto & w : state.each_value_immutable(var))
                                        logger->emit_rup_proof_line_under_reason(reason,
                                            WPBSum{} + 1_i * ! selectors[j] + 1_i * (var != w) >= 1_i,
                                            ProofLevel::Temporary);
                                logger->emit_rup_proof_line_under_reason(reason,
                                    WPBSum{} + 1_i * ! selectors[j] >= 1_i,
                                    ProofLevel::Temporary);
                            }
                        }},
                        ReasonFunction{[=]() { return reason; }});
                }
            }

            // If var is fixed to a constant we know is in val_vals, no further propagation
            // can possibly fire usefully.
            auto fixed = state.optional_single_value(var);
            if (fixed && binary_search(val_vals, *fixed))
                return PropagatorState::DisableUntilBacktrack;

            return PropagatorState::Enable;
        },
        triggers);
}

auto In::s_exprify(const string & name, const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} in {} (", name, model->names_and_ids_tracker().s_expr_name_of(_var));
    for (const auto & v : _var_vals)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    for (const auto & v : _val_vals)
        print(s, " {}", v);
    print(s, ")");

    return s.str();
}
