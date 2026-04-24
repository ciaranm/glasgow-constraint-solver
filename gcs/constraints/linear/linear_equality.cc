#include <gcs/constraints/linear/linear_equality.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/exception.hh>
#include <gcs/innards/extensional_utils.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <fmt/ostream.h>

#include <functional>
#include <memory>
#include <sstream>
#include <type_traits>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::decay_t;
using std::function;
using std::is_same_v;
using std::make_pair;
using std::make_shared;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::stringstream;
using std::unique_ptr;
using std::vector;

using fmt::print;

ReifiedLinearEquality::ReifiedLinearEquality(WeightedSum coeff_vars, Integer value, ReificationCondition cond, bool gac, bool flipped_cond) :
    _coeff_vars(move(coeff_vars)),
    _value(value),
    _reif_cond(cond),
    _gac(gac),
    _flipped_cond(flipped_cond)
{
}

namespace
{
    template <typename CV_>
    auto build_table(const CV_ & coeff_vars, Integer value, ReificationCondition cond, State & state, ProofLogger * const logger) -> optional<ExtensionalData>
    {
        vector<vector<IntegerOrWildcard>> permitted;
        vector<Integer> current;

        vector<IntegerVariableID> vars;
        for (auto & cv : coeff_vars.terms) {
            auto var = get_var(cv);
            vars.push_back(var);
        }

        auto future_var_id = state.what_variable_id_will_be_created_next();

        WPBSum trail;
        function<void(ProofLogger * const)> search = [&](ProofLogger * const logger) {
            if (current.size() == coeff_vars.terms.size()) {
                Integer actual_value{0_i};
                for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
                    actual_value += get_coeff(cv) * current[idx];
                }

                bool match = overloaded{
                    [&](const reif::MustHold &) { return actual_value == value; },
                    [&](const reif::MustNotHold &) { return actual_value != value; },
                    [&](const reif::If) -> bool { throw UnimplementedException{}; },
                    [&](const reif::NotIf) -> bool { throw UnimplementedException{}; },
                    [&](const reif::Iff) -> bool { throw UnimplementedException{}; }}
                                 .visit(cond);

                if (match) {
                    permitted.emplace_back(current.begin(), current.end());
                    if (logger) {
                        Integer sel_value(permitted.size() - 1);
                        logger->names_and_ids_tracker().create_literals_for_introduced_variable_value(future_var_id, sel_value, "lineq");
                        trail += 1_i * (future_var_id == sel_value);

                        WPBSum forward_implication, reverse_implication;
                        forward_implication += Integer(coeff_vars.terms.size()) * (future_var_id != sel_value);
                        reverse_implication += 1_i * (future_var_id == sel_value);

                        for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
                            forward_implication += 1_i * (get_var(cv) == current[idx]);
                            reverse_implication += 1_i * (get_var(cv) != current[idx]);
                        }

                        logger->emit_red_proof_line(forward_implication >= Integer(coeff_vars.terms.size()),
                            {{future_var_id == sel_value, FalseLiteral{}}}, ProofLevel::Current);
                        logger->emit_red_proof_line(reverse_implication >= 1_i,
                            {{future_var_id == sel_value, TrueLiteral{}}}, ProofLevel::Current);
                    }
                }
            }
            else {
                const auto & var = get_var(coeff_vars.terms[current.size()]);
                for (auto val : state.each_value_mutable(var)) {
                    current.push_back(val);
                    search(logger);
                    current.pop_back();
                }
            }

            if (logger) {
                WPBSum backtrack = trail;
                for (const auto & [idx, val] : enumerate(current))
                    backtrack += 1_i * (get_var(coeff_vars.terms[idx]) != val);

                logger->emit_rup_proof_line(backtrack >= 1_i, ProofLevel::Current);
            }
        };

        if (logger)
            logger->emit_proof_comment("building GAC table for linear equality");
        search(logger);

        if (permitted.empty())
            return nullopt;

        auto sel = state.allocate_integer_variable_with_state(0_i, Integer(permitted.size() - 1));
        if (sel != future_var_id)
            throw UnexpectedException{"something went horribly wrong with variable IDs"};

        return ExtensionalData{sel, move(vars), move(permitted)};
    }
}

auto ReifiedLinearEquality::install(Propagators & propagators, State & state, ProofModel * const optional_model) && -> void
{
    optional<ProofLine> proof_line;
    if (optional_model) {
        WPBSum terms;
        for (auto & [c, v] : _coeff_vars.terms)
            terms += c * v;

        overloaded{
            [&](const reif::MustHold &) {
                // condition is definitely true, it's just an inequality
                proof_line = optional_model->add_constraint("ReifiedLinearEquality", "unconditional sum", terms == _value, nullopt).first.value();
            },
            [&](const reif::MustNotHold &) {
                // condition is definitely false, the flag implies either greater or less
                auto neflag = optional_model->create_proof_flag("linne");
                optional_model->add_constraint("ReifiedLinearEquality", "greater option", terms >= _value + 1_i, HalfReifyOnConjunctionOf{{neflag}});
                optional_model->add_constraint("ReifiedLinearEquality", "less than option", terms <= _value - 1_i, HalfReifyOnConjunctionOf{{! neflag}});
            },
            [&](const reif::If & cond) {
                proof_line = optional_model->add_constraint("ReifiedLinearEquality", "unconditional sum", terms == _value, HalfReifyOnConjunctionOf{{cond.cond}}).first.value();
            },
            [&](const reif::NotIf & cond) {
                // condition is definitely false, the flag implies either greater or less
                auto neflag = optional_model->create_proof_flag("linne");
                optional_model->add_constraint("ReifiedLinearEquality", "greater option", terms >= _value + 1_i, HalfReifyOnConjunctionOf{{cond.cond, neflag}});
                optional_model->add_constraint("ReifiedLinearEquality", "less than option", terms <= _value - 1_i, HalfReifyOnConjunctionOf{{cond.cond, ! neflag}});
            },
            [&](const reif::Iff & cond) {
                // condition unknown, the condition implies it is neither greater nor less
                proof_line = optional_model->add_constraint("ReifiedLinearEquality", "equals option", terms == _value, HalfReifyOnConjunctionOf{{cond.cond}}).first.value();

                auto gtflag = optional_model->create_proof_flag("lineqgt");
                optional_model->add_constraint("ReifiedLinearEquality", "greater option", terms >= _value + 1_i, HalfReifyOnConjunctionOf{{gtflag}});
                auto ltflag = optional_model->create_proof_flag("lineqlt");
                optional_model->add_constraint("ReifiedLinearEquality", "less than option", terms <= _value - 1_i, HalfReifyOnConjunctionOf{{ltflag}});

                // lt + eq + gt >= 1
                optional_model->add_constraint("ReifiedLinearEquality", "one of less than, equals, greater than", WPBSum{} + 1_i * ltflag + 1_i * gtflag + 1_i * cond.cond >= 1_i);
            }}
            .visit(_reif_cond);
    }

    auto [sanitised_cv, modifier] = tidy_up_linear(_coeff_vars);

    vector<IntegerVariableID> all_vars;
    visit([&](const auto & sanitised_cv) {
        for (const auto & cv : sanitised_cv.terms)
            all_vars.push_back(get_var(cv));
    },
        sanitised_cv);
    overloaded{
        [&](const reif::MustHold &) {},
        [&](const reif::MustNotHold &) {},
        [&](const reif::If & cond) { all_vars.push_back(cond.cond.var); },
        [&](const reif::NotIf & cond) { all_vars.push_back(cond.cond.var); },
        [&](const reif::Iff & cond) { all_vars.push_back(cond.cond.var); }}
        .visit(_reif_cond);

    if (_gac) {
        visit([&, modifier = modifier](auto & sanitised_cv) {
            // we're watching everything
            Triggers triggers;
            for (auto & cv : sanitised_cv.terms)
                triggers.on_change.push_back(get_var(cv));

            auto data = make_shared<optional<ExtensionalData>>(nullopt);
            propagators.install_initialiser([data = data, coeff_vars = sanitised_cv, value = _value + modifier, cond = _reif_cond](
                                                State & state, auto & inference, ProofLogger * const logger) {
                *data = build_table(coeff_vars, value, cond, state, logger);
                if (! data->has_value())
                    inference.infer(logger, FalseLiteral{}, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{}; }});
            });

            propagators.install([data = data](
                                    const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                if (data->has_value())
                    return propagate_extensional(data.get()->value(), state, inference, logger);
                else
                    return PropagatorState::DisableUntilBacktrack;
            },
                triggers, "lin_eq_gac");
        },
            sanitised_cv);
    }
    else {
        overloaded{
            [&](const evaluated_reif::MustHold & reif) {
                // condition is definitely true, an empty sum matches iff the modifiers sum to the value
                if (visit([](const auto & s) { return s.terms.empty(); }, sanitised_cv) && modifier != _value) {
                    propagators.install_initialiser([reason_from_cond = reif.cond](const State &, auto & inference, ProofLogger * const logger) {
                        inference.infer(logger, FalseLiteral{}, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{reason_from_cond}}; }});
                    });
                }

                // easy case: we're doing bounds consistency, and the condition is fixed
                Triggers triggers;
                for (auto & [_, v] : _coeff_vars.terms)
                    triggers.on_bounds.push_back(v);

                visit(
                    [&, modifier = modifier](const auto & lin) {
                        propagators.install([modifier = modifier, lin = lin, value = _value, proof_line = proof_line, reason_from_cond = reif.cond](
                                                const State & state, auto & inference, ProofLogger * const logger) {
                            return propagate_linear(lin, value + modifier, state, inference, logger, true, proof_line, reason_from_cond);
                        },
                            triggers, "linear equality");
                    },
                    sanitised_cv);
            },

            [&](const evaluated_reif::MustNotHold & reif) {
                // condition is definitely false on a full reification, an empty sum matches iff the modifiers sum to something other than the value
                if (visit([](const auto & s) { return s.terms.empty(); }, sanitised_cv) && modifier == _value) {
                    propagators.install_initialiser([reason_from_cond = reif.cond](const State &, auto & inference, ProofLogger * const logger) {
                        inference.infer(logger, FalseLiteral{}, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{reason_from_cond}}; }});
                    });
                }

                // strictly speaking, we care when we're down to only one variable left unassigned, and then there's one
                // value it potentially mustn't have
                Triggers triggers;
                for (auto & [_, v] : _coeff_vars.terms)
                    triggers.on_change.push_back(v);

                visit([&, modifier = modifier](const auto & sanitised_cv) {
                    propagators.install([sanitised_cv = sanitised_cv, value = _value + modifier, all_vars = move(all_vars)](
                                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                        return propagate_linear_not_equals(sanitised_cv, value, state, inference, logger, all_vars);
                    },
                        triggers, "linear nonequality");
                },
                    sanitised_cv);
            },

            [&](const evaluated_reif::Deactivated &) {
                // condition is definitely false, but on a half reification, so we do nothing
            },

            [&](const evaluated_reif::Undecided & reif) {
                // we care when the condition changes, or once we're down to a single unassigned variable
                // because that might force the condition one way or (possibly) another.
                Triggers triggers;
                for (auto & [_, v] : _coeff_vars.terms)
                    triggers.on_change.push_back(v);
                triggers.on_change.push_back(reif.cond.var);

                visit([&, modifier = modifier](const auto & sanitised_cv) {
                    propagators.install([sanitised_cv = sanitised_cv, value = _value + modifier, cond = _reif_cond, proof_line = proof_line, all_vars = move(all_vars)](
                                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                        return overloaded{
                            [&](const evaluated_reif::MustHold & reif) {
                                // we now know the condition definitely holds, so it's a linear equality
                                return propagate_linear(sanitised_cv, value, state, inference, logger, true, proof_line, reif.cond);
                            },

                            [&](const evaluated_reif::MustNotHold &) {
                                // we now know the condition definitely doesn't hold, so it's a linear not-equals
                                return propagate_linear_not_equals(sanitised_cv, value, state, inference, logger, all_vars);
                            },

                            [](const evaluated_reif::Deactivated &) {
                                return PropagatorState::DisableUntilBacktrack;
                            },

                            [&](const evaluated_reif::Undecided & reif) {
                                // we still don't know whether the condition holds. if we're down to a single unassigned
                                // variable, we might have some information.
                                auto single_unset = sanitised_cv.terms.end();
                                Integer accum = 0_i;
                                for (auto i = sanitised_cv.terms.begin(), i_end = sanitised_cv.terms.end(); i != i_end; ++i) {
                                    auto val = state.optional_single_value(get_var(*i));
                                    if (val)
                                        accum += get_coeff(*i) * *val;
                                    else {
                                        if (single_unset != sanitised_cv.terms.end()) {
                                            // at least two unset variables, do nothing for now
                                            return PropagatorState::Enable;
                                        }
                                        else
                                            single_unset = i;
                                    }
                                }

                                if (single_unset == sanitised_cv.terms.end()) {
                                    // every variable is assigned, so we know what the condition must be (if we're fully
                                    // reified)
                                    if (accum == value) {
                                        if (reif.set_cond_if_must_hold)
                                            inference.infer(logger, reif.cond, JustifyUsingRUP{}, generic_reason(state, all_vars));
                                        else if (reif.set_not_cond_if_must_hold)
                                            inference.infer(logger, ! reif.cond, JustifyUsingRUP{}, generic_reason(state, all_vars));
                                        return PropagatorState::DisableUntilBacktrack;
                                    }
                                    else {
                                        if (reif.set_not_cond_if_must_not_hold)
                                            inference.infer(logger, ! reif.cond, JustifyUsingRUP{}, generic_reason(state, all_vars));
                                        return PropagatorState::DisableUntilBacktrack;
                                    }
                                }
                                else {
                                    // exactly one thing remaining. perhaps the value that would make the equality
                                    // work doesn't occur in its domain?
                                    Integer residual = value - accum;
                                    if (0_i == residual % get_coeff(*single_unset)) {
                                        Integer would_make_equal = residual / get_coeff(*single_unset);
                                        if (! state.in_domain(get_var(*single_unset), would_make_equal)) {
                                            // no way for the remaining variable to take that value, so the condition
                                            // has to be false
                                            if (reif.set_not_cond_if_must_not_hold)
                                                inference.infer(logger, ! reif.cond, JustifyUsingRUP{}, generic_reason(state, all_vars));
                                            return PropagatorState::DisableUntilBacktrack;
                                        }
                                        else {
                                            // could go either way, but this might change as more values are lost
                                            return PropagatorState::Enable;
                                        }
                                    }
                                    else {
                                        // the value that would make the equality work isn't an integer, so the condition
                                        // has to be false
                                        if (reif.set_not_cond_if_must_not_hold)
                                            inference.infer(logger, ! reif.cond, JustifyUsingRUP{}, generic_reason(state, all_vars));
                                        return PropagatorState::DisableUntilBacktrack;
                                    }
                                }
                            }}
                            .visit(state.test_reification_condition(cond));
                    },
                        triggers, "linear");
                },
                    sanitised_cv);
            }}
            .visit(state.test_reification_condition(_reif_cond));
    }
}

auto ReifiedLinearEquality::s_exprify(const std::string & name, const ProofModel * const model) const -> std::string
{
    stringstream s;

    auto [rei, cons] = overloaded{
        [&](const reif::MustHold &) { return make_pair(false, "lin_equals"); },
        [&](const reif::If &) { return make_pair(true, "lin_equals_if"); },
        [&](const reif::Iff &) { return make_pair(true, _flipped_cond ? "lin_not_equals_iff" : "lin_equals_iff"); },
        [&](const reif::MustNotHold &) { return make_pair(false, "lin_not_equals"); },
        [&](const reif::NotIf &) { return make_pair(true, "lin_not_equals_if"); }}
                           .visit(_reif_cond);

    print(s, "{} {}", name, cons);
    if (rei) {
        print(s, " {} ", model->names_and_ids_tracker().s_expr_name_of(_reif_cond));
    }
    print(s, " (");
    for (const auto & [c, v] : _coeff_vars.terms) {
        print(s, " {} {}", c.raw_value, model->names_and_ids_tracker().s_expr_name_of(v));
    }
    print(s, ") {}", _value.raw_value);

    return s.str();
}

auto ReifiedLinearEquality::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ReifiedLinearEquality>(WeightedSum{_coeff_vars}, _value, _reif_cond, _gac, _flipped_cond);
}

LinearEquality::LinearEquality(WeightedSum coeff_vars, Integer value, bool gac) :
    ReifiedLinearEquality(coeff_vars, value, reif::MustHold{}, gac)
{
}

namespace
{
    template <typename T_>
    auto literal_to_reif(const Literal & cond) -> ReificationCondition
    {
        return overloaded{
            [&](const TrueLiteral &) -> ReificationCondition { return reif::MustHold{}; },
            [&](const FalseLiteral &) -> ReificationCondition { return reif::MustNotHold{}; },
            [&](const IntegerVariableCondition & cond) -> ReificationCondition { return T_{cond}; }}
            .visit(cond);
    }
}

LinearEqualityIf::LinearEqualityIf(WeightedSum coeff_vars, Integer value, Literal cond, bool gac) :
    ReifiedLinearEquality(move(coeff_vars), value, literal_to_reif<reif::If>(cond), gac)
{
}

LinearEqualityIff::LinearEqualityIff(WeightedSum coeff_vars, Integer value, Literal cond, bool gac) :
    ReifiedLinearEquality(move(coeff_vars), value, literal_to_reif<reif::Iff>(cond), gac)
{
}

LinearNotEquals::LinearNotEquals(WeightedSum coeff_vars, Integer value, bool gac) :
    ReifiedLinearEquality(move(coeff_vars), value, reif::MustNotHold{}, gac)
{
}

LinearNotEqualsIf::LinearNotEqualsIf(WeightedSum coeff_vars, Integer value, Literal cond, bool gac) :
    ReifiedLinearEquality(move(coeff_vars), value, literal_to_reif<reif::NotIf>(cond), gac)
{
}

LinearNotEqualsIff::LinearNotEqualsIff(WeightedSum coeff_vars, Integer value, Literal cond, bool gac) :
    ReifiedLinearEquality(move(coeff_vars), value, literal_to_reif<reif::Iff>(! cond), gac, true)
{
}
