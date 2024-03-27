#include <gcs/constraints/linear/linear_equality.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/exception.hh>
#include <gcs/innards/extensional_utils.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <functional>
#include <memory>
#include <sstream>
#include <type_traits>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::function;
using std::is_same_v;
using std::make_shared;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::stringstream;
using std::unique_ptr;
using std::vector;

LinearEqualityIff::LinearEqualityIff(WeightedSum coeff_vars, Integer value, Literal cond, bool gac) :
    _coeff_vars(move(coeff_vars)),
    _value(value),
    _cond(cond),
    _gac(gac)
{
}

auto LinearEqualityIff::clone() const -> unique_ptr<Constraint>
{
    return make_unique<LinearEqualityIff>(WeightedSum{_coeff_vars}, _value, _cond, _gac);
}

namespace
{
    auto to_coeff(Integer v)
    {
        return v;
    }

    auto get_var(const PositiveOrNegative<SimpleIntegerVariableID> & cv) -> SimpleIntegerVariableID
    {
        return cv.variable;
    }

    auto get_var(const Weighted<SimpleIntegerVariableID> & cv) -> SimpleIntegerVariableID
    {
        return cv.variable;
    }

    auto get_var(const SimpleIntegerVariableID & cv) -> SimpleIntegerVariableID
    {
        return cv;
    }

    auto get_coeff(const PositiveOrNegative<SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.positive ? 1_i : -1_i;
    }

    auto get_coeff(const Weighted<SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.coefficient;
    }

    auto get_coeff(const SimpleIntegerVariableID &) -> Integer
    {
        return 1_i;
    }

    template <typename CV_>
    auto build_table(const CV_ & coeff_vars, Integer value, State & state, ProofLogger * const logger) -> ExtensionalData
    {
        vector<vector<Integer>> permitted;
        vector<Integer> current;

        vector<IntegerVariableID> vars;
        for (auto & cv : coeff_vars.terms) {
            auto var = get_var(cv);
            vars.push_back(var);
        }

        auto future_var_id = state.what_variable_id_will_be_created_next();

        WeightedPseudoBooleanSum trail;
        function<void(ProofLogger * const)> search = [&](ProofLogger * const logger) {
            if (current.size() == coeff_vars.terms.size()) {
                Integer actual_value{0_i};
                for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
                    auto coeff = get_coeff(cv);
                    actual_value += to_coeff(coeff) * current[idx];
                }
                if (actual_value == value) {
                    permitted.push_back(current);
                    if (logger) {
                        Integer sel_value(permitted.size() - 1);
                        logger->variable_constraints_tracker().create_literals_for_introduced_variable_value(future_var_id, sel_value, "lineq");
                        trail += 1_i * (future_var_id == sel_value);

                        WeightedPseudoBooleanSum forward_implication, reverse_implication;
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
                state.for_each_value(var, [&](Integer val) {
                    current.push_back(val);
                    search(logger);
                    current.pop_back();
                });
            }

            if (logger) {
                WeightedPseudoBooleanSum backtrack = trail;
                for (const auto & [idx, val] : enumerate(current))
                    backtrack += 1_i * (get_var(coeff_vars.terms[idx]) != val);

                logger->emit_rup_proof_line(backtrack >= 1_i, ProofLevel::Current);
            }
        };

        if (logger)
            logger->emit_proof_comment("building GAC table for linear equality");
        search(logger);

        auto sel = state.allocate_integer_variable_with_state(0_i, Integer(permitted.size() - 1));
        if (sel != future_var_id)
            throw UnexpectedException{"something went horribly wrong with variable IDs"};

        return ExtensionalData{sel, move(vars), move(permitted)};
    }
}

auto LinearEqualityIff::install(Propagators & propagators, State & state, ProofModel * const optional_model) && -> void
{
    optional<ProofLine> proof_line;
    optional<ProofFlag> gtflag, ltflag, eqflag;
    if (optional_model) {
        WeightedPseudoBooleanSum terms;
        for (auto & [c, v] : _coeff_vars.terms)
            terms += c * v;

        overloaded{
            [&](const TrueLiteral &) {
                proof_line = optional_model->add_constraint(terms == _value, nullopt).first.value();
            },
            [&](const FalseLiteral &) {
                auto neflag = optional_model->create_proof_flag("linne");
                optional_model->add_constraint(terms >= _value + 1_i, HalfReifyOnConjunctionOf{{neflag}});
                optional_model->add_constraint(terms <= _value - 1_i, HalfReifyOnConjunctionOf{{! neflag}});
            },
            [&](const IntegerVariableCondition & cond) {
                eqflag = optional_model->create_proof_flag("lineq");
                proof_line = optional_model->add_constraint(terms == _value, HalfReifyOnConjunctionOf{{*eqflag}}).first.value();

                gtflag = optional_model->create_proof_flag("lineqgt");
                optional_model->add_constraint(terms >= _value + 1_i, HalfReifyOnConjunctionOf{{*gtflag}});
                ltflag = optional_model->create_proof_flag("lineqlt");
                optional_model->add_constraint(terms <= _value - 1_i, HalfReifyOnConjunctionOf{{*ltflag}});

                // eq -> ! gt and ! lt
                optional_model->add_constraint(WeightedPseudoBooleanSum{} + 2_i * ! *eqflag + 1_i * ! *gtflag + 1_i * ! *ltflag >= 2_i);
                // gt -> ! eq and ! lt
                optional_model->add_constraint(WeightedPseudoBooleanSum{} + 2_i * ! *gtflag + 1_i * ! *eqflag + 1_i * ! *ltflag >= 2_i);
                // lt -> ! eq and ! gt
                optional_model->add_constraint(WeightedPseudoBooleanSum{} + 2_i * ! *ltflag + 1_i * ! *gtflag + 1_i * ! *eqflag >= 2_i);
                // lt \/ eq \/ gt
                optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * *ltflag + 1_i * *gtflag + 1_i * *eqflag >= 1_i);
                // cond -> eq
                optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! cond + 1_i * *eqflag >= 1_i);
                // ! cond -> ! eq
                optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * cond + 1_i * ! *eqflag >= 1_i);
            }}
            .visit(_cond);
    }

    auto [sanitised_cv, modifier] = tidy_up_linear(_coeff_vars);

    vector<IntegerVariableID> all_vars;
    visit([&](const auto & sanitised_cv) {
        for (const auto & cv : sanitised_cv.terms)
            all_vars.push_back(get_var(cv));
    },
        sanitised_cv);
    overloaded{
        [&](const TrueLiteral &) {},
        [&](const FalseLiteral &) {},
        [&](const IntegerVariableCondition & cond) { all_vars.push_back(cond.var); }}
        .visit(_cond);

    switch (state.test_literal(_cond)) {
    case LiteralIs::DefinitelyTrue: {
        if (visit([](const auto & s) { return s.terms.empty(); }, sanitised_cv) && modifier != _value) {
            propagators.install_initialiser([cond = _cond](State & state, ProofLogger * const logger) -> Inference {
                return state.infer(logger, FalseLiteral{}, JustifyUsingRUP{Literals{cond}});
            });
        }

        Triggers triggers;
        for (auto & [_, v] : _coeff_vars.terms)
            triggers.on_bounds.push_back(v);

        overloaded{
            [&, modifier = modifier](const SumOf<Weighted<SimpleIntegerVariableID>> & lin) {
                propagators.install([modifier = modifier, lin = lin, value = _value, proof_line = proof_line, cond = _cond](
                                        State & state, ProofLogger * const logger) {
                    return propagate_linear(lin, value + modifier, state, logger, true, proof_line, cond);
                },
                    triggers, "linear equality");
            },
            [&, modifier = modifier](const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & sum) {
                propagators.install([modifier = modifier, sum = sum, value = _value, proof_line = proof_line, cond = _cond](
                                        State & state, ProofLogger * const logger) {
                    return propagate_sum(sum, value + modifier, state, logger, true, proof_line, cond);
                },
                    triggers, "linear equality");
            },
            [&, modifier = modifier](const SumOf<SimpleIntegerVariableID> & sum) {
                propagators.install([modifier = modifier, sum = sum, value = _value, proof_line = proof_line, cond = _cond](
                                        State & state, ProofLogger * const logger) {
                    return propagate_sum_all_positive(sum, value + modifier, state, logger, true, proof_line, cond);
                },
                    triggers, "linear equality");
            }}
            .visit(sanitised_cv);

        if (_gac) {
            visit([&, modifier = modifier](auto & sanitised_cv) {
                Triggers triggers;
                for (auto & cv : sanitised_cv.terms)
                    triggers.on_change.push_back(get_var(cv));

                auto data = make_shared<optional<ExtensionalData>>(nullopt);
                propagators.install_initialiser([data = data, coeff_vars = sanitised_cv, value = _value + modifier](State & state,
                                                    ProofLogger * const logger) {
                    *data = build_table(coeff_vars, value, state, logger);
                    return Inference::NoChange;
                });
                propagators.install([data = data](State & state, ProofLogger * const logger) -> pair<Inference, PropagatorState> {
                    return propagate_extensional(data.get()->value(), state, logger);
                },
                    triggers, "lin_eq_gac");
            },
                sanitised_cv);
        }
    } break;

    case LiteralIs::DefinitelyFalse: {
        if (visit([](const auto & s) { return s.terms.empty(); }, sanitised_cv) && modifier == _value) {
            propagators.install_initialiser([cond = _cond](State & state, ProofLogger * const logger) -> Inference {
                return state.infer(logger, FalseLiteral{}, JustifyUsingRUP{Literals{cond}});
            });
        }

        Triggers triggers;
        for (auto & [_, v] : _coeff_vars.terms)
            triggers.on_change.push_back(v);

        return visit([&](const auto & sanitised_cv) {
            propagators.install([sanitised_cv = sanitised_cv, value = _value + modifier, cond = _cond, all_vars = move(all_vars)](
                                    State & state, ProofLogger * const logger) -> pair<Inference, PropagatorState> {
                auto single_unset = sanitised_cv.terms.end();
                Integer accum = 0_i;
                for (auto i = sanitised_cv.terms.begin(), i_end = sanitised_cv.terms.end(); i != i_end; ++i) {
                    auto val = state.optional_single_value(get_var(*i));
                    if (val)
                        accum += get_coeff(*i) * *val;
                    else {
                        if (single_unset != sanitised_cv.terms.end()) {
                            // at least two unset variables, do nothing for now
                            return pair{Inference::NoChange, PropagatorState::Enable};
                        }
                        else
                            single_unset = i;
                    }
                }

                if (single_unset == sanitised_cv.terms.end()) {
                    // everything set, do a sanity check
                    if (accum == value) {
                        state.infer_false(logger, JustifyUsingRUP{generic_reason(state, all_vars)});
                        return pair{Inference::Contradiction, PropagatorState::Enable};
                    }
                    else
                        return pair{Inference::NoChange, PropagatorState::DisableUntilBacktrack};
                }
                else {
                    // exactly one thing remaining
                    Integer residual = value - accum;
                    if (0_i == residual % get_coeff(*single_unset)) {
                        Integer forbidden = residual / get_coeff(*single_unset);
                        if (state.in_domain(get_var(*single_unset), forbidden)) {
                            return pair{state.infer(logger, get_var(*single_unset) != forbidden, JustifyUsingRUP{generic_reason(state, all_vars)}),
                                PropagatorState::DisableUntilBacktrack};
                        }
                        else
                            return pair{Inference::NoChange, PropagatorState::DisableUntilBacktrack};
                    }
                    else
                        return pair{Inference::NoChange, PropagatorState::Enable};
                }
            },
                triggers, "linear nonequality");
        },
            sanitised_cv);
    } break;

    case LiteralIs::Undecided: {
        if (visit([modifier = modifier, value = _value, cond = _cond](const auto & s) { return s.terms.empty(); }, sanitised_cv)) {
            if (modifier == _value) {
                propagators.install_initialiser([cond = _cond](State & state, ProofLogger * const logger) -> Inference {
                    return state.infer(logger, cond, NoJustificationNeeded{});
                });
            }
            else {
                propagators.install_initialiser([cond = _cond](State & state, ProofLogger * const logger) -> Inference {
                    return state.infer(logger, ! cond, NoJustificationNeeded{});
                });
            }
        }

        Triggers triggers;
        for (auto & [_, v] : _coeff_vars.terms)
            triggers.on_change.push_back(v);
        overloaded{
            [&](const TrueLiteral &) {},
            [&](const FalseLiteral &) {},
            [&](const IntegerVariableCondition & cond) { triggers.on_change.push_back(cond.var); }}
            .visit(_cond);

        visit([&](const auto & sanitised_cv) {
            propagators.install([sanitised_cv = sanitised_cv, value = _value + modifier, cond = _cond, proof_line = proof_line,
                                    all_vars = move(all_vars), eqflag = eqflag, ltflag = ltflag, gtflag = gtflag](
                                    State & state, ProofLogger * const logger) -> pair<Inference, PropagatorState> {
                switch (state.test_literal(cond)) {
                case LiteralIs::Undecided: {
                    return pair{Inference::NoChange, PropagatorState::Enable};
                    auto single_unset = sanitised_cv.terms.end();
                    Integer accum = 0_i;
                    for (auto i = sanitised_cv.terms.begin(), i_end = sanitised_cv.terms.end(); i != i_end; ++i) {
                        auto val = state.optional_single_value(get_var(*i));
                        if (val)
                            accum += get_coeff(*i) * *val;
                        else {
                            if (single_unset != sanitised_cv.terms.end()) {
                                // at least two unset variables, do nothing for now
                                return pair{Inference::NoChange, PropagatorState::Enable};
                            }
                            else
                                single_unset = i;
                        }
                    }

                    if (single_unset == sanitised_cv.terms.end()) {
                        // everything set, the condition is forced
                        if (accum == value) {
                            return pair{state.infer(logger, cond, JustifyUsingRUP{generic_reason(state, all_vars)}),
                                PropagatorState::DisableUntilBacktrack};
                        }
                        else {
                            return pair{state.infer(logger, ! cond, JustifyUsingRUP{generic_reason(state, all_vars)}),
                                PropagatorState::DisableUntilBacktrack};
                        }
                    }
                    else {
                        // exactly one thing remaining
                        Integer residual = value - accum;
                        if (0_i == residual % get_coeff(*single_unset)) {
                            Integer would_make_equal = residual / get_coeff(*single_unset);
                            if (! state.in_domain(get_var(*single_unset), would_make_equal)) {
                                return pair{state.infer(logger, ! cond, NoJustificationNeeded{}), PropagatorState::DisableUntilBacktrack};
                            }
                            else
                                return pair{Inference::NoChange, PropagatorState::DisableUntilBacktrack};
                        }
                        else
                            return pair{state.infer(logger, ! cond, NoJustificationNeeded{}), PropagatorState::DisableUntilBacktrack};
                    }
                } break;

                case LiteralIs::DefinitelyTrue: {
                    if constexpr (is_same_v<decltype(sanitised_cv), const SumOf<Weighted<SimpleIntegerVariableID>>>) {
                        return propagate_linear(sanitised_cv, value, state, logger, true, proof_line, cond);
                    }
                    else if constexpr (is_same_v<decltype(sanitised_cv), const SumOf<PositiveOrNegative<SimpleIntegerVariableID>>>) {
                        return propagate_sum(sanitised_cv, value, state, logger, true, proof_line, cond);
                    }
                    else if constexpr (is_same_v<decltype(sanitised_cv), const SumOf<SimpleIntegerVariableID>>) {
                        return propagate_sum_all_positive(sanitised_cv, value, state, logger, true, proof_line, cond);
                    }
                    else
                        static_assert(false, "missing type");
                } break;

                case LiteralIs::DefinitelyFalse: {
                    auto single_unset = sanitised_cv.terms.end();
                    Integer accum = 0_i;
                    for (auto i = sanitised_cv.terms.begin(), i_end = sanitised_cv.terms.end(); i != i_end; ++i) {
                        auto val = state.optional_single_value(get_var(*i));
                        if (val)
                            accum += get_coeff(*i) * *val;
                        else {
                            if (single_unset != sanitised_cv.terms.end()) {
                                // at least two unset variables, do nothing for now
                                return pair{Inference::NoChange, PropagatorState::Enable};
                            }
                            else
                                single_unset = i;
                        }
                    }

                    if (single_unset == sanitised_cv.terms.end()) {
                        // everything set, do a sanity check
                        if (accum == value) {
                            // cond is viewed as false, but needs to be true, this will contradict
                            auto reason = generic_reason(state, all_vars);
                            auto just = [&]() {
                                logger->emit_rup_proof_line_under_reason(state, reason,
                                    WeightedPseudoBooleanSum{} + 1_i * ! *gtflag >= 1_i, ProofLevel::Temporary);
                                logger->emit_rup_proof_line_under_reason(state, reason,
                                    WeightedPseudoBooleanSum{} + 1_i * ! *ltflag >= 1_i, ProofLevel::Temporary);
                            };
                            return pair{state.infer(logger, cond, JustifyExplicitly{just, reason}), PropagatorState::Enable};
                        }
                        else
                            return pair{Inference::NoChange, PropagatorState::DisableUntilBacktrack};
                    }
                    else {
                        // exactly one thing remaining
                        Integer residual = value - accum;
                        if (0_i == residual % get_coeff(*single_unset)) {
                            Integer forbidden = residual / get_coeff(*single_unset);
                            if (state.in_domain(get_var(*single_unset), forbidden)) {
                                vector<IntegerVariableID> vars;
                                for (const auto & cv : sanitised_cv.terms)
                                    vars.push_back(get_var(cv));
                                overloaded{
                                    [&](const TrueLiteral &) {},
                                    [&](const FalseLiteral &) {},
                                    [&](const IntegerVariableCondition & cond) { vars.push_back(cond.var); }}
                                    .visit(cond);

                                auto reason = generic_reason(state, all_vars);
                                auto just = [&]() {
                                    logger->emit_rup_proof_line_under_reason(state, reason, WeightedPseudoBooleanSum{} + 1_i * (get_var(*single_unset) != forbidden) + 1_i * ! *gtflag >= 1_i,
                                        ProofLevel::Temporary);
                                    logger->emit_rup_proof_line_under_reason(state, reason, WeightedPseudoBooleanSum{} + 1_i * (get_var(*single_unset) != forbidden) + 1_i * ! *ltflag >= 1_i,
                                        ProofLevel::Temporary);
                                };
                                return pair{state.infer(logger, get_var(*single_unset) != forbidden, JustifyExplicitly{just, reason}),
                                    PropagatorState::DisableUntilBacktrack};
                            }
                            else
                                return pair{Inference::NoChange, PropagatorState::DisableUntilBacktrack};
                        }
                        else
                            return pair{Inference::NoChange, PropagatorState::Enable};
                    }
                } break;
                }

                throw NonExhaustiveSwitch{};
            },
                triggers, "linear");
        },
            sanitised_cv);
    } break;
    }
}

auto LinearEqualityIff::describe_for_proof() -> std::string
{
    return "linear equality";
}

LinearEquality::LinearEquality(WeightedSum coeff_vars, Integer value, bool gac) :
    LinearEqualityIff(coeff_vars, value, TrueLiteral{}, gac)
{
}

LinearNotEquals::LinearNotEquals(WeightedSum coeff_vars, Integer value, bool gac) :
    LinearEqualityIff(coeff_vars, value, FalseLiteral{}, gac)
{
}
