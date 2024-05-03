#include <gcs/constraints/equals.hh>
#include <gcs/constraints/not_equals.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <sstream>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::max;
using std::min;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

namespace
{
    auto enforce_equality(ProofLogger * const logger, const auto & v1, const auto & v2, const State & state,
        InferenceTracker & inference, const optional<Literal> & cond) -> PropagatorState
    {
        auto val1 = state.optional_single_value(v1);
        if (val1) {
            inference.infer_equal(logger, v2, *val1, JustifyUsingRUP{}, Reason{[=]() { return Literals{v1 == *val1, cond ? *cond : TrueLiteral{}}; }});
            return PropagatorState::DisableUntilBacktrack;
        }

        auto val2 = state.optional_single_value(v2);
        if (val2) {
            inference.infer_equal(logger, v1, *val2, JustifyUsingRUP{}, Reason{[=]() { return Literals{v2 == *val2, cond ? *cond : TrueLiteral{}}; }});
            return PropagatorState::DisableUntilBacktrack;
        }

        if (state.domain_has_holes(v1) || state.domain_has_holes(v2)) {
            state.for_each_value(v1, [&](Integer val) {
                if (! state.in_domain(v2, val))
                    inference.infer_not_equal(logger, v1, val, JustifyUsingRUP{}, Reason{[=]() { return Literals{v2 != val, cond ? *cond : TrueLiteral{}}; }});
            });

            state.for_each_value(v2, [&](Integer val) {
                if (! state.in_domain(v1, val))
                    inference.infer_not_equal(logger, v2, val, JustifyUsingRUP{}, Reason{[=]() { return Literals{v1 != val, cond ? *cond : TrueLiteral{}}; }});
            });
        }
        else {
            auto bounds1 = state.bounds(v1), bounds2 = state.bounds(v2);
            if (bounds1 != bounds2) {
                inference.infer_greater_than_or_equal(logger, v2, bounds1.first, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v1 >= bounds1.first, cond ? *cond : TrueLiteral{}}}; }});
                inference.infer_greater_than_or_equal(logger, v1, bounds2.first, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v2 >= bounds2.first, cond ? *cond : TrueLiteral{}}}; }});
                inference.infer_less_than(logger, v2, bounds1.second + 1_i, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v1 < bounds1.second + 1_i, cond ? *cond : TrueLiteral{}}}; }});
                inference.infer_less_than(logger, v1, bounds2.second + 1_i, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v2 < bounds2.second + 1_i, cond ? *cond : TrueLiteral{}}}; }});
            }
        }

        return PropagatorState::Enable;
    }

    auto no_overlap_justification(const State & state, ProofLogger * const logger,
        IntegerVariableID v1, IntegerVariableID v2, Literal cond) -> pair<JustifyExplicitly, Reason>
    {
        auto v1_bounds = state.bounds(v1);
        Literals reason{{v1 >= v1_bounds.first, v1 < v1_bounds.second + 1_i}};

        for (Integer val = v1_bounds.first; val <= v1_bounds.second; ++val)
            if (state.in_domain(v1, val))
                reason.emplace_back(v2 != val);
            else
                reason.emplace_back(v1 != val);

        auto justify = [&state = state, logger = logger, v1 = v1, v2 = v2, v1_bounds = v1_bounds, cond = cond](
                           const Reason &) {
            for (Integer val = v1_bounds.first; val <= v1_bounds.second; ++val)
                if (state.in_domain(v1, val))
                    logger->emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * (v1 != val) + 1_i * (v2 == val) + 1_i * ! cond >= 1_i, ProofLevel::Temporary);
                else
                    logger->emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * (v2 != val) + 1_i * (v1 == val) + 1_i * ! cond >= 1_i, ProofLevel::Temporary);
        };

        return pair{JustifyExplicitly{justify}, Reason{[=]() { return reason; }}};
    }
}

Equals::Equals(const IntegerVariableID v1, const IntegerVariableID v2) :
    _v1(v1),
    _v2(v2)
{
}

auto Equals::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Equals>(_v1, _v2);
}

auto Equals::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    auto v1_is_constant = initial_state.optional_single_value(_v1);
    auto v2_is_constant = initial_state.optional_single_value(_v2);

    if (v1_is_constant && v2_is_constant) {
        if (*v1_is_constant != *v2_is_constant) {
            propagators.model_contradiction(initial_state, optional_model, "Equals constraint on two variables with different constant values");
            return;
        }
    }
    else if (v1_is_constant) {
        propagators.install_initialiser([v1_is_constant = v1_is_constant, v1 = _v1, v2 = _v2](State & state, ProofLogger * const logger) -> Inference {
            return state.infer_equal(logger, v2, *v1_is_constant, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v1 == *v1_is_constant}}; }});
        });
    }
    else if (v2_is_constant) {
        propagators.install_initialiser([v2_is_constant = v2_is_constant, v1 = _v1, v2 = _v2](State & state, ProofLogger * const logger) -> Inference {
            return state.infer_equal(logger, v1, *v2_is_constant, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v2 == *v2_is_constant}}; }});
        });
    }
    else {
        Triggers triggers;
        triggers.on_change = {_v1, _v2};

        visit([&](auto & _v1, auto & _v2) {
            propagators.install([v1 = _v1, v2 = _v2](const State & state, InferenceTracker & inference, ProofLogger * const logger) -> PropagatorState {
                return enforce_equality(logger, v1, v2, state, inference, nullopt);
            },
                triggers, "equals");
        },
            _v1, _v2);
    }

    if (optional_model)
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * _v1 + -1_i * _v2 == 0_i, nullopt);
}

auto Equals::describe_for_proof() -> string
{
    return "equals";
}

EqualsIf::EqualsIf(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
    _v1(v1),
    _v2(v2),
    _cond(cond)
{
}

auto EqualsIf::clone() const -> unique_ptr<Constraint>
{
    return make_unique<EqualsIf>(_v1, _v2, _cond);
}

auto EqualsIf::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    overloaded{
        [&](const TrueLiteral &) {
            Equals{_v1, _v2}.install(propagators, initial_state, optional_model);
        },
        [&](const FalseLiteral &) {
        },
        [&](const IntegerVariableCondition & cond) {
            Triggers triggers{.on_change = {_v1, _v2}};
            switch (cond.op) {
            case VariableConditionOperator::Less:
            case VariableConditionOperator::GreaterEqual:
                triggers.on_bounds.push_back(cond.var);
                break;
            case VariableConditionOperator::Equal:
            case VariableConditionOperator::NotEqual:
                triggers.on_change.push_back(cond.var);
                break;
            }

            visit([&](auto & _v1, auto & _v2) {
                propagators.install([v1 = _v1, v2 = _v2, cond = cond](const State & state, InferenceTracker & inference,
                                        ProofLogger * const logger) -> PropagatorState {
                    switch (state.test_literal(cond)) {
                    case LiteralIs::DefinitelyTrue: {
                        // condition is true, force equality
                        return enforce_equality(logger, v1, v2, state, inference, cond);
                    } break;

                    case LiteralIs::DefinitelyFalse: {
                        return PropagatorState::Enable;
                    } break;

                    case LiteralIs::Undecided: {
                        // condition is undecided, are we in a situation where it's now forced?
                        auto value1 = state.optional_single_value(v1);
                        auto value2 = state.optional_single_value(v2);
                        if (value1 && value2) {
                            if (*value1 != *value2) {
                                inference.infer(logger, ! cond, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v1 == *value1, v2 == *value2}}; }});
                                return PropagatorState::DisableUntilBacktrack;
                            }
                            else
                                return PropagatorState::DisableUntilBacktrack;
                        }
                        else if (value1) {
                            if (! state.in_domain(v2, *value1)) {
                                inference.infer(logger, ! cond, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v1 == *value1, v2 != *value1}}; }});
                                return PropagatorState::DisableUntilBacktrack;
                            }
                            else
                                return PropagatorState::Enable;
                        }
                        else if (value2) {
                            if (! state.in_domain(v1, *value2)) {
                                inference.infer(logger, ! cond, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v2 == *value2, v1 != *value2}}; }});
                                return PropagatorState::DisableUntilBacktrack;
                            }
                            else
                                return PropagatorState::Enable;
                        }
                        else {
                            // not equals is forced if there's no overlap between domains
                            bool overlap = false;
                            state.for_each_value_while(v1, [&](Integer val) {
                                if (state.in_domain(v2, val))
                                    overlap = true;
                                return ! overlap;
                            });

                            if (! overlap) {
                                auto [just, reason] = no_overlap_justification(state, logger, v1, v2, cond);
                                inference.infer(logger, ! cond, just, reason);
                                return PropagatorState::DisableUntilBacktrack;
                            }
                            else
                                return PropagatorState::Enable;
                        }
                    } break;
                    }

                    throw NonExhaustiveSwitch{};
                },
                    triggers, "equals if");
            },
                _v1, _v2);

            if (optional_model) {
                optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * _v1 + -1_i * _v2 == 0_i,
                    HalfReifyOnConjunctionOf{{cond}});
            }
        }}
        .visit(_cond);
}

auto EqualsIf::describe_for_proof() -> string
{
    return "equals if";
}

EqualsIff::EqualsIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
    _v1(v1),
    _v2(v2),
    _cond(cond)
{
}

auto EqualsIff::clone() const -> unique_ptr<Constraint>
{
    return make_unique<EqualsIff>(_v1, _v2, _cond);
}

auto EqualsIff::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    auto lower_common = max(initial_state.lower_bound(_v1), initial_state.lower_bound(_v2));
    auto upper_common = min(initial_state.upper_bound(_v1), initial_state.upper_bound(_v2));
    if (lower_common > upper_common) {
        if (optional_model)
            optional_model->add_constraint({{! _cond}});
        propagators.install_initialiser([cond = _cond, v1 = _v1, v2 = _v2](State & state, ProofLogger * const logger) {
            auto v1_bounds = state.bounds(v1);
            auto v2_bounds = state.bounds(v2);
            return state.infer(logger, ! cond, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v1 >= v1_bounds.first, v1 < v1_bounds.second + 1_i, v2 >= v2_bounds.first, v2 < v2_bounds.second + 1_i}}; }});
        });
        return;
    }

    overloaded{
        [&](const TrueLiteral &) {
            Equals{_v1, _v2}.install(propagators, initial_state, optional_model);
        },
        [&](const FalseLiteral &) {
            NotEquals{_v1, _v2}.install(propagators, initial_state, optional_model);
        },
        [&](const IntegerVariableCondition & cond) {
            Triggers triggers{.on_change = {_v1, _v2}};
            switch (cond.op) {
            case VariableConditionOperator::Less:
            case VariableConditionOperator::GreaterEqual:
                triggers.on_bounds.push_back(cond.var);
                break;
            case VariableConditionOperator::Equal:
            case VariableConditionOperator::NotEqual:
                triggers.on_change.push_back(cond.var);
                break;
            }

            visit([&](auto & _v1, auto & _v2) {
                propagators.install([v1 = _v1, v2 = _v2, cond = cond](
                                        const State & state, InferenceTracker & inference, ProofLogger * const logger) -> PropagatorState {
                    switch (state.test_literal(cond)) {
                    case LiteralIs::DefinitelyTrue: {
                        // condition is true, force equality
                        return enforce_equality(logger, v1, v2, state, inference, cond);
                    } break;

                    case LiteralIs::DefinitelyFalse: {
                        // condition is false, force inequality
                        auto value1 = state.optional_single_value(v1);
                        auto value2 = state.optional_single_value(v2);
                        if (value1 && value2) {
                            if (*value1 == *value2) {
                                inference.infer_false(logger, JustifyUsingRUP{}, [=]() { return Literals{v1 == *value1, v2 == *value2}; });
                            }
                            else
                                return PropagatorState::DisableUntilBacktrack;
                        }
                        else if (value1) {
                            inference.infer_not_equal(logger, v2, *value1, NoJustificationNeeded{}, Reason{});
                            return PropagatorState::DisableUntilBacktrack;
                        }
                        else if (value2) {
                            inference.infer_not_equal(logger, v1, *value2, NoJustificationNeeded{}, Reason{});
                            return PropagatorState::DisableUntilBacktrack;
                        }
                        else
                            return PropagatorState::Enable;
                    } break;

                    case LiteralIs::Undecided: {
                        // condition is undecided, are we in a situation where it's now forced?
                        auto value1 = state.optional_single_value(v1);
                        auto value2 = state.optional_single_value(v2);
                        if (value1 && value2) {
                            inference.infer(logger, *value1 == *value2 ? cond : ! cond, NoJustificationNeeded{}, Reason{});
                            return PropagatorState::DisableUntilBacktrack;
                        }
                        else if (value1) {
                            if (! state.in_domain(v2, *value1)) {
                                inference.infer(logger, ! cond, NoJustificationNeeded{}, Reason{});
                                return PropagatorState::DisableUntilBacktrack;
                            }
                            else
                                return PropagatorState::Enable;
                        }
                        else if (value2) {
                            if (! state.in_domain(v1, *value2)) {
                                inference.infer(logger, ! cond, NoJustificationNeeded{}, Reason{});
                                return PropagatorState::DisableUntilBacktrack;
                            }
                            else
                                return PropagatorState::Enable;
                        }
                        else {
                            // not equals is forced if there's no overlap between domains
                            bool overlap = false;
                            state.for_each_value_while(v1, [&](Integer val) {
                                if (state.in_domain(v2, val))
                                    overlap = true;
                                return ! overlap;
                            });

                            if (! overlap) {
                                auto [just, reason] = no_overlap_justification(state, logger, v1, v2, cond);
                                inference.infer(logger, ! cond, just, reason);
                                return PropagatorState::DisableUntilBacktrack;
                            }
                            else
                                return PropagatorState::Enable;
                        }
                    } break;
                    }

                    throw NonExhaustiveSwitch{};
                },
                    triggers, "equals iff");
            },
                _v1, _v2);

            if (optional_model) {
                auto v1_is_constant = initial_state.optional_single_value(_v1);
                auto v2_is_constant = initial_state.optional_single_value(_v2);

                if (v1_is_constant) {
                    optional_model->add_constraint({{_v2 == *v1_is_constant}, {! cond}});
                    optional_model->add_constraint({{_v2 != *v1_is_constant}, {cond}});
                }
                else if (v2_is_constant) {
                    optional_model->add_constraint({{_v1 == *v2_is_constant}, {! cond}});
                    optional_model->add_constraint({{_v1 != *v2_is_constant}, {cond}});
                }
                else {
                    if (initial_state.lower_bound(_v1) < lower_common)
                        optional_model->add_constraint({{_v1 >= lower_common}, {! cond}});
                    if (initial_state.lower_bound(_v2) < lower_common)
                        optional_model->add_constraint({{_v2 >= lower_common}, {! cond}});
                    if (initial_state.upper_bound(_v1) > upper_common)
                        optional_model->add_constraint({{_v1 < upper_common + 1_i}, {! cond}});
                    if (initial_state.upper_bound(_v2) > upper_common)
                        optional_model->add_constraint({{_v2 < upper_common + 1_i}, {! cond}});

                    // (cond and _v1 == v) -> _v2 == v
                    for (auto v = lower_common; v <= upper_common; ++v)
                        optional_model->add_constraint({{_v1 != v}, {_v2 == v}, {! cond}});

                    // (! cond and _v1 == v) -> _v2 != v
                    for (auto v = lower_common; v <= upper_common; ++v)
                        optional_model->add_constraint({{cond}, {_v1 != v}, {_v2 != v}});
                }
            }
        }}
        .visit(_cond);
}

auto EqualsIff::describe_for_proof() -> string
{
    return "equals iff";
}
