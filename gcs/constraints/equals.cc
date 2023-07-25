#include <gcs/constraints/equals.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proof.hh>
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
using std::pair;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

namespace
{
    auto enforce_equality(const auto & v1, const auto & v2, State & state) -> pair<Inference, PropagatorState>
    {
        auto val1 = state.optional_single_value(v1);
        if (val1)
            return pair{state.infer_equal(v2, *val1, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};

        auto val2 = state.optional_single_value(v2);
        if (val2)
            return pair{state.infer_equal(v1, *val2, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};

        Inference result = Inference::NoChange;
        if (state.domain_has_holes(v1) || state.domain_has_holes(v2) || state.maybe_proof()) {
            state.for_each_value_while(v1, [&](Integer val) {
                if (! state.in_domain(v2, val))
                    increase_inference_to(result, state.infer_not_equal(v1, val, JustifyUsingRUP{}));
                return result != Inference::Contradiction;
            });

            state.for_each_value_while(v2, [&](Integer val) {
                if (! state.in_domain(v1, val))
                    increase_inference_to(result, state.infer_not_equal(v2, val, JustifyUsingRUP{}));
                return result != Inference::Contradiction;
            });
        }
        else {
            auto bounds1 = state.bounds(v1), bounds2 = state.bounds(v2);
            if (bounds1 != bounds2) {
                increase_inference_to(result, state.infer_greater_than_or_equal(v2, bounds1.first, JustifyUsingRUP{}));
                if (result != Inference::Contradiction)
                    increase_inference_to(result, state.infer_greater_than_or_equal(v1, bounds2.first, JustifyUsingRUP{}));
                if (result != Inference::Contradiction)
                    increase_inference_to(result, state.infer_less_than(v2, bounds1.second + 1_i, JustifyUsingRUP{}));
                if (result != Inference::Contradiction)
                    increase_inference_to(result, state.infer_less_than(v1, bounds2.second + 1_i, JustifyUsingRUP{}));
            }
        }

        return pair{result, PropagatorState::Enable};
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

auto Equals::install(Propagators & propagators, State & initial_state) && -> void
{
    auto v1_is_constant = initial_state.optional_single_value(_v1);
    auto v2_is_constant = initial_state.optional_single_value(_v2);

    if (v1_is_constant && v2_is_constant) {
        if (*v1_is_constant != *v2_is_constant) {
            propagators.model_contradiction("Equals constraint on two variables with different constant values");
            return;
        }
    }
    else if (v1_is_constant) {
        propagators.install([v1_is_constant = v1_is_constant, v2 = _v2](State & state) -> pair<Inference, PropagatorState> {
            return pair{state.infer_equal(v2, *v1_is_constant, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
        },
            Triggers{}, "equals");
    }
    else if (v2_is_constant) {
        propagators.install([v2_is_constant = v2_is_constant, v1 = _v1](State & state) -> pair<Inference, PropagatorState> {
            return pair{state.infer_equal(v1, *v2_is_constant, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
        },
            Triggers{}, "equals");
    }
    else {
        Triggers triggers;
        triggers.on_change = {_v1, _v2};

        visit([&](auto & _v1, auto & _v2) {
            propagators.install([v1 = _v1, v2 = _v2](State & state) -> pair<Inference, PropagatorState> {
                return enforce_equality(v1, v2, state);
            },
                triggers, "equals");
        },
            _v1, _v2);
    }

    if (propagators.want_definitions()) {
        propagators.define_linear_eq(initial_state, WeightedSum{} + 1_i * _v1 + -1_i * _v2, 0_i, nullopt);
    }
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

auto EqualsIf::install(Propagators & propagators, State & initial_state) && -> void
{
    overloaded{
        [&](const TrueLiteral &) {
            Equals{_v1, _v2}.install(propagators, initial_state);
        },
        [&](const FalseLiteral &) {
        },
        [&](const LiteralFromIntegerVariable & cond) {
            Triggers triggers{.on_change = {_v1, _v2}};
            switch (cond.op) {
            case LiteralFromIntegerVariable::Operator::Less:
            case LiteralFromIntegerVariable::Operator::GreaterEqual:
                triggers.on_bounds.push_back(cond.var);
                break;
            case LiteralFromIntegerVariable::Operator::Equal:
            case LiteralFromIntegerVariable::Operator::NotEqual:
                triggers.on_change.push_back(cond.var);
                break;
            }

            visit([&](auto & _v1, auto & _v2) {
                propagators.install([v1 = _v1, v2 = _v2, cond = cond](State & state) -> pair<Inference, PropagatorState> {
                    switch (state.test_literal(cond)) {
                    case LiteralIs::DefinitelyTrue: {
                        // condition is true, force equality
                        return enforce_equality(v1, v2, state);
                    } break;

                    case LiteralIs::DefinitelyFalse: {
                        return pair{Inference::NoChange, PropagatorState::Enable};
                    } break;

                    case LiteralIs::Undecided: {
                        // condition is undecided, are we in a situation where it's now forced?
                        auto value1 = state.optional_single_value(v1);
                        auto value2 = state.optional_single_value(v2);
                        if (value1 && value2) {
                            if (*value1 != *value2)
                                return pair{state.infer(! cond, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
                            else
                                return pair{Inference::NoChange, PropagatorState::DisableUntilBacktrack};
                        }
                        else if (value1) {
                            if (! state.in_domain(v2, *value1))
                                return pair{state.infer(! cond, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
                            else
                                return pair{Inference::NoChange, PropagatorState::Enable};
                        }
                        else if (value2) {
                            if (! state.in_domain(v1, *value2))
                                return pair{state.infer(! cond, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
                            else
                                return pair{Inference::NoChange, PropagatorState::Enable};
                        }
                        else {
                            // not equals is forced if there's no overlap between domains
                            bool overlap = false;
                            state.for_each_value_while(v1, [&](Integer val) {
                                if (state.in_domain(v2, val))
                                    overlap = true;
                                return ! overlap;
                            });

                            if (! overlap)
                                return pair{state.infer(! cond, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
                            else
                                return pair{Inference::NoChange, PropagatorState::Enable};
                        }
                    } break;
                    }

                    throw NonExhaustiveSwitch{};
                },
                    triggers, "equals if");
            },
                _v1, _v2);

            if (propagators.want_definitions()) {
                propagators.define_linear_eq(initial_state, WeightedSum{} + 1_i * _v1 + -1_i * _v2, 0_i, cond);
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

auto EqualsIff::install(Propagators & propagators, State & initial_state) && -> void
{
    auto lower_common = max(initial_state.lower_bound(_v1), initial_state.lower_bound(_v2));
    auto upper_common = min(initial_state.upper_bound(_v1), initial_state.upper_bound(_v2));
    if (lower_common > upper_common) {
        propagators.define_cnf(initial_state, {{! _cond}});
        propagators.install([cond = _cond](State & state) {
            return pair{state.infer(! cond, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
        },
            Triggers{}, "equals iff");
        return;
    }

    overloaded{
        [&](const TrueLiteral &) {
            Equals{_v1, _v2}.install(propagators, initial_state);
        },
        [&](const FalseLiteral &) {
            NotEquals{_v1, _v2}.install(propagators, initial_state);
        },
        [&](const LiteralFromIntegerVariable & cond) {
            Triggers triggers{.on_change = {_v1, _v2}};
            switch (cond.op) {
            case LiteralFromIntegerVariable::Operator::Less:
            case LiteralFromIntegerVariable::Operator::GreaterEqual:
                triggers.on_bounds.push_back(cond.var);
                break;
            case LiteralFromIntegerVariable::Operator::Equal:
            case LiteralFromIntegerVariable::Operator::NotEqual:
                triggers.on_change.push_back(cond.var);
                break;
            }

            visit([&](auto & _v1, auto & _v2) {
                propagators.install([v1 = _v1, v2 = _v2, cond = cond](State & state) -> pair<Inference, PropagatorState> {
                    switch (state.test_literal(cond)) {
                    case LiteralIs::DefinitelyTrue: {
                        // condition is true, force equality
                        return enforce_equality(v1, v2, state);
                    } break;

                    case LiteralIs::DefinitelyFalse: {
                        // condition is false, force inequality
                        auto value1 = state.optional_single_value(v1);
                        auto value2 = state.optional_single_value(v2);
                        if (value1 && value2)
                            return pair{(*value1 != *value2) ? Inference::NoChange : Inference::Contradiction, PropagatorState::DisableUntilBacktrack};
                        else if (value1)
                            return pair{state.infer_not_equal(v2, *value1, NoJustificationNeeded{}), PropagatorState::DisableUntilBacktrack};
                        else if (value2)
                            return pair{state.infer_not_equal(v1, *value2, NoJustificationNeeded{}), PropagatorState::DisableUntilBacktrack};
                        else
                            return pair{Inference::NoChange, PropagatorState::Enable};
                    } break;

                    case LiteralIs::Undecided: {
                        // condition is undecided, are we in a situation where it's now forced?
                        auto value1 = state.optional_single_value(v1);
                        auto value2 = state.optional_single_value(v2);
                        if (value1 && value2) {
                            return pair{state.infer(*value1 == *value2 ? cond : ! cond,
                                            NoJustificationNeeded{}),
                                PropagatorState::DisableUntilBacktrack};
                        }
                        else if (value1) {
                            if (! state.in_domain(v2, *value1))
                                return pair{state.infer(! cond, NoJustificationNeeded{}), PropagatorState::DisableUntilBacktrack};
                            else
                                return pair{Inference::NoChange, PropagatorState::Enable};
                        }
                        else if (value2) {
                            if (! state.in_domain(v1, *value2))
                                return pair{state.infer(! cond, NoJustificationNeeded{}), PropagatorState::DisableUntilBacktrack};
                            else
                                return pair{Inference::NoChange, PropagatorState::Enable};
                        }
                        else {
                            // not equals is forced if there's no overlap between domains
                            bool overlap = false;
                            state.for_each_value_while(v1, [&](Integer val) {
                                if (state.in_domain(v2, val))
                                    overlap = true;
                                return ! overlap;
                            });

                            if (! overlap)
                                return pair{state.infer(! cond, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
                            else
                                return pair{Inference::NoChange, PropagatorState::Enable};
                        }
                    } break;
                    }

                    throw NonExhaustiveSwitch{};
                },
                    triggers, "equals iff");
            },
                _v1, _v2);

            if (propagators.want_definitions()) {
                auto v1_is_constant = initial_state.optional_single_value(_v1);
                auto v2_is_constant = initial_state.optional_single_value(_v2);

                if (v1_is_constant) {
                    propagators.define_cnf(initial_state, {{_v2 == *v1_is_constant}, {! cond}});
                    propagators.define_cnf(initial_state, {{_v2 != *v1_is_constant}, {cond}});
                }
                else if (v2_is_constant) {
                    propagators.define_cnf(initial_state, {{_v1 == *v2_is_constant}, {! cond}});
                    propagators.define_cnf(initial_state, {{_v1 != *v2_is_constant}, {cond}});
                }
                else {
                    if (initial_state.lower_bound(_v1) < lower_common)
                        propagators.define_cnf(initial_state, {{_v1 >= lower_common}, {! cond}});
                    if (initial_state.lower_bound(_v2) < lower_common)
                        propagators.define_cnf(initial_state, {{_v2 >= lower_common}, {! cond}});
                    if (initial_state.upper_bound(_v1) > upper_common)
                        propagators.define_cnf(initial_state, {{_v1 < upper_common + 1_i}, {! cond}});
                    if (initial_state.upper_bound(_v2) > upper_common)
                        propagators.define_cnf(initial_state, {{_v2 < upper_common + 1_i}, {! cond}});

                    // (cond and _v1 == v) -> _v2 == v
                    for (auto v = lower_common; v <= upper_common; ++v)
                        propagators.define_cnf(initial_state, {{_v1 != v}, {_v2 == v}, {! cond}});

                    // (! cond and _v1 == v) -> _v2 != v
                    for (auto v = lower_common; v <= upper_common; ++v)
                        propagators.define_cnf(initial_state, {{cond}, {_v1 != v}, {_v2 != v}});
                }
            }
        }}
        .visit(_cond);
}

auto EqualsIff::describe_for_proof() -> string
{
    return "equals iff";
}

NotEquals::NotEquals(const IntegerVariableID v1, const IntegerVariableID v2) :
    _v1(v1),
    _v2(v2)
{
}

auto NotEquals::clone() const -> unique_ptr<Constraint>
{
    return make_unique<NotEquals>(_v1, _v2);
}

auto NotEquals::install(Propagators & propagators, State & initial_state) && -> void
{
    auto v1_is_constant = initial_state.optional_single_value(_v1);
    auto v2_is_constant = initial_state.optional_single_value(_v2);

    bool convert_to_values_ne = false;

    if (v1_is_constant && v2_is_constant) {
        if (*v1_is_constant == *v2_is_constant) {
            propagators.model_contradiction("NotEquals constraint on two variables with the same constant values");
            return;
        }
    }
    else if (v1_is_constant) {
        propagators.install([v1_is_constant = v1_is_constant, v2 = _v2](State & state) -> pair<Inference, PropagatorState> {
            return pair{state.infer_not_equal(v2, *v1_is_constant, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
        },
            Triggers{}, "not equals");
    }
    else if (v2_is_constant) {
        propagators.install([v2_is_constant = v2_is_constant, v1 = _v1](State & state) -> pair<Inference, PropagatorState> {
            return pair{state.infer_not_equal(v1, *v2_is_constant, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
        },
            Triggers{}, "not equals");
    }
    else {
        if (initial_state.domain_size(_v1) < 100_i && initial_state.domain_size(_v2) < 100_i)
            convert_to_values_ne = true;

        Triggers triggers;
        triggers.on_instantiated = {_v1, _v2};

        visit([&](auto & _v1, auto & _v2) {
            propagators.install([v1 = _v1, v2 = _v2, convert_to_values_ne = convert_to_values_ne](State & state) -> pair<Inference, PropagatorState> {
                auto value1 = state.optional_single_value(v1);
                if (value1)
                    return pair{state.infer_not_equal(v2, *value1, convert_to_values_ne ? Justification{NoJustificationNeeded{}} : Justification{JustifyUsingRUP{}}),
                        PropagatorState::DisableUntilBacktrack};
                auto value2 = state.optional_single_value(v2);
                if (value2)
                    return pair{state.infer_not_equal(v1, *value2, convert_to_values_ne ? Justification{NoJustificationNeeded{}} : Justification{JustifyUsingRUP{}}),
                        PropagatorState::DisableUntilBacktrack};
                return pair{Inference::NoChange, PropagatorState::Enable};
            },
                triggers, "not equals");
        },
            _v1, _v2);

        if (convert_to_values_ne && propagators.want_definitions()) {
            propagators.install([v1 = _v1, v2 = _v2](State & state) -> pair<Inference, PropagatorState> {
                state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) -> void {
                    proof.emit_proof_comment("converting not equals to value encoding");
                    // proof.emit_proof_comment("converting not equals to value encoding", true);
                    state.for_each_value(v1, [&](Integer val1) {
                        if (state.in_domain(v2, val1)) {
                            proof.need_proof_variable(v1 != val1);
                            proof.need_proof_variable(v2 != val1);
                            // proof.need_proof_variable(v1 != val1, true);
                            // proof.need_proof_variable(v2 != val1, true);                           
                            stringstream line;
                            line << "u 1 " << proof.proof_variable(v1 != val1) << " 1 " << proof.proof_variable(v2 != val1)
                                 << " >= 1 ;";
                            proof.emit_proof_line(line.str());
                            // proof.emit_proof_line(line.str(), true);
                        }
                    });
                }});
                return pair{Inference::NoChange, PropagatorState::DisableUntilBacktrack};
            },
                Triggers{}, "not equals conversion");
        }
    }

    if (propagators.want_definitions()) {
        auto selector = propagators.create_proof_flag("notequals");

        propagators.define_linear_le(initial_state, WeightedSum{} + 1_i * _v1 + -1_i * _v2, -1_i, selector);
        propagators.define_linear_le(initial_state, WeightedSum{} + -1_i * _v1 + 1_i * _v2, -1_i, ! selector);
    }
}

auto NotEquals::describe_for_proof() -> string
{
    return "not equals";
}
