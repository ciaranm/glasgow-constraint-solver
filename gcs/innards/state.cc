#include <gcs/exception.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>
#include <gcs/innards/variable_id_utils.hh>
#include <gcs/problem.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <bit>
#include <list>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::countr_zero;
using std::function;
using std::generator;
using std::get;
using std::list;
using std::make_optional;
using std::make_shared;
using std::max;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::to_string;
using std::tuple;
using std::vector;
using std::visit;

namespace
{
    auto deview(const SimpleIntegerVariableID & var) -> tuple<SimpleIntegerVariableID, bool, Integer>
    {
        return tuple{var, false, 0_i};
    }

    auto deview(const ViewOfIntegerVariableID & var) -> tuple<SimpleIntegerVariableID, bool, Integer>
    {
        return tuple{var.actual_variable, var.negate_first, var.then_add};
    }

    auto deview(const ConstantIntegerVariableID & var) -> tuple<ConstantIntegerVariableID, bool, Integer>
    {
        return tuple{var, false, 0_i};
    }

    auto deview(const IntegerVariableID & var) -> tuple<DirectIntegerVariableID, bool, Integer>
    {
        return overloaded{
            [&](const SimpleIntegerVariableID & var) {
                return tuple{DirectIntegerVariableID{var}, false, 0_i};
            },
            [&](const ConstantIntegerVariableID & var) {
                return tuple{DirectIntegerVariableID{var}, false, 0_i};
            },
            [&](const ViewOfIntegerVariableID & var) {
                return tuple{DirectIntegerVariableID{var.actual_variable}, var.negate_first, var.then_add};
            },
        }
            .visit(var);
    }

    auto deview(const DirectIntegerVariableID & var) -> tuple<DirectIntegerVariableID, bool, Integer>
    {
        return overloaded{
            [&](const SimpleIntegerVariableID & var) {
                return tuple{DirectIntegerVariableID{var}, false, 0_i};
            },
            [&](const ConstantIntegerVariableID & var) {
                return tuple{DirectIntegerVariableID{var}, false, 0_i};
            }}
            .visit(var);
    }
}

template <typename VarType_>
struct State::GetStateAndOffsetOf
{
    tuple<DirectIntegerVariableID, bool, Integer> var_negate_then_add;
    IntegerVariableState space;
    const IntegerVariableState & state;

    GetStateAndOffsetOf(const State & state, const VarType_ & var) :
        var_negate_then_add(deview(var)),
        space(IntegerVariableConstantState{0_i}),
        state(state.state_of(get<0>(var_negate_then_add), space))
    {
    }
};

template <>
struct State::GetStateAndOffsetOf<SimpleIntegerVariableID>
{
    tuple<SimpleIntegerVariableID, bool, Integer> var_negate_then_add;
    const IntegerVariableState & state;

    GetStateAndOffsetOf(const State & state, const SimpleIntegerVariableID & var) :
        var_negate_then_add(deview(var)),
        state(state.state_of(get<0>(var_negate_then_add)))
    {
    }
};

template <>
struct State::GetStateAndOffsetOf<ViewOfIntegerVariableID>
{
    tuple<SimpleIntegerVariableID, bool, Integer> var_negate_then_add;
    const IntegerVariableState & state;

    GetStateAndOffsetOf(const State & state, const ViewOfIntegerVariableID & var) :
        var_negate_then_add(deview(var)),
        state(state.state_of(get<0>(var_negate_then_add)))
    {
    }
};

template <typename VarType_>
struct State::GetMutableStateAndOffsetOf
{
    tuple<DirectIntegerVariableID, bool, Integer> var_negate_then_add;
    IntegerVariableState space;
    IntegerVariableState & state;

    GetMutableStateAndOffsetOf(State & state, const VarType_ & var) :
        var_negate_then_add(deview(var)),
        space(IntegerVariableConstantState{0_i}),
        state(state.state_of(get<0>(var_negate_then_add), space))
    {
    }
};

template <>
struct State::GetMutableStateAndOffsetOf<SimpleIntegerVariableID>
{
    tuple<SimpleIntegerVariableID, bool, Integer> var_negate_then_add;
    IntegerVariableState & state;

    GetMutableStateAndOffsetOf(State & state, const SimpleIntegerVariableID & var) :
        var_negate_then_add(deview(var)),
        state(state.state_of(get<0>(var_negate_then_add)))
    {
    }
};

template <>
struct State::GetMutableStateAndOffsetOf<ViewOfIntegerVariableID>
{
    tuple<SimpleIntegerVariableID, bool, Integer> var_negate_then_add;
    IntegerVariableState & state;

    GetMutableStateAndOffsetOf(State & state, const SimpleIntegerVariableID & var) :
        var_negate_then_add(deview(var)),
        state(state.state_of(get<0>(var_negate_then_add)))
    {
    }
};

struct State::Imp
{
    ProofLogger * maybe_proof_logger;

    list<vector<IntegerVariableState>> integer_variable_states{};
    list<vector<ConstraintState>> constraint_states{};
    vector<ConstraintState> persistent_constraint_states{};
    list<vector<function<auto()->void>>> on_backtracks{};
    vector<Literal> guesses{};
    vector<Literal> extra_proof_conditions{};

    optional<IntegerVariableID> optional_minimise_variable{};
    optional<Integer> optional_objective_incumbent{};
};

State::State() :
    _imp(new Imp{})
{
    _imp->integer_variable_states.emplace_back();
    _imp->constraint_states.emplace_back();
    _imp->on_backtracks.emplace_back();
}

State::State(State && other) noexcept :
    _imp(move(other._imp))
{
}

State::~State() = default;

auto State::clone() const -> State
{
    auto result = State{};
    result._imp->integer_variable_states = _imp->integer_variable_states;
    result._imp->constraint_states = _imp->constraint_states;
    result._imp->persistent_constraint_states = _imp->persistent_constraint_states;
    result._imp->on_backtracks = _imp->on_backtracks;
    result._imp->optional_minimise_variable = _imp->optional_minimise_variable;
    result._imp->optional_objective_incumbent = _imp->optional_objective_incumbent;
    result._imp->maybe_proof_logger = _imp->maybe_proof_logger;
    return result;
}

auto State::allocate_integer_variable_with_state(Integer lower, Integer upper) -> SimpleIntegerVariableID
{
    if (lower == upper)
        _imp->integer_variable_states.back().push_back(IntegerVariableConstantState{lower});
    else
        _imp->integer_variable_states.back().push_back(IntegerVariableRangeState{lower, upper});

    return SimpleIntegerVariableID{_imp->integer_variable_states.back().size() - 1};
}

auto State::what_variable_id_will_be_created_next() const -> SimpleIntegerVariableID
{
    return SimpleIntegerVariableID{_imp->integer_variable_states.back().size()};
}

auto State::assign_to_state_of(const DirectIntegerVariableID i) -> IntegerVariableState &
{
    return overloaded{
        [&](const SimpleIntegerVariableID & v) -> IntegerVariableState & {
            return _imp->integer_variable_states.back()[v.index];
        },
        [&](const ConstantIntegerVariableID &) -> IntegerVariableState & {
            throw UnexpectedException{"shouldn't have a const here"};
        }}
        .visit(i);
}

auto State::state_of(const ConstantIntegerVariableID & v, IntegerVariableState & space) -> IntegerVariableState &
{
    space = IntegerVariableConstantState{v.const_value};
    return space;
}

auto State::state_of(const ConstantIntegerVariableID & v, IntegerVariableState & space) const -> const IntegerVariableState &
{
    space = IntegerVariableConstantState{v.const_value};
    return space;
}

auto State::state_of(const SimpleIntegerVariableID & v) -> IntegerVariableState &
{
    return _imp->integer_variable_states.back().at(v.index);
}

auto State::state_of(const SimpleIntegerVariableID & v) const -> const IntegerVariableState &
{
    return _imp->integer_variable_states.back().at(v.index);
}

auto State::state_of(const DirectIntegerVariableID & v, IntegerVariableState & space) -> IntegerVariableState &
{
    return overloaded{
        [&](const SimpleIntegerVariableID & v) -> IntegerVariableState & { return state_of(v); },
        [&](const ConstantIntegerVariableID & v) -> IntegerVariableState & { return state_of(v, space); }}
        .visit(v);
}

auto State::state_of(const DirectIntegerVariableID & v, IntegerVariableState & space) const -> const IntegerVariableState &
{
    return overloaded{
        [&](const SimpleIntegerVariableID & v) -> const IntegerVariableState & { return state_of(v); },
        [&](const ConstantIntegerVariableID & v) -> const IntegerVariableState & { return state_of(v, space); }}
        .visit(v);
}

template <DirectIntegerVariableIDLike VarType_>
auto State::change_state_for_equal(
    const VarType_ & var,
    Integer value) -> Inference
{
    GetMutableStateAndOffsetOf<VarType_> get_state{*this, var};

    // Has to be equal. If the value isn't in the domain, we've found a
    // contradiction, otherwise update to a constant value.
    return overloaded{
        [&](IntegerVariableConstantState & c) -> Inference {
            if (c.value == value)
                return Inference::NoChange;
            else
                return Inference::Contradiction;
        },
        [&](IntegerVariableRangeState & rvar) -> Inference {
            if (value < rvar.lower || value > rvar.upper)
                return Inference::Contradiction;
            else if (rvar.lower == rvar.upper && rvar.lower == value) {
                assign_to_state_of(var) = IntegerVariableConstantState{value};
                return Inference::NoChange;
            }
            else {
                assign_to_state_of(var) = IntegerVariableConstantState{value};
                return Inference::Instantiated;
            }
        },
        [&](IntegerVariableSmallSetState & svar) -> Inference {
            if (value < svar.lower || value > (svar.lower + Integer{Bits::number_of_bits - 1})) {
                return Inference::Contradiction;
            }
            else if (! svar.bits.test((value - svar.lower).raw_value)) {
                return Inference::Contradiction;
            }
            else if (svar.bits.popcount() == 1) {
                assign_to_state_of(var) = IntegerVariableConstantState{value};
                return Inference::NoChange;
            }
            else {
                assign_to_state_of(var) = IntegerVariableConstantState{value};
                return Inference::Instantiated;
            }
        },
        [&](IntegerVariableIntervalSetState & svar) -> Inference {
            if (svar.values->contains(value)) {
                if (svar.values->lower() == svar.values->upper()) {
                    assign_to_state_of(var) = IntegerVariableConstantState{value};
                    return Inference::NoChange;
                }
                else {
                    assign_to_state_of(var) = IntegerVariableConstantState{value};
                    return Inference::Instantiated;
                }
            }
            else
                return Inference::Contradiction;
        }}
        .visit(get_state.state);
}

template <DirectIntegerVariableIDLike VarType_>
auto State::change_state_for_not_equal(
    const VarType_ & var,
    Integer value) -> Inference
{
    GetMutableStateAndOffsetOf<VarType_> get_state{*this, var};

    return overloaded{
        [&](IntegerVariableConstantState & cvar) -> Inference {
            // Constant equal to the value, potential problem!
            return cvar.value != value
                ? Inference::NoChange
                : Inference::Contradiction;
        },
        [&](IntegerVariableRangeState & rvar) -> Inference {
            if (value < rvar.lower || value > rvar.upper) {
                // not in the domain, no problem
                return Inference::NoChange;
            }
            else if (rvar.lower == rvar.upper) {
                // Constant equal to the value, problem!
                return Inference::Contradiction;
            }
            else if (rvar.lower == value) {
                // Can just bump the bound
                ++rvar.lower;
                if (rvar.lower == rvar.upper) {
                    assign_to_state_of(var) = IntegerVariableConstantState{rvar.lower};
                    return Inference::Instantiated;
                }
                else
                    return Inference::BoundsChanged;
            }
            else if (rvar.upper == value) {
                --rvar.upper;

                if (rvar.lower == rvar.upper) {
                    assign_to_state_of(var) = IntegerVariableConstantState{rvar.lower};
                    return Inference::Instantiated;
                }
                else
                    return Inference::BoundsChanged;
            }
            else {
                // Holey domain, convert to set. This should handle offsets...
                if (rvar.lower < 0_i || rvar.upper >= Integer{Bits::number_of_bits}) {
                    auto values = make_shared<IntervalSet<Integer>>(rvar.lower, rvar.upper);
                    values->erase(value);
                    assign_to_state_of(var) = IntegerVariableIntervalSetState{values};
                }
                else {
                    IntegerVariableSmallSetState svar{Integer{0}, Bits{}};
                    for (Integer v = rvar.lower; v <= rvar.upper; ++v)
                        if (v != value)
                            svar.bits.set(v.raw_value);
                    assign_to_state_of(var) = move(svar);
                }
                return Inference::InteriorValuesChanged;
            }
        },
        [&](IntegerVariableSmallSetState & svar) -> Inference {
            if (value < svar.lower || value > (svar.lower + Integer{Bits::number_of_bits - 1})) {
                // out of bounds, not in domain
                return Inference::NoChange;
            }
            else if (! svar.bits.test((value - svar.lower).raw_value)) {
                // not in domain, no problem
                return Inference::NoChange;
            }

            // Knock out the value
            bool is_bound = (value == svar.lower + Integer{svar.bits.countr_zero()}) ||
                (value == svar.lower + Integer{Bits::number_of_bits} - Integer{svar.bits.countl_zero()} - 1_i);
            svar.bits.reset((value - svar.lower).raw_value);
            if (svar.bits.has_single_bit()) {
                assign_to_state_of(var) = IntegerVariableConstantState{svar.lower + Integer{svar.bits.countr_zero()}};
                return Inference::Instantiated;
            }
            else if (svar.bits.none())
                return Inference::Contradiction;
            else if (is_bound)
                return Inference::BoundsChanged;
            else
                return Inference::InteriorValuesChanged;
        },
        [&](IntegerVariableIntervalSetState & svar) -> Inference {
            if (! svar.values->contains(value))
                return Inference::NoChange;

            // Knock out the value
            bool is_bound = (value == svar.values->lower() || value == svar.values->upper());
            if (svar.values->lower() == svar.values->upper())
                return Inference::Contradiction;
            else if (svar.values.use_count() == 1) {
                svar.values->erase(value);
                if (svar.values->lower() == svar.values->upper()) {
                    assign_to_state_of(var) = IntegerVariableConstantState{svar.values->lower()};
                    return Inference::Instantiated;
                }

                return is_bound ? Inference::BoundsChanged : Inference::InteriorValuesChanged;
            }
            else {
                auto new_values = make_shared<IntervalSet<Integer>>(*svar.values);
                new_values->erase(value);
                svar.values = new_values;
                if (svar.values->lower() == svar.values->upper()) {
                    assign_to_state_of(var) = IntegerVariableConstantState{svar.values->lower()};
                    return Inference::Instantiated;
                }
                return is_bound ? Inference::BoundsChanged : Inference::InteriorValuesChanged;
            }
        }}
        .visit(get_state.state);
}

template <DirectIntegerVariableIDLike VarType_>
auto State::change_state_for_less_than(
    const VarType_ & var,
    Integer value) -> Inference
{
    GetMutableStateAndOffsetOf<VarType_> get_state{*this, var};

    return overloaded{
        [&](IntegerVariableConstantState & c) -> Inference {
            // Ok if the constant is less, otherwise contradiction
            return c.value < value ? Inference::NoChange : Inference::Contradiction;
        },
        [&](IntegerVariableRangeState & rvar) -> Inference {
            if (rvar.upper >= value) {
                rvar.upper = value - 1_i;
                if (rvar.lower == rvar.upper) {
                    assign_to_state_of(var) = IntegerVariableConstantState{rvar.lower};
                    return Inference::Instantiated;
                }
                else if (rvar.lower > rvar.upper)
                    return Inference::Contradiction;
                else
                    return Inference::BoundsChanged;
            }
            else
                return Inference::NoChange;
        },
        [&](IntegerVariableSmallSetState & svar) -> Inference {
            auto pc_before = svar.bits.popcount();

            int first_bit_to_clear = (value - svar.lower).raw_value;
            if (first_bit_to_clear < 0)
                return Inference::Contradiction;

            int word_to_modify = first_bit_to_clear / Bits::bits_per_word;
            if (word_to_modify < Bits::n_words) {
                int number_of_bits_to_keep = first_bit_to_clear % Bits::bits_per_word;
                Bits::BitWord mask = (Bits::BitWord{1} << number_of_bits_to_keep) - 1;
                svar.bits.data[word_to_modify] &= mask;
                for (int w = word_to_modify + 1; w < Bits::n_words; ++w)
                    svar.bits.data[w] = 0;
            }
            else
                return Inference::NoChange;

            auto pc_after = svar.bits.popcount();
            if (pc_after == 0)
                return Inference::Contradiction;
            if (pc_after == 1) {
                assign_to_state_of(var) = IntegerVariableConstantState{svar.lower + Integer{svar.bits.countr_zero()}};
                return Inference::Instantiated;
            }
            return pc_before == pc_after ? Inference::NoChange : Inference::BoundsChanged;
        },
        [&](IntegerVariableIntervalSetState & svar) -> Inference {
            if (svar.values->upper() < value)
                return Inference::NoChange;

            if (svar.values.use_count() != 1)
                svar.values = make_shared<IntervalSet<Integer>>(*svar.values);

            svar.values->erase_greater_than(value - 1_i);
            if (svar.values->empty())
                return Inference::Contradiction;
            else if (svar.values->lower() == svar.values->upper()) {
                assign_to_state_of(var) = IntegerVariableConstantState{svar.values->lower()};
                return Inference::Instantiated;
            }
            else
                return Inference::BoundsChanged;
        }}
        .visit(get_state.state);
}

template <DirectIntegerVariableIDLike VarType_>
auto State::change_state_for_greater_than_or_equal(
    const VarType_ & var,
    Integer value) -> Inference
{
    GetMutableStateAndOffsetOf<VarType_> get_state{*this, var};

    return overloaded{
        [&](IntegerVariableConstantState & c) -> Inference {
            // Ok if the constant is greater or equal, otherwise contradiction
            return c.value >= value ? Inference::NoChange : Inference::Contradiction;
        },
        [&](IntegerVariableRangeState & rvar) -> Inference {
            if (rvar.lower < value) {
                rvar.lower = value;
                if (rvar.lower == rvar.upper) {
                    assign_to_state_of(var) = IntegerVariableConstantState{rvar.lower};
                    return Inference::Instantiated;
                }
                else if (rvar.lower > rvar.upper)
                    return Inference::Contradiction;
                else
                    return Inference::BoundsChanged;
            }
            return Inference::NoChange;
        },
        [&](IntegerVariableSmallSetState & svar) -> Inference {
            int last_bit_to_keep = (value - svar.lower).raw_value;
            if (last_bit_to_keep < 0)
                return Inference::NoChange;

            auto pc_before = svar.bits.popcount();

            int word_to_modify = last_bit_to_keep / Bits::bits_per_word;
            if (word_to_modify < Bits::n_words) {
                int inv_number_of_bits_to_keep = last_bit_to_keep % Bits::bits_per_word;
                Bits::BitWord mask = (Bits::BitWord{1} << inv_number_of_bits_to_keep) - 1;
                svar.bits.data[word_to_modify] &= ~mask;
                for (int w = 0; w < word_to_modify; ++w)
                    svar.bits.data[w] = 0;
            }
            else
                return Inference::NoChange;

            auto pc_after = svar.bits.popcount();
            if (pc_after == 0)
                return Inference::Contradiction;
            if (pc_after == 1) {
                assign_to_state_of(var) = IntegerVariableConstantState{svar.lower + Integer{svar.bits.countr_zero()}};
                return Inference::Instantiated;
            }
            return pc_before == pc_after ? Inference::NoChange : Inference::BoundsChanged;
        },
        [&](IntegerVariableIntervalSetState & svar) -> Inference {
            if (svar.values->lower() >= value)
                return Inference::NoChange;

            if (svar.values.use_count() != 1)
                svar.values = make_shared<IntervalSet<Integer>>(*svar.values);

            svar.values->erase_less_than(value);
            if (svar.values->empty())
                return Inference::Contradiction;
            else if (svar.values->lower() == svar.values->upper()) {
                assign_to_state_of(var) = IntegerVariableConstantState{svar.values->lower()};
                return Inference::Instantiated;
            }
            else
                return Inference::BoundsChanged;
        }}
        .visit(get_state.state);
}

auto State::infer(const Literal & lit) -> Inference
{
    return overloaded{
        [&](const IntegerVariableCondition & cond) -> Inference {
            return infer(cond);
        },
        [&](const TrueLiteral &) {
            return Inference::NoChange;
        },
        [&](const FalseLiteral &) {
            return Inference::Contradiction;
        }}
        .visit(lit);
}

template <IntegerVariableIDLike VarType_>
auto State::infer(const VariableConditionFrom<VarType_> & cond) -> Inference
{
    switch (cond.op) {
    case VariableConditionOperator::Equal:
        return infer_equal(cond.var, cond.value);
    case VariableConditionOperator::NotEqual:
        return infer_not_equal(cond.var, cond.value);
    case VariableConditionOperator::Less:
        return infer_less_than(cond.var, cond.value);
    case VariableConditionOperator::GreaterEqual:
        return infer_greater_than_or_equal(cond.var, cond.value);
    }
    throw NonExhaustiveSwitch{};
}

template <IntegerVariableIDLike VarType_>
auto State::infer_not_equal(const VarType_ & var, Integer value) -> Inference
{
    auto [actual_var, negate_first, then_add] = deview(var);
    return change_state_for_not_equal(actual_var, (negate_first ? -value + then_add : value - then_add));
}

template <IntegerVariableIDLike VarType_>
auto State::infer_equal(const VarType_ & var, Integer value) -> Inference
{
    auto [actual_var, negate_first, then_add] = deview(var);
    return change_state_for_equal(actual_var, (negate_first ? -value + then_add : value - then_add));
}

template <IntegerVariableIDLike VarType_>
auto State::infer_less_than(const VarType_ & var, Integer value) -> Inference
{
    auto [actual_var, negate_first, then_add] = deview(var);
    if (negate_first) {
        return change_state_for_greater_than_or_equal(actual_var, -value + then_add + 1_i);
    }
    else {
        return change_state_for_less_than(actual_var, value - then_add);
    }
}

template <IntegerVariableIDLike VarType_>
auto State::infer_greater_than_or_equal(const VarType_ & var, Integer value) -> Inference
{
    auto [actual_var, negate_first, then_add] = deview(var);
    if (negate_first) {
        return change_state_for_less_than(actual_var, -value + then_add + 1_i);
    }
    else {
        return change_state_for_greater_than_or_equal(actual_var, value - then_add);
    }
}

auto State::guess(const Literal & lit) -> void
{
    switch (infer(lit)) {
    case Inference::NoChange:
    case Inference::BoundsChanged:
    case Inference::InteriorValuesChanged:
    case Inference::Instantiated:
        _imp->guesses.push_back(lit);
        return;

    case Inference::Contradiction:
        throw UnexpectedException{"couldn't infer a branch variable"};
    }
}

auto State::add_extra_proof_condition(const Literal & lit) -> void
{
    _imp->extra_proof_conditions.push_back(lit);
}

auto State::lower_bound(const IntegerVariableID var) const -> Integer
{
    auto [actual_var, negate_first, then_add] = deview(var);
    IntegerVariableState space = IntegerVariableConstantState{0_i};

    if (negate_first) {
        return -overloaded{
                   [](const IntegerVariableRangeState & v) { return v.upper; },
                   [](const IntegerVariableConstantState & v) { return v.value; },
                   [](const IntegerVariableSmallSetState & v) { return v.lower + Integer{Bits::number_of_bits} - Integer{v.bits.countl_zero()} - 1_i; },
                   [](const IntegerVariableIntervalSetState & v) { return v.values->upper(); }}
                    .visit(state_of(actual_var, space)) +
            then_add;
    }
    else {
        return overloaded{
                   [](const IntegerVariableRangeState & v) { return v.lower; },
                   [](const IntegerVariableConstantState & v) { return v.value; },
                   [](const IntegerVariableSmallSetState & v) { return v.lower + Integer{v.bits.countr_zero()}; },
                   [](const IntegerVariableIntervalSetState & v) { return v.values->lower(); }}
                   .visit(state_of(actual_var, space)) +
            then_add;
    }
}

auto State::upper_bound(const IntegerVariableID var) const -> Integer
{
    auto [actual_var, negate_first, then_add] = deview(var);
    IntegerVariableState space = IntegerVariableConstantState{0_i};

    if (negate_first) {
        return -overloaded{
                   [](const IntegerVariableRangeState & v) { return v.lower; },
                   [](const IntegerVariableConstantState & v) { return v.value; },
                   [](const IntegerVariableSmallSetState & v) { return v.lower + Integer{v.bits.countr_zero()}; },
                   [](const IntegerVariableIntervalSetState & v) { return v.values->lower(); }}
                    .visit(state_of(actual_var, space)) +
            then_add;
    }
    else {
        return overloaded{
                   [](const IntegerVariableRangeState & v) { return v.upper; },
                   [](const IntegerVariableConstantState & v) { return v.value; },
                   [](const IntegerVariableSmallSetState & v) { return v.lower + Integer{Bits::number_of_bits} - Integer{v.bits.countl_zero()} - 1_i; },
                   [](const IntegerVariableIntervalSetState & v) { return v.values->upper(); }}
                   .visit(state_of(actual_var, space)) +
            then_add;
    }
}

template <IntegerVariableIDLike VarType_>
auto State::bounds(const VarType_ & var) const -> pair<Integer, Integer>
{
    GetStateAndOffsetOf<VarType_> get_state{*this, var};
    auto result = overloaded{
        [](const IntegerVariableRangeState & v) { return pair{v.lower, v.upper}; },
        [](const IntegerVariableConstantState & v) { return pair{v.value, v.value}; },
        [](const IntegerVariableSmallSetState & v) { return pair{
                                                         v.lower + Integer{v.bits.countr_zero()},
                                                         v.lower + Integer{Bits::number_of_bits} - Integer{v.bits.countl_zero()} - 1_i}; },
        [](const IntegerVariableIntervalSetState & v) { return pair{v.values->lower(), v.values->upper()}; }}
                      .visit(get_state.state);

    if (get<1>(get_state.var_negate_then_add))
        return pair{-result.second + get<2>(get_state.var_negate_then_add), -result.first + get<2>(get_state.var_negate_then_add)};
    else
        return pair{result.first + get<2>(get_state.var_negate_then_add), result.second + get<2>(get_state.var_negate_then_add)};
}

template <IntegerVariableIDLike VarType_>
auto State::in_domain(const VarType_ & var, const Integer val) const -> bool
{
    GetStateAndOffsetOf<VarType_> get_state{*this, var};
    auto actual_val = (get<1>(get_state.var_negate_then_add) ? -val + get<2>(get_state.var_negate_then_add) : val - get<2>(get_state.var_negate_then_add));
    return overloaded{
        [val = actual_val](const IntegerVariableRangeState & v) { return val >= v.lower && val <= v.upper; },
        [val = actual_val](const IntegerVariableConstantState & v) { return val == v.value; },
        [val = actual_val](const IntegerVariableSmallSetState & v) {
            if (val < v.lower || val > (v.lower + Integer{Bits::number_of_bits - 1}))
                return false;
            else
                return v.bits.test((val - v.lower).raw_value);
        },
        [val = actual_val](const IntegerVariableIntervalSetState & v) { return v.values->contains(val); }}
        .visit(get_state.state);
}

auto State::domain_has_holes(const IntegerVariableID var) const -> bool
{
    auto [actual_var, _1, _2] = deview(var);
    IntegerVariableState space = IntegerVariableConstantState{0_i};
    return overloaded{
        [](const IntegerVariableRangeState &) { return false; },
        [](const IntegerVariableConstantState &) { return false; },
        [](const IntegerVariableSmallSetState &) { return true; },
        [](const IntegerVariableIntervalSetState & v) { return v.values->has_holes(); }}
        .visit(state_of(actual_var, space));
}

template <IntegerVariableIDLike VarType_>
auto State::optional_single_value(const VarType_ & var) const -> optional<Integer>
{
    GetStateAndOffsetOf<VarType_> get_state{*this, var};
    auto result = overloaded{
        [](const IntegerVariableRangeState & v) -> optional<Integer> {
            if (v.lower == v.upper)
                return make_optional(v.lower);
            else
                return nullopt;
        },
        [](const IntegerVariableConstantState & v) -> optional<Integer> {
            return make_optional(v.value);
        },
        [](const IntegerVariableSmallSetState & v) -> optional<Integer> {
            if (v.bits.has_single_bit())
                return make_optional(v.lower + Integer{v.bits.countr_zero()});
            else
                return nullopt;
        },
        [](const IntegerVariableIntervalSetState & v) -> optional<Integer> {
            if (v.values->lower() == v.values->upper())
                return make_optional(v.values->lower());
            else
                return nullopt;
        }}.visit(get_state.state);

    if (result)
        return (get<1>(get_state.var_negate_then_add) ? -*result : *result) + get<2>(get_state.var_negate_then_add);
    else
        return result;
}

auto State::has_single_value(const IntegerVariableID var) const -> bool
{
    auto [actual_var, _1, _2] = deview(var);
    IntegerVariableState space = IntegerVariableConstantState{0_i};
    return overloaded{
        [](const IntegerVariableRangeState & v) -> bool { return v.lower == v.upper; },
        [](const IntegerVariableConstantState &) -> bool { return true; },
        [](const IntegerVariableSmallSetState & v) -> bool { return v.bits.has_single_bit(); },
        [](const IntegerVariableIntervalSetState & v) -> bool { return v.values->lower() == v.values->upper(); }}
        .visit(state_of(actual_var, space));
}

template <IntegerVariableIDLike VarType_>
auto State::domain_size(const VarType_ & var) const -> Integer
{
    GetStateAndOffsetOf<VarType_> get_state{*this, var};
    return overloaded{
        [](const IntegerVariableConstantState &) { return Integer{1}; },
        [](const IntegerVariableRangeState & r) { return r.upper - r.lower + Integer{1}; },
        [](const IntegerVariableSmallSetState & s) { return Integer{s.bits.popcount()}; },
        [](const IntegerVariableIntervalSetState & s) { return Integer(s.values->size()); }}
        .visit(get_state.state);
}

template <IntegerVariableIDLike VarType_>
auto State::for_each_value(const VarType_ & var, const function<auto(Integer)->void> & f) const -> void
{
    for_each_value_while(var, [&](Integer v) -> bool {
        f(v);
        return true;
    });
}

template <IntegerVariableIDLike VarType_>
auto State::for_each_value_immutable(const VarType_ & var, const function<auto(Integer)->void> & f) const -> void
{
    for_each_value_while_immutable(var, [&](Integer v) -> bool {
        f(v);
        return true;
    });
}

template <IntegerVariableIDLike VarType_>
auto State::for_each_value_while(const VarType_ & var, const function<auto(Integer)->bool> & f) const -> bool
{
    auto [actual_var, negate_first, then_add] = deview(var);

    GetStateAndOffsetOf<VarType_> get_state{*this, var};
    IntegerVariableState var_copy = get_state.state;

    auto apply = [negate_first = negate_first, then_add = then_add](Integer v) -> Integer {
        return (negate_first ? -v : v) + then_add;
    };

    bool result = true;

    overloaded{
        [&](const IntegerVariableConstantState & c) {
            f(apply(c.value));
        },
        [&](const IntegerVariableRangeState & r) {
            for (auto v = r.lower; v <= r.upper; ++v)
                if (! f(apply(v))) {
                    result = false;
                    break;
                }
        },
        [&](const IntegerVariableSmallSetState & r) {
            for (unsigned w = 0; w < Bits::n_words; ++w) {
                auto b = r.bits.data[w];
                while (true) {
                    int z = countr_zero(b);
                    if (z == Bits::bits_per_word)
                        break;
                    b &= ~(Bits::BitWord{1} << z);
                    if (! f(apply(r.lower + Integer{w * Bits::bits_per_word} + Integer{z}))) {
                        result = false;
                        break;
                    }
                }
            }
        },
        [&](const IntegerVariableIntervalSetState & s) {
            auto values = s.values;
            for (auto i : values->each())
                if (! f(apply(i))) {
                    result = false;
                    return;
                }
        }}
        .visit(var_copy);

    return result;
}

template <IntegerVariableIDLike VarType_>
auto State::for_each_value_while_immutable(const VarType_ & var, const function<auto(Integer)->bool> & f) const -> bool
{
    auto [actual_var, negate_first, then_add] = deview(var);

    auto apply = [&, negate_first = negate_first, then_add = then_add](Integer v) -> Integer {
        return (negate_first ? -v : v) + then_add;
    };

    GetStateAndOffsetOf<VarType_> get_state{*this, var};
    const IntegerVariableState & var_ref = get_state.state;

    bool result = true;

    overloaded{
        [&](const IntegerVariableConstantState & c) {
            f(apply(c.value));
        },
        [&](const IntegerVariableRangeState & r) {
            for (auto v = r.lower; v <= r.upper; ++v)
                if (! f(apply(v))) {
                    result = false;
                    break;
                }
        },
        [&](const IntegerVariableSmallSetState & r) {
            for (unsigned w = 0; w < Bits::n_words; ++w) {
                auto b = r.bits.data[w];
                while (true) {
                    int z = countr_zero(b);
                    if (z == Bits::bits_per_word)
                        break;
                    b &= ~(Bits::BitWord{1} << z);
                    if (! f(apply(r.lower + Integer{w * Bits::bits_per_word} + Integer{z}))) {
                        result = false;
                        break;
                    }
                }
            }
        },
        [&](const IntegerVariableIntervalSetState & s) {
            for (auto i : s.values->each())
                if (! f(apply(i))) {
                    result = false;
                    return;
                }
        }}
        .visit(var_ref);

    return result;
}

template <IntegerVariableIDLike VarType_>
auto State::copy_of_values(const VarType_ & var) const -> IntervalSet<Integer>
{
    GetStateAndOffsetOf<VarType_> get_state{*this, var};
    if ((! get<1>(get_state.var_negate_then_add)) && (0_i == get<2>(get_state.var_negate_then_add)) &&
        holds_alternative<IntegerVariableIntervalSetState>(get_state.state)) {
        return *get<IntegerVariableIntervalSetState>(get_state.state).values;
    }
    else if ((! get<1>(get_state.var_negate_then_add)) && (0_i == get<2>(get_state.var_negate_then_add)) &&
        holds_alternative<IntegerVariableRangeState>(get_state.state)) {
        IntervalSet<Integer> result;
        result.insert_at_end(
            get<IntegerVariableRangeState>(get_state.state).lower,
            get<IntegerVariableRangeState>(get_state.state).upper);
        return result;
    }
    else {
        IntervalSet<Integer> result;
        for_each_value_immutable(var, [&](Integer i) {
            result.insert_at_end(i);
        });
        return result;
    }
}

template <IntegerVariableIDLike VarType_>
auto State::each_value_immutable(const VarType_ & var) const -> generator<Integer>
{
    auto [actual_var, negate_first, then_add] = deview(var);

    auto apply = [negate_first = negate_first, then_add = then_add](Integer v) -> Integer {
        return (negate_first ? -v : v) + then_add;
    };

    GetStateAndOffsetOf<VarType_> get_state{*this, var};
    const IntegerVariableState & var_ref = get_state.state;

    return overloaded{
        [&](const IntegerVariableConstantState & c) {
            return [](const IntegerVariableConstantState & c, auto apply) -> generator<Integer> {
                co_yield apply(c.value);
            }(c, apply);
        },
        [&](const IntegerVariableRangeState & r) {
            return [](const IntegerVariableRangeState & r, auto apply) -> generator<Integer> {
                for (auto v = r.lower; v <= r.upper; ++v)
                    co_yield apply(v);
            }(r, apply);
        },
        [&](const IntegerVariableSmallSetState & r) {
            return [](const IntegerVariableSmallSetState & r, auto apply) -> generator<Integer> {
                for (unsigned w = 0; w < Bits::n_words; ++w) {
                    auto b = r.bits.data[w];
                    while (true) {
                        int z = countr_zero(b);
                        if (z == Bits::bits_per_word)
                            break;
                        b &= ~(Bits::BitWord{1} << z);
                        co_yield apply(r.lower + Integer{w * Bits::bits_per_word} + Integer{z});
                    }
                }
            }(r, apply);
        },
        [&](const IntegerVariableIntervalSetState & s) {
            return [](const IntegerVariableIntervalSetState & s, auto apply) -> generator<Integer> {
                for (auto i : s.values->each())
                    co_yield apply(i);
            }(s, apply);
        }}
        .visit(var_ref);
}

template <IntegerVariableIDLike VarType_>
auto State::each_value_mutable(const VarType_ & var) const -> generator<Integer>
{
    auto [actual_var, negate_first, then_add] = deview(var);

    GetStateAndOffsetOf<VarType_> get_state{*this, var};
    const IntegerVariableState & var_ref = get_state.state;

    auto apply = [negate_first = negate_first, then_add = then_add](Integer v) -> Integer {
        return (negate_first ? -v : v) + then_add;
    };

    return overloaded{
        [&](const IntegerVariableConstantState & c) {
            return [](IntegerVariableConstantState c, auto apply) -> generator<Integer> {
                co_yield apply(c.value);
            }(c, apply);
        },
        [&](const IntegerVariableRangeState & r) {
            return [](IntegerVariableRangeState r, auto apply) -> generator<Integer> {
                for (auto v = r.lower; v <= r.upper; ++v)
                    co_yield apply(v);
            }(r, apply);
        },
        [&](const IntegerVariableSmallSetState & r) {
            return [](IntegerVariableSmallSetState r, auto apply) -> generator<Integer> {
                for (unsigned w = 0; w < Bits::n_words; ++w) {
                    auto b = r.bits.data[w];
                    while (true) {
                        int z = countr_zero(b);
                        if (z == Bits::bits_per_word)
                            break;
                        b &= ~(Bits::BitWord{1} << z);
                        co_yield apply(r.lower + Integer{w * Bits::bits_per_word} + Integer{z});
                    }
                }
            }(r, apply);
        },
        [&](const IntegerVariableIntervalSetState s) {
            return [](IntegerVariableIntervalSetState s, auto apply) -> generator<Integer> {
                for (auto i : s.values->each())
                    co_yield apply(i);
            }(s, apply);
        }}
        .visit(var_ref);
}

auto State::operator()(const IntegerVariableID & i) const -> Integer
{
    if (auto result = optional_single_value(i))
        return *result;
    auto [actual_var, negate_first, then_add] = deview(i);
    IntegerVariableState space = IntegerVariableConstantState{0_i};
    throw VariableDoesNotHaveUniqueValue{"Integer variable " + visit([&](const auto & i) { return debug_string(i) + " " + debug_string(state_of(i, space)); }, actual_var)};
}

auto State::new_epoch(bool subsearch) -> Timestamp
{
    _imp->integer_variable_states.push_back(_imp->integer_variable_states.back());
    _imp->constraint_states.push_back(_imp->constraint_states.back());
    _imp->on_backtracks.emplace_back();

    return Timestamp{
        _imp->integer_variable_states.size() - 1,
        _imp->guesses.size(),
        subsearch ? make_optional<unsigned long long>(_imp->extra_proof_conditions.size()) : nullopt};
}

auto State::backtrack(Timestamp t) -> void
{
    _imp->integer_variable_states.resize(t.when);
    _imp->constraint_states.resize(t.when);
    _imp->guesses.erase(_imp->guesses.begin() + t.how_many_guesses, _imp->guesses.end());
    if (t.how_many_extra_proof_conditions)
        _imp->extra_proof_conditions.erase(_imp->extra_proof_conditions.begin() + *t.how_many_extra_proof_conditions,
            _imp->extra_proof_conditions.end());

    while (_imp->on_backtracks.size() > t.when) {
        for (auto & f : _imp->on_backtracks.back())
            f();
        _imp->on_backtracks.pop_back();
    }
}

auto State::guesses() const -> generator<Literal>
{
    return [] (const auto & extra_proof_conditions, const auto & guesses) -> generator<Literal> {
        for (auto & g : extra_proof_conditions)
            co_yield g;
        for (auto & g : guesses)
            co_yield g;
    }(_imp->extra_proof_conditions, _imp->guesses);
}

auto State::test_literal(const Literal & lit) const -> LiteralIs
{
    return overloaded{
        [&](const IntegerVariableCondition & cond) -> LiteralIs {
            return test_literal(cond);
        },
        [](const TrueLiteral &) { return LiteralIs::DefinitelyTrue; },
        [](const FalseLiteral &) { return LiteralIs::DefinitelyFalse; }}
        .visit(lit);
}

auto State::test_literal(const IntegerVariableCondition & cond) const -> LiteralIs
{
    switch (cond.op) {
    case VariableConditionOperator::Equal:
        if (! in_domain(cond.var, cond.value))
            return LiteralIs::DefinitelyFalse;
        else if (has_single_value(cond.var))
            return LiteralIs::DefinitelyTrue;
        else
            return LiteralIs::Undecided;

    case VariableConditionOperator::Less:
        if (lower_bound(cond.var) < cond.value) {
            if (upper_bound(cond.var) < cond.value)
                return LiteralIs::DefinitelyTrue;
            else
                return LiteralIs::Undecided;
        }
        else
            return LiteralIs::DefinitelyFalse;

    case VariableConditionOperator::GreaterEqual:
        if (upper_bound(cond.var) >= cond.value) {
            if (lower_bound(cond.var) >= cond.value)
                return LiteralIs::DefinitelyTrue;
            else
                return LiteralIs::Undecided;
        }
        else
            return LiteralIs::DefinitelyFalse;

    case VariableConditionOperator::NotEqual:
        if (! in_domain(cond.var, cond.value))
            return LiteralIs::DefinitelyTrue;
        else if (has_single_value(cond.var))
            return LiteralIs::DefinitelyFalse;
        else
            return LiteralIs::Undecided;
    }

    throw NonExhaustiveSwitch{};
}

auto State::on_backtrack(std::function<auto()->void> f) -> void
{
    _imp->on_backtracks.back().push_back(move(f));
}

auto State::current() -> CurrentState
{
    return CurrentState{*this};
}

auto innards::State::add_constraint_state(const ConstraintState c) -> ConstraintStateHandle
{
    // Copying because I'm not sure if making it a reference is a bad idea... (want it to persist)
    _imp->constraint_states.back().push_back(c);
    return ConstraintStateHandle(_imp->constraint_states.back().size() - 1);
}

auto innards::State::add_persistent_constraint_state(const ConstraintState c) -> ConstraintStateHandle
{
    // Does not restore on backtracking
    _imp->persistent_constraint_states.push_back(c);
    return ConstraintStateHandle(_imp->persistent_constraint_states.size() - 1);
}

auto innards::State::get_constraint_state(const ConstraintStateHandle h) const -> ConstraintState &
{
    return _imp->constraint_states.back()[h.index];
}

auto innards::State::get_persistent_constraint_state(const ConstraintStateHandle h) const -> ConstraintState &
{
    return _imp->persistent_constraint_states[h.index];
}

namespace gcs
{
    template auto State::in_domain(const IntegerVariableID &, Integer) const -> bool;
    template auto State::in_domain(const SimpleIntegerVariableID &, Integer) const -> bool;
    template auto State::in_domain(const ViewOfIntegerVariableID &, Integer) const -> bool;
    template auto State::in_domain(const ConstantIntegerVariableID &, Integer) const -> bool;

    template auto State::optional_single_value(const IntegerVariableID &) const -> optional<Integer>;
    template auto State::optional_single_value(const SimpleIntegerVariableID &) const -> optional<Integer>;
    template auto State::optional_single_value(const ViewOfIntegerVariableID &) const -> optional<Integer>;
    template auto State::optional_single_value(const ConstantIntegerVariableID &) const -> optional<Integer>;

    template auto State::bounds(const IntegerVariableID & var) const -> pair<Integer, Integer>;
    template auto State::bounds(const SimpleIntegerVariableID & var) const -> pair<Integer, Integer>;
    template auto State::bounds(const ViewOfIntegerVariableID & var) const -> pair<Integer, Integer>;
    template auto State::bounds(const ConstantIntegerVariableID & var) const -> pair<Integer, Integer>;

    template auto State::domain_size(const IntegerVariableID &) const -> Integer;
    template auto State::domain_size(const SimpleIntegerVariableID &) const -> Integer;

    template auto State::for_each_value(const IntegerVariableID &, const std::function<auto(Integer)->void> &) const -> void;
    template auto State::for_each_value(const SimpleIntegerVariableID &, const std::function<auto(Integer)->void> &) const -> void;
    template auto State::for_each_value(const ViewOfIntegerVariableID &, const std::function<auto(Integer)->void> &) const -> void;
    template auto State::for_each_value(const ConstantIntegerVariableID &, const std::function<auto(Integer)->void> &) const -> void;

    template auto State::for_each_value_immutable(const IntegerVariableID &, const std::function<auto(Integer)->void> &) const -> void;
    template auto State::for_each_value_immutable(const SimpleIntegerVariableID &, const std::function<auto(Integer)->void> &) const -> void;
    template auto State::for_each_value_immutable(const ViewOfIntegerVariableID &, const std::function<auto(Integer)->void> &) const -> void;
    template auto State::for_each_value_immutable(const ConstantIntegerVariableID &, const std::function<auto(Integer)->void> &) const -> void;

    template auto State::for_each_value_while(const IntegerVariableID &, const std::function<auto(Integer)->bool> &) const -> bool;
    template auto State::for_each_value_while(const SimpleIntegerVariableID &, const std::function<auto(Integer)->bool> &) const -> bool;
    template auto State::for_each_value_while(const ViewOfIntegerVariableID &, const std::function<auto(Integer)->bool> &) const -> bool;
    template auto State::for_each_value_while(const ConstantIntegerVariableID &, const std::function<auto(Integer)->bool> &) const -> bool;

    template auto State::for_each_value_while_immutable(const IntegerVariableID &, const std::function<auto(Integer)->bool> &) const -> bool;
    template auto State::for_each_value_while_immutable(const SimpleIntegerVariableID &, const std::function<auto(Integer)->bool> &) const -> bool;
    template auto State::for_each_value_while_immutable(const ViewOfIntegerVariableID &, const std::function<auto(Integer)->bool> &) const -> bool;
    template auto State::for_each_value_while_immutable(const ConstantIntegerVariableID &, const std::function<auto(Integer)->bool> &) const -> bool;

    template auto State::each_value_immutable(const IntegerVariableID &) const -> generator<Integer>;
    template auto State::each_value_immutable(const SimpleIntegerVariableID &) const -> generator<Integer>;
    template auto State::each_value_immutable(const ViewOfIntegerVariableID &) const -> generator<Integer>;
    template auto State::each_value_immutable(const ConstantIntegerVariableID &) const -> generator<Integer>;

    template auto State::each_value_mutable(const IntegerVariableID &) const -> generator<Integer>;
    template auto State::each_value_mutable(const SimpleIntegerVariableID &) const -> generator<Integer>;
    template auto State::each_value_mutable(const ViewOfIntegerVariableID &) const -> generator<Integer>;
    template auto State::each_value_mutable(const ConstantIntegerVariableID &) const -> generator<Integer>;

    template auto State::copy_of_values(const IntegerVariableID &) const -> IntervalSet<Integer>;
    template auto State::copy_of_values(const SimpleIntegerVariableID &) const -> IntervalSet<Integer>;
    template auto State::copy_of_values(const ViewOfIntegerVariableID &) const -> IntervalSet<Integer>;
    template auto State::copy_of_values(const ConstantIntegerVariableID &) const -> IntervalSet<Integer>;

    template auto State::infer(const VariableConditionFrom<IntegerVariableID> &) -> Inference;
    template auto State::infer(const VariableConditionFrom<SimpleIntegerVariableID> &) -> Inference;
    template auto State::infer(const VariableConditionFrom<ViewOfIntegerVariableID> &) -> Inference;
    template auto State::infer(const VariableConditionFrom<ConstantIntegerVariableID> &) -> Inference;

    template auto State::infer_equal(const IntegerVariableID &, Integer) -> Inference;
    template auto State::infer_equal(const SimpleIntegerVariableID &, Integer) -> Inference;
    template auto State::infer_equal(const ViewOfIntegerVariableID &, Integer) -> Inference;
    template auto State::infer_equal(const ConstantIntegerVariableID &, Integer) -> Inference;

    template auto State::infer_not_equal(const IntegerVariableID &, Integer) -> Inference;
    template auto State::infer_not_equal(const SimpleIntegerVariableID &, Integer) -> Inference;
    template auto State::infer_not_equal(const ViewOfIntegerVariableID &, Integer) -> Inference;
    template auto State::infer_not_equal(const ConstantIntegerVariableID &, Integer) -> Inference;

    template auto State::infer_less_than(const IntegerVariableID &, Integer) -> Inference;
    template auto State::infer_less_than(const SimpleIntegerVariableID &, Integer) -> Inference;
    template auto State::infer_less_than(const ViewOfIntegerVariableID &, Integer) -> Inference;
    template auto State::infer_less_than(const ConstantIntegerVariableID &, Integer) -> Inference;

    template auto State::infer_greater_than_or_equal(const IntegerVariableID &, Integer) -> Inference;
    template auto State::infer_greater_than_or_equal(const SimpleIntegerVariableID &, Integer) -> Inference;
    template auto State::infer_greater_than_or_equal(const ViewOfIntegerVariableID &, Integer) -> Inference;
    template auto State::infer_greater_than_or_equal(const ConstantIntegerVariableID &, Integer) -> Inference;
}
