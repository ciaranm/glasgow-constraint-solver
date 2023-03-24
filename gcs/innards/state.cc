#include <gcs/exception.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/state.hh>
#include <gcs/innards/variable_id_utils.hh>
#include <gcs/problem.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <bit>
#include <deque>
#include <list>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::countr_zero;
using std::decay_t;
using std::deque;
using std::function;
using std::get;
using std::is_same_v;
using std::list;
using std::make_optional;
using std::make_shared;
using std::max;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::tuple;
using std::vector;
using std::visit;

auto gcs::innards::increase_inference_to(Inference & current, const Inference updated) -> void
{
    switch (updated) {
    case Inference::NoChange: break;
    case Inference::Change:
        if (current != Inference::Contradiction)
            current = updated;
        break;
    case Inference::Contradiction:
        current = updated;
        break;
    }
}

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
    Proof * maybe_proof;

    list<vector<IntegerVariableState>> integer_variable_states{};
    list<vector<ConstraintState>> constraint_states{};
    list<vector<function<auto()->void>>> on_backtracks{};
    vector<HowChanged> how_changed{};
    deque<SimpleIntegerVariableID> changed{};
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
    result._imp->on_backtracks = _imp->on_backtracks;
    result._imp->changed = _imp->changed;
    result._imp->optional_minimise_variable = _imp->optional_minimise_variable;
    result._imp->optional_objective_incumbent = _imp->optional_objective_incumbent;
    result._imp->maybe_proof = _imp->maybe_proof;
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
    Integer value) -> pair<Inference, HowChanged>
{
    GetMutableStateAndOffsetOf<VarType_> get_state{*this, var};

    // Has to be equal. If the value isn't in the domain, we've found a
    // contradiction, otherwise update to a constant value.
    return overloaded{
        [&](IntegerVariableConstantState & c) -> pair<Inference, HowChanged> {
            if (c.value == value)
                return pair{Inference::NoChange, HowChanged::Dummy};
            else
                return pair{Inference::Contradiction, HowChanged::Dummy};
        },
        [&](IntegerVariableRangeState & rvar) -> pair<Inference, HowChanged> {
            if (value < rvar.lower || value > rvar.upper)
                return pair{Inference::Contradiction, HowChanged::Dummy};
            else if (rvar.lower == rvar.upper && rvar.lower == value) {
                assign_to_state_of(var) = IntegerVariableConstantState{value};
                return pair{Inference::NoChange, HowChanged::Dummy};
            }
            else {
                assign_to_state_of(var) = IntegerVariableConstantState{value};
                return pair{Inference::Change, HowChanged::Instantiated};
            }
        },
        [&](IntegerVariableSmallSetState & svar) -> pair<Inference, HowChanged> {
            if (value < svar.lower || value > (svar.lower + Integer{Bits::number_of_bits - 1})) {
                return pair{Inference::Contradiction, HowChanged::Dummy};
            }
            else if (! svar.bits.test((value - svar.lower).raw_value)) {
                return pair{Inference::Contradiction, HowChanged::Dummy};
            }
            else if (svar.bits.popcount() == 1) {
                assign_to_state_of(var) = IntegerVariableConstantState{value};
                return pair{Inference::NoChange, HowChanged::Dummy};
            }
            else {
                assign_to_state_of(var) = IntegerVariableConstantState{value};
                return pair{Inference::Change, HowChanged::Instantiated};
            }
        },
        [&](IntegerVariableSetState & svar) -> pair<Inference, HowChanged> {
            if (svar.values->contains(value)) {
                if (svar.values->size() == 1) {
                    assign_to_state_of(var) = IntegerVariableConstantState{value};
                    return pair{Inference::NoChange, HowChanged::Dummy};
                }
                else {
                    assign_to_state_of(var) = IntegerVariableConstantState{value};
                    return pair{Inference::Change, HowChanged::Instantiated};
                }
            }
            else
                return pair{Inference::Contradiction, HowChanged::Dummy};
        }}
        .visit(get_state.state);
}

template <DirectIntegerVariableIDLike VarType_>
auto State::change_state_for_not_equal(
    const VarType_ & var,
    Integer value) -> pair<Inference, HowChanged>
{
    GetMutableStateAndOffsetOf<VarType_> get_state{*this, var};

    return overloaded{
        [&](IntegerVariableConstantState & cvar) -> pair<Inference, HowChanged> {
            // Constant equal to the value, potential problem!
            return cvar.value != value
                ? pair{Inference::NoChange, HowChanged::Dummy}
                : pair{Inference::Contradiction, HowChanged::Dummy};
        },
        [&](IntegerVariableRangeState & rvar) -> pair<Inference, HowChanged> {
            if (value < rvar.lower || value > rvar.upper) {
                // not in the domain, no problem
                return pair{Inference::NoChange, HowChanged::Dummy};
            }
            else if (rvar.lower == rvar.upper) {
                // Constant equal to the value, problem!
                return pair{Inference::Contradiction, HowChanged::Dummy};
            }
            else if (rvar.lower == value) {
                // Can just bump the bound
                ++rvar.lower;
                if (rvar.lower == rvar.upper) {
                    assign_to_state_of(var) = IntegerVariableConstantState{rvar.lower};
                    return pair{Inference::Change, HowChanged::Instantiated};
                }
                else
                    return pair{Inference::Change, HowChanged::BoundsChanged};
            }
            else if (rvar.upper == value) {
                --rvar.upper;

                if (rvar.lower == rvar.upper) {
                    assign_to_state_of(var) = IntegerVariableConstantState{rvar.lower};
                    return pair{Inference::Change, HowChanged::Instantiated};
                }
                else
                    return pair{Inference::Change, HowChanged::BoundsChanged};
            }
            else {
                // Holey domain, convert to set. This should handle offsets...
                if (rvar.lower < 0_i || rvar.upper >= Integer{Bits::number_of_bits}) {
                    auto values = make_shared<set<Integer>>();
                    for (Integer v = rvar.lower; v <= rvar.upper; ++v)
                        if (v != value)
                            values->insert(v);
                    assign_to_state_of(var) = IntegerVariableSetState{values};
                }
                else {
                    IntegerVariableSmallSetState svar{Integer{0}, Bits{}};
                    for (Integer v = rvar.lower; v <= rvar.upper; ++v)
                        if (v != value)
                            svar.bits.set(v.raw_value);
                    assign_to_state_of(var) = move(svar);
                }
                return pair{Inference::Change, HowChanged::InteriorValuesChanged};
            }
        },
        [&](IntegerVariableSmallSetState & svar) -> pair<Inference, HowChanged> {
            if (value < svar.lower || value > (svar.lower + Integer{Bits::number_of_bits - 1})) {
                // out of bounds, not in domain
                return pair{Inference::NoChange, HowChanged::Dummy};
            }
            else if (! svar.bits.test((value - svar.lower).raw_value)) {
                // not in domain, no problem
                return pair{Inference::NoChange, HowChanged::Dummy};
            }

            // Knock out the value
            bool is_bound = (value == svar.lower + Integer{svar.bits.countr_zero()}) ||
                (value == svar.lower + Integer{Bits::number_of_bits} - Integer{svar.bits.countl_zero()} - 1_i);
            svar.bits.reset((value - svar.lower).raw_value);
            if (svar.bits.has_single_bit()) {
                assign_to_state_of(var) = IntegerVariableConstantState{svar.lower + Integer{svar.bits.countr_zero()}};
                return pair{Inference::Change, HowChanged::Instantiated};
            }
            else if (svar.bits.none())
                return pair{Inference::Contradiction, HowChanged::Dummy};
            else if (is_bound)
                return pair{Inference::Change, HowChanged::BoundsChanged};
            else
                return pair{Inference::Change, HowChanged::InteriorValuesChanged};
        },
        [&](IntegerVariableSetState & svar) -> pair<Inference, HowChanged> {
            if (! svar.values->contains(value))
                return pair{Inference::NoChange, HowChanged::Dummy};

            // Knock out the value
            bool is_bound = (value == *svar.values->begin() || value == *svar.values->rbegin());
            if (1 == svar.values->size())
                return pair{Inference::Contradiction, HowChanged::Dummy};
            else if (2 == svar.values->size()) {
                assign_to_state_of(var) = IntegerVariableConstantState{
                    value == *svar.values->begin() ? *next(svar.values->begin()) : *svar.values->begin()};
                return pair{Inference::Change, HowChanged::Instantiated};
            }
            else if (svar.values.unique()) {
                svar.values->erase(value);
                return pair{Inference::Change, is_bound ? HowChanged::BoundsChanged : HowChanged::InteriorValuesChanged};
            }
            else {
                auto new_values = make_shared<set<Integer>>(*svar.values);
                new_values->erase(value);
                svar.values = new_values;
                return pair{Inference::Change, is_bound ? HowChanged::BoundsChanged : HowChanged::InteriorValuesChanged};
            }
        }}
        .visit(get_state.state);
}

template <DirectIntegerVariableIDLike VarType_>
auto State::change_state_for_less_than(
    const VarType_ & var,
    Integer value) -> pair<Inference, HowChanged>
{
    GetMutableStateAndOffsetOf<VarType_> get_state{*this, var};

    return overloaded{
        [&](IntegerVariableConstantState & c) -> pair<Inference, HowChanged> {
            // Ok if the constant is less, otherwise contradiction
            return pair{c.value < value ? Inference::NoChange : Inference::Contradiction, HowChanged::Dummy};
        },
        [&](IntegerVariableRangeState & rvar) -> pair<Inference, HowChanged> {
            if (rvar.upper >= value) {
                rvar.upper = value - 1_i;
                if (rvar.lower == rvar.upper) {
                    assign_to_state_of(var) = IntegerVariableConstantState{rvar.lower};
                    return pair{Inference::Change, HowChanged::Instantiated};
                }
                else if (rvar.lower > rvar.upper)
                    return pair{Inference::Contradiction, HowChanged::Dummy};
                else
                    return pair{Inference::Change, HowChanged::BoundsChanged};
            }
            else
                return pair{Inference::NoChange, HowChanged::Dummy};
        },
        [&](IntegerVariableSmallSetState & svar) -> pair<Inference, HowChanged> {
            auto pc_before = svar.bits.popcount();

            int first_bit_to_clear = (value - svar.lower).raw_value;
            if (first_bit_to_clear < 0)
                return pair{Inference::Contradiction, HowChanged::Dummy};

            int word_to_modify = first_bit_to_clear / Bits::bits_per_word;
            if (word_to_modify < Bits::n_words) {
                int number_of_bits_to_keep = first_bit_to_clear % Bits::bits_per_word;
                Bits::BitWord mask = (Bits::BitWord{1} << number_of_bits_to_keep) - 1;
                svar.bits.data[word_to_modify] &= mask;
                for (int w = word_to_modify + 1; w < Bits::n_words; ++w)
                    svar.bits.data[w] = 0;
            }
            else
                return pair{Inference::NoChange, HowChanged::Dummy};

            auto pc_after = svar.bits.popcount();
            if (pc_after == 0)
                return pair{Inference::Contradiction, HowChanged::Dummy};
            if (pc_after == 1) {
                assign_to_state_of(var) = IntegerVariableConstantState{svar.lower + Integer{svar.bits.countr_zero()}};
                return pair{Inference::Change, HowChanged::Instantiated};
            }
            return pc_before == pc_after ? pair{Inference::NoChange, HowChanged::Dummy} : pair{Inference::Change, HowChanged::BoundsChanged};
        },
        [&](IntegerVariableSetState & svar) -> pair<Inference, HowChanged> {
            // This should also be much smarter...
            auto erase_from = svar.values->upper_bound(value - 1_i);
            if (erase_from == svar.values->end())
                return pair{Inference::NoChange, HowChanged::Dummy};

            if (! svar.values.unique()) {
                svar.values = make_shared<set<Integer>>(*svar.values);
                erase_from = svar.values->upper_bound(value - 1_i);
            }

            svar.values->erase(erase_from, svar.values->end());
            if (svar.values->size() == 0)
                return pair{Inference::Contradiction, HowChanged::Dummy};
            else if (svar.values->size() == 1) {
                assign_to_state_of(var) = IntegerVariableConstantState{*svar.values->begin()};
                return pair{Inference::Change, HowChanged::Instantiated};
            }
            else
                return pair{Inference::Change, HowChanged::BoundsChanged};
        }}
        .visit(get_state.state);
}

template <DirectIntegerVariableIDLike VarType_>
auto State::change_state_for_greater_than_or_equal(
    const VarType_ & var,
    Integer value) -> pair<Inference, HowChanged>
{
    GetMutableStateAndOffsetOf<VarType_> get_state{*this, var};

    return overloaded{
        [&](IntegerVariableConstantState & c) -> pair<Inference, HowChanged> {
            // Ok if the constant is greater or equal, otherwise contradiction
            return pair{c.value >= value ? Inference::NoChange : Inference::Contradiction, HowChanged::Dummy};
        },
        [&](IntegerVariableRangeState & rvar) -> pair<Inference, HowChanged> {
            if (rvar.lower < value) {
                rvar.lower = value;
                if (rvar.lower == rvar.upper) {
                    assign_to_state_of(var) = IntegerVariableConstantState{rvar.lower};
                    return pair{Inference::Change, HowChanged::Instantiated};
                }
                else if (rvar.lower > rvar.upper)
                    return pair{Inference::Contradiction, HowChanged::Dummy};
                else
                    return pair{Inference::Change, HowChanged::BoundsChanged};
            }
            return pair{Inference::NoChange, HowChanged::Dummy};
        },
        [&](IntegerVariableSmallSetState & svar) -> pair<Inference, HowChanged> {
            int last_bit_to_keep = (value - svar.lower).raw_value;
            if (last_bit_to_keep < 0)
                return pair{Inference::Contradiction, HowChanged::Dummy};

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
                return pair{Inference::NoChange, HowChanged::Dummy};

            auto pc_after = svar.bits.popcount();
            if (pc_after == 0)
                return pair{Inference::Contradiction, HowChanged::Dummy};
            if (pc_after == 1) {
                assign_to_state_of(var) = IntegerVariableConstantState{svar.lower + Integer{svar.bits.countr_zero()}};
                return pair{Inference::Change, HowChanged::Instantiated};
            }
            return pc_before == pc_after ? pair{Inference::NoChange, HowChanged::Dummy} : pair{Inference::Change, HowChanged::BoundsChanged};
        },
        [&](IntegerVariableSetState & svar) -> pair<Inference, HowChanged> {
            // This should also be much smarter...
            auto erase_to = svar.values->lower_bound(value);
            if (erase_to == svar.values->begin())
                return pair{Inference::NoChange, HowChanged::Dummy};

            if (! svar.values.unique()) {
                svar.values = make_shared<set<Integer>>(*svar.values);
                erase_to = svar.values->lower_bound(value);
            }

            svar.values->erase(svar.values->begin(), erase_to);
            if (svar.values->size() == 0)
                return pair{Inference::Contradiction, HowChanged::Dummy};
            else if (svar.values->size() == 1) {
                assign_to_state_of(var) = IntegerVariableConstantState{*svar.values->begin()};
                return pair{Inference::Change, HowChanged::Instantiated};
            }
            else
                return pair{Inference::Change, HowChanged::BoundsChanged};
        }}
        .visit(get_state.state);
}

auto State::prove_and_remember_change(const Inference & inference, const HowChanged & how_changed, const Justification & just,
    const Literal & lit, const DirectIntegerVariableID & actual_var) -> void
{
    switch (inference) {
    case Inference::NoChange:
        break;

    case Inference::Contradiction:
        if (_imp->maybe_proof)
            _imp->maybe_proof->infer(*this, FalseLiteral{}, just);
        break;

    case Inference::Change: {
        // we know now that the variable definitely isn't a constant
        auto simple_var = get<SimpleIntegerVariableID>(actual_var);

        if (_imp->how_changed.size() <= simple_var.index)
            _imp->how_changed.resize(simple_var.index + 1, HowChanged::Dummy);

        if (_imp->how_changed[simple_var.index] == HowChanged::Dummy)
            _imp->changed.push_back(simple_var);

        _imp->how_changed[simple_var.index] = max<HowChanged>(_imp->how_changed[simple_var.index], how_changed);

        if (_imp->maybe_proof)
            _imp->maybe_proof->infer(*this, lit, just);
        break;
    }
    }
}

auto State::infer(const Literal & lit, const Justification & just) -> Inference
{
    return overloaded{
        [&](const LiteralFromIntegerVariable & ilit) -> Inference {
            return infer(ilit, just);
        },
        [&](const TrueLiteral &) {
            if (_imp->maybe_proof)
                _imp->maybe_proof->infer(*this, TrueLiteral{}, just);
            return Inference::NoChange;
        },
        [&](const FalseLiteral &) {
            if (_imp->maybe_proof)
                _imp->maybe_proof->infer(*this, FalseLiteral{}, just);
            return Inference::Contradiction;
        }}
        .visit(lit);
}

auto State::infer(const LiteralFromIntegerVariable & ilit, const Justification & just) -> Inference
{
    switch (ilit.op) {
    case LiteralFromIntegerVariable::Operator::Equal:
        return infer_equal(ilit.var, ilit.value, just);
    case LiteralFromIntegerVariable::Operator::NotEqual:
        return infer_not_equal(ilit.var, ilit.value, just);
    case LiteralFromIntegerVariable::Operator::Less:
        return infer_less_than(ilit.var, ilit.value, just);
    case LiteralFromIntegerVariable::Operator::GreaterEqual:
        return infer_greater_than_or_equal(ilit.var, ilit.value, just);
    }
    throw NonExhaustiveSwitch{};
}

auto State::infer_true(const Justification & just) -> void
{
    if (_imp->maybe_proof)
        _imp->maybe_proof->infer(*this, TrueLiteral{}, just);
}

template <IntegerVariableIDLike VarType_>
auto State::infer_not_equal(const VarType_ & var, Integer value, const Justification & just) -> Inference
{
    auto [actual_var, negate_first, then_add] = deview(var);
    auto [inference, how_changed] = change_state_for_not_equal(actual_var, (negate_first ? -value + then_add : value - then_add));
    prove_and_remember_change(inference, how_changed, just, var != value, actual_var);
    return inference;
}

template <IntegerVariableIDLike VarType_>
auto State::infer_equal(const VarType_ & var, Integer value, const Justification & just) -> Inference
{
    auto [actual_var, negate_first, then_add] = deview(var);
    auto [inference, how_changed] = change_state_for_equal(actual_var, (negate_first ? -value + then_add : value - then_add));
    prove_and_remember_change(inference, how_changed, just, var == value, actual_var);
    return inference;
}

template <IntegerVariableIDLike VarType_>
auto State::infer_less_than(const VarType_ & var, Integer value, const Justification & just) -> Inference
{
    auto [actual_var, negate_first, then_add] = deview(var);
    if (negate_first) {
        auto [inference, how_changed] = change_state_for_greater_than_or_equal(actual_var, -value + then_add + 1_i);
        prove_and_remember_change(inference, how_changed, just, var < value, actual_var);
        return inference;
    }
    else {
        auto [inference, how_changed] = change_state_for_less_than(actual_var, value - then_add);
        prove_and_remember_change(inference, how_changed, just, var < value, actual_var);
        return inference;
    }
}

template <IntegerVariableIDLike VarType_>
auto State::infer_greater_than_or_equal(const VarType_ & var, Integer value, const Justification & just) -> Inference
{
    auto [actual_var, negate_first, then_add] = deview(var);
    if (negate_first) {
        auto [inference, how_changed] = change_state_for_less_than(actual_var, -value + then_add + 1_i);
        prove_and_remember_change(inference, how_changed, just, var >= value, actual_var);
        return inference;
    }
    else {
        auto [inference, how_changed] = change_state_for_greater_than_or_equal(actual_var, value - then_add);
        prove_and_remember_change(inference, how_changed, just, var >= value, actual_var);
        return inference;
    }
}

auto State::infer_all(const vector<Literal> & lits, const Justification & just) -> Inference
{
    bool first = true;

    // only do explicit justifications once
    Justification just_not_first{NoJustificationNeeded{}};
    if (_imp->maybe_proof)
        visit([&](const auto & j) -> void {
            if constexpr (is_same_v<decay_t<decltype(j)>, JustifyExplicitly>)
                just_not_first = JustifyUsingRUP{};
            else
                just_not_first = just;
        },
            just);

    Inference result = Inference::NoChange;
    for (const auto & lit : lits) {
        switch (first ? infer(lit, just) : infer(lit, just_not_first)) {
        case Inference::NoChange:
            break;
        case Inference::Change:
            result = Inference::Change;
            break;
        case Inference::Contradiction:
            return Inference::Contradiction;
        }
        first = false;
    }

    return result;
}

auto State::guess(const Literal & lit) -> void
{
    if (_imp->maybe_proof)
        _imp->maybe_proof->new_guess();

    switch (infer(lit, Guess{})) {
    case Inference::NoChange:
    case Inference::Change:
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
                   [](const IntegerVariableSetState & v) { return *v.values->rbegin(); }}
                    .visit(state_of(actual_var, space)) +
            then_add;
    }
    else {
        return overloaded{
                   [](const IntegerVariableRangeState & v) { return v.lower; },
                   [](const IntegerVariableConstantState & v) { return v.value; },
                   [](const IntegerVariableSmallSetState & v) { return v.lower + Integer{v.bits.countr_zero()}; },
                   [](const IntegerVariableSetState & v) { return *v.values->begin(); }}
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
                   [](const IntegerVariableSetState & v) { return *v.values->begin(); }}
                    .visit(state_of(actual_var, space)) +
            then_add;
    }
    else {
        return overloaded{
                   [](const IntegerVariableRangeState & v) { return v.upper; },
                   [](const IntegerVariableConstantState & v) { return v.value; },
                   [](const IntegerVariableSmallSetState & v) { return v.lower + Integer{Bits::number_of_bits} - Integer{v.bits.countl_zero()} - 1_i; },
                   [](const IntegerVariableSetState & v) { return *v.values->rbegin(); }}
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
        [](const IntegerVariableSetState & v) { return pair{*v.values->begin(), *v.values->rbegin()}; }}
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
        [val = actual_val](const IntegerVariableSetState & v) { return v.values->end() != v.values->find(val); }}
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
        [](const IntegerVariableSetState &) { return true; }}
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
        [](const IntegerVariableSetState & v) -> optional<Integer> {
            if (1 == v.values->size())
                return make_optional(*v.values->begin());
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
        [](const IntegerVariableSetState & v) -> bool { return 1 == v.values->size(); }}
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
        [](const IntegerVariableSetState & s) { return Integer(s.values->size()); }}
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
        [&](const IntegerVariableSetState & s) {
            for (const auto & v : *s.values)
                if (! f(apply(v))) {
                    result = false;
                    break;
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
        [&](const IntegerVariableSetState & s) {
            for (const auto & v : *s.values)
                if (! f(apply(v))) {
                    result = false;
                    break;
                }
        }}
        .visit(var_ref);

    return result;
}

auto State::operator()(const IntegerVariableID & i) const -> Integer
{
    if (auto result = optional_single_value(i))
        return *result;
    throw VariableDoesNotHaveUniqueValue{"Integer variable " + debug_string(i)};
}

auto State::new_epoch(bool subsearch) -> Timestamp
{
    if (! _imp->changed.empty())
        throw UnimplementedException{};

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
    if (_imp->maybe_proof)
        _imp->maybe_proof->undo_guess();

    _imp->integer_variable_states.resize(t.when);
    _imp->constraint_states.resize(t.when);
    _imp->changed.clear();
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

auto State::extract_changed_variables(const function<auto(SimpleIntegerVariableID, HowChanged)->void> & f) -> void
{
    for (auto & c : _imp->changed)
        f(c, _imp->how_changed[c.index]);
    _imp->changed.clear();
    fill(_imp->how_changed.begin(), _imp->how_changed.end(), HowChanged::Dummy);
}

auto State::for_each_guess(const function<auto(Literal)->void> & f) const -> void
{
    for (auto & g : _imp->extra_proof_conditions)
        f(g);
    for (auto & g : _imp->guesses)
        f(g);
}

auto State::maybe_proof() const -> Proof *
{
    return _imp->maybe_proof;
}

auto State::log_inferences_to(Proof & p) -> void
{
    _imp->maybe_proof = &p;
}

auto State::add_proof_steps(JustifyExplicitly why) -> void
{
    if (_imp->maybe_proof) {
        vector<ProofLine> to_delete;
        _imp->maybe_proof->add_proof_steps(why, to_delete);
        _imp->maybe_proof->delete_proof_lines(to_delete);
    }
}

auto State::test_literal(const Literal & lit) const -> LiteralIs
{
    return overloaded{
        [&](const LiteralFromIntegerVariable & ilit) -> LiteralIs {
            return test_literal(ilit);
        },
        [](const TrueLiteral &) { return LiteralIs::DefinitelyTrue; },
        [](const FalseLiteral &) { return LiteralIs::DefinitelyFalse; }}
        .visit(lit);
}

auto State::test_literal(const LiteralFromIntegerVariable & ilit) const -> LiteralIs
{
    switch (ilit.op) {
    case LiteralFromIntegerVariable::Operator::Equal:
        if (! in_domain(ilit.var, ilit.value))
            return LiteralIs::DefinitelyFalse;
        else if (has_single_value(ilit.var))
            return LiteralIs::DefinitelyTrue;
        else
            return LiteralIs::Undecided;

    case LiteralFromIntegerVariable::Operator::Less:
        if (lower_bound(ilit.var) < ilit.value) {
            if (upper_bound(ilit.var) < ilit.value)
                return LiteralIs::DefinitelyTrue;
            else
                return LiteralIs::Undecided;
        }
        else
            return LiteralIs::DefinitelyFalse;

    case LiteralFromIntegerVariable::Operator::GreaterEqual:
        if (upper_bound(ilit.var) >= ilit.value) {
            if (lower_bound(ilit.var) >= ilit.value)
                return LiteralIs::DefinitelyTrue;
            else
                return LiteralIs::Undecided;
        }
        else
            return LiteralIs::DefinitelyFalse;

    case LiteralFromIntegerVariable::Operator::NotEqual:
        if (! in_domain(ilit.var, ilit.value))
            return LiteralIs::DefinitelyTrue;
        else if (has_single_value(ilit.var))
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

auto State::minimise(IntegerVariableID var) -> void
{
    if (_imp->optional_minimise_variable)
        throw UnimplementedException{"Not sure how to have multiple objectives"};
    _imp->optional_minimise_variable = var;
}

auto State::maximise(IntegerVariableID var) -> void
{
    if (_imp->optional_minimise_variable)
        throw UnimplementedException{"Not sure how to have multiple objectives"};
    _imp->optional_minimise_variable = -var;
}

auto State::update_objective_to_current_solution() -> void
{
    if (_imp->optional_minimise_variable)
        _imp->optional_objective_incumbent = (*this)(*_imp->optional_minimise_variable);
}

auto State::optional_minimise_variable() const -> optional<IntegerVariableID>
{
    return _imp->optional_minimise_variable;
}

auto State::infer_on_objective_variable_before_propagation() -> Inference
{
    if (_imp->optional_minimise_variable && _imp->optional_objective_incumbent)
        return infer(*_imp->optional_minimise_variable < *_imp->optional_objective_incumbent, NoJustificationNeeded{});
    else
        return Inference::NoChange;
}

auto innards::State::add_constraint_state(const ConstraintState c) -> ConstraintStateHandle
{
    // Copying because I'm not sure if making it a reference is a bad idea... (want it to persist)
    _imp->constraint_states.back().push_back(c);
    return ConstraintStateHandle{_imp->constraint_states.size() - 1};
}

auto innards::State::get_constraint_state(const ConstraintStateHandle h) -> ConstraintState &
{
    return _imp->constraint_states.back()[h.index];
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

    template auto State::infer_equal(const IntegerVariableID &, Integer, const Justification &) -> Inference;
    template auto State::infer_equal(const SimpleIntegerVariableID &, Integer, const Justification &) -> Inference;
    template auto State::infer_equal(const ViewOfIntegerVariableID &, Integer, const Justification &) -> Inference;
    template auto State::infer_equal(const ConstantIntegerVariableID &, Integer, const Justification &) -> Inference;

    template auto State::infer_not_equal(const IntegerVariableID &, Integer, const Justification &) -> Inference;
    template auto State::infer_not_equal(const SimpleIntegerVariableID &, Integer, const Justification &) -> Inference;
    template auto State::infer_not_equal(const ViewOfIntegerVariableID &, Integer, const Justification &) -> Inference;
    template auto State::infer_not_equal(const ConstantIntegerVariableID &, Integer, const Justification &) -> Inference;

    template auto State::infer_less_than(const IntegerVariableID &, Integer, const Justification &) -> Inference;
    template auto State::infer_less_than(const SimpleIntegerVariableID &, Integer, const Justification &) -> Inference;
    template auto State::infer_less_than(const ViewOfIntegerVariableID &, Integer, const Justification &) -> Inference;
    template auto State::infer_less_than(const ConstantIntegerVariableID &, Integer, const Justification &) -> Inference;

    template auto State::infer_greater_than_or_equal(const IntegerVariableID &, Integer, const Justification &) -> Inference;
    template auto State::infer_greater_than_or_equal(const SimpleIntegerVariableID &, Integer, const Justification &) -> Inference;
    template auto State::infer_greater_than_or_equal(const ViewOfIntegerVariableID &, Integer, const Justification &) -> Inference;
    template auto State::infer_greater_than_or_equal(const ConstantIntegerVariableID &, Integer, const Justification &) -> Inference;
}
