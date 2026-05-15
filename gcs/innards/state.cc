#include <gcs/exception.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>
#include <gcs/innards/variable_id_utils.hh>
#include <gcs/problem.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <list>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::function;
using std::generator;
using std::list;
using std::make_optional;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::tuple;
using std::vector;

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

    auto apply_view(Integer v, bool negate_first, Integer then_add) -> Integer
    {
        return (negate_first ? -v : v) + then_add;
    }

    template <typename SimpleFn_, typename ConstantFn_>
    auto visit_actual(const SimpleIntegerVariableID & v, SimpleFn_ && sf, ConstantFn_ &&) -> decltype(sf(v))
    {
        return sf(v);
    }

    template <typename SimpleFn_, typename ConstantFn_>
    auto visit_actual(const ConstantIntegerVariableID & v, SimpleFn_ &&, ConstantFn_ && cf) -> decltype(cf(v))
    {
        return cf(v);
    }

    template <typename SimpleFn_, typename ConstantFn_>
    auto visit_actual(const DirectIntegerVariableID & v, SimpleFn_ && sf, ConstantFn_ && cf)
    {
        return overloaded{sf, cf}.visit(v);
    }
}

struct State::Imp
{
    ProofLogger * maybe_proof_logger;

    list<vector<IntervalSet<Integer>>> integer_variable_states{};
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
    if (lower > upper)
        throw InvalidProblemDefinitionException{"variable created with lower bound greater than upper bound"};
    _imp->integer_variable_states.back().emplace_back(lower, upper);
    return SimpleIntegerVariableID{_imp->integer_variable_states.back().size() - 1};
}

auto State::what_variable_id_will_be_created_next() const -> SimpleIntegerVariableID
{
    return SimpleIntegerVariableID{_imp->integer_variable_states.back().size()};
}

auto State::state_of(const SimpleIntegerVariableID & v) -> IntervalSet<Integer> &
{
    return _imp->integer_variable_states.back().at(v.index);
}

auto State::state_of(const SimpleIntegerVariableID & v) const -> const IntervalSet<Integer> &
{
    return _imp->integer_variable_states.back().at(v.index);
}

auto State::change_state_for_equal(const SimpleIntegerVariableID & var, Integer value) -> Inference
{
    auto & set = state_of(var);
    if (! set.contains(value))
        return Inference::Contradiction;
    if (set.lower() == set.upper())
        return Inference::NoChange;
    set.clear();
    set.insert_at_end(value);
    return Inference::Instantiated;
}

auto State::change_state_for_not_equal(const SimpleIntegerVariableID & var, Integer value) -> Inference
{
    auto & set = state_of(var);
    if (! set.contains(value))
        return Inference::NoChange;
    if (set.lower() == set.upper())
        return Inference::Contradiction;
    bool is_bound = (value == set.lower() || value == set.upper());
    set.erase(value);
    if (set.lower() == set.upper())
        return Inference::Instantiated;
    return is_bound ? Inference::BoundsChanged : Inference::InteriorValuesChanged;
}

auto State::change_state_for_less_than(const SimpleIntegerVariableID & var, Integer value) -> Inference
{
    auto & set = state_of(var);
    if (set.upper() < value)
        return Inference::NoChange;
    set.erase_greater_than(value - 1_i);
    if (set.empty())
        return Inference::Contradiction;
    if (set.lower() == set.upper())
        return Inference::Instantiated;
    return Inference::BoundsChanged;
}

auto State::change_state_for_greater_than_or_equal(const SimpleIntegerVariableID & var, Integer value) -> Inference
{
    auto & set = state_of(var);
    if (set.lower() >= value)
        return Inference::NoChange;
    set.erase_less_than(value);
    if (set.empty())
        return Inference::Contradiction;
    if (set.lower() == set.upper())
        return Inference::Instantiated;
    return Inference::BoundsChanged;
}

namespace
{
    auto infer_equal_on_constant(Integer const_value, Integer value) -> Inference
    {
        return const_value == value ? Inference::NoChange : Inference::Contradiction;
    }

    auto infer_not_equal_on_constant(Integer const_value, Integer value) -> Inference
    {
        return const_value != value ? Inference::NoChange : Inference::Contradiction;
    }

    auto infer_less_than_on_constant(Integer const_value, Integer value) -> Inference
    {
        return const_value < value ? Inference::NoChange : Inference::Contradiction;
    }

    auto infer_greater_than_or_equal_on_constant(Integer const_value, Integer value) -> Inference
    {
        return const_value >= value ? Inference::NoChange : Inference::Contradiction;
    }
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
        using enum VariableConditionOperator;
    case Equal:
        return infer_equal(cond.var, cond.value);
    case NotEqual:
        return infer_not_equal(cond.var, cond.value);
    case Less:
        return infer_less_than(cond.var, cond.value);
    case GreaterEqual:
        return infer_greater_than_or_equal(cond.var, cond.value);
    }
    throw NonExhaustiveSwitch{};
}

template <IntegerVariableIDLike VarType_>
auto State::infer_equal(const VarType_ & var, Integer value) -> Inference
{
    auto [actual_var, negate_first, then_add] = deview(var);
    auto adjusted = (negate_first ? -value + then_add : value - then_add);
    return visit_actual(actual_var, [&](const SimpleIntegerVariableID & v) { return change_state_for_equal(v, adjusted); }, [&](const ConstantIntegerVariableID & v) { return infer_equal_on_constant(v.const_value, adjusted); });
}

template <IntegerVariableIDLike VarType_>
auto State::infer_not_equal(const VarType_ & var, Integer value) -> Inference
{
    auto [actual_var, negate_first, then_add] = deview(var);
    auto adjusted = (negate_first ? -value + then_add : value - then_add);
    return visit_actual(actual_var, [&](const SimpleIntegerVariableID & v) { return change_state_for_not_equal(v, adjusted); }, [&](const ConstantIntegerVariableID & v) { return infer_not_equal_on_constant(v.const_value, adjusted); });
}

template <IntegerVariableIDLike VarType_>
auto State::infer_less_than(const VarType_ & var, Integer value) -> Inference
{
    auto [actual_var, negate_first, then_add] = deview(var);
    if (negate_first) {
        auto adjusted = -value + then_add + 1_i;
        return visit_actual(actual_var, [&](const SimpleIntegerVariableID & v) { return change_state_for_greater_than_or_equal(v, adjusted); }, [&](const ConstantIntegerVariableID & v) { return infer_greater_than_or_equal_on_constant(v.const_value, adjusted); });
    }
    else {
        auto adjusted = value - then_add;
        return visit_actual(actual_var, [&](const SimpleIntegerVariableID & v) { return change_state_for_less_than(v, adjusted); }, [&](const ConstantIntegerVariableID & v) { return infer_less_than_on_constant(v.const_value, adjusted); });
    }
}

template <IntegerVariableIDLike VarType_>
auto State::infer_greater_than_or_equal(const VarType_ & var, Integer value) -> Inference
{
    auto [actual_var, negate_first, then_add] = deview(var);
    if (negate_first) {
        auto adjusted = -value + then_add + 1_i;
        return visit_actual(actual_var, [&](const SimpleIntegerVariableID & v) { return change_state_for_less_than(v, adjusted); }, [&](const ConstantIntegerVariableID & v) { return infer_less_than_on_constant(v.const_value, adjusted); });
    }
    else {
        auto adjusted = value - then_add;
        return visit_actual(actual_var, [&](const SimpleIntegerVariableID & v) { return change_state_for_greater_than_or_equal(v, adjusted); }, [&](const ConstantIntegerVariableID & v) { return infer_greater_than_or_equal_on_constant(v.const_value, adjusted); });
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
    auto raw = overloaded{
        [&](const SimpleIntegerVariableID & v) { return negate_first ? state_of(v).upper() : state_of(v).lower(); },
        [&](const ConstantIntegerVariableID & v) { return v.const_value; }}
                   .visit(actual_var);
    return (negate_first ? -raw : raw) + then_add;
}

auto State::upper_bound(const IntegerVariableID var) const -> Integer
{
    auto [actual_var, negate_first, then_add] = deview(var);
    auto raw = overloaded{
        [&](const SimpleIntegerVariableID & v) { return negate_first ? state_of(v).lower() : state_of(v).upper(); },
        [&](const ConstantIntegerVariableID & v) { return v.const_value; }}
                   .visit(actual_var);
    return (negate_first ? -raw : raw) + then_add;
}

template <IntegerVariableIDLike VarType_>
auto State::bounds(const VarType_ & var) const -> pair<Integer, Integer>
{
    auto [actual_var, negate_first, then_add] = deview(var);
    auto raw = visit_actual(actual_var, [&](const SimpleIntegerVariableID & v) { return pair{state_of(v).lower(), state_of(v).upper()}; }, [&](const ConstantIntegerVariableID & v) { return pair{v.const_value, v.const_value}; });
    if (negate_first)
        return pair{-raw.second + then_add, -raw.first + then_add};
    else
        return pair{raw.first + then_add, raw.second + then_add};
}

template <IntegerVariableIDLike VarType_>
auto State::in_domain(const VarType_ & var, const Integer val) const -> bool
{
    auto [actual_var, negate_first, then_add] = deview(var);
    auto adjusted = (negate_first ? -val + then_add : val - then_add);
    return visit_actual(actual_var, [&](const SimpleIntegerVariableID & v) { return state_of(v).contains(adjusted); }, [&](const ConstantIntegerVariableID & v) { return v.const_value == adjusted; });
}

auto State::domain_has_holes(const IntegerVariableID var) const -> bool
{
    auto [actual_var, _1, _2] = deview(var);
    return overloaded{
        [&](const SimpleIntegerVariableID & v) { return state_of(v).has_holes(); },
        [](const ConstantIntegerVariableID &) { return false; }}
        .visit(actual_var);
}

template <IntegerVariableIDLike VarType_>
auto State::optional_single_value(const VarType_ & var) const -> optional<Integer>
{
    auto [actual_var, negate_first, then_add] = deview(var);
    auto raw = visit_actual(actual_var, [&](const SimpleIntegerVariableID & v) -> optional<Integer> {
            const auto & set = state_of(v);
            if (set.lower() == set.upper())
                return make_optional(set.lower());
            return nullopt; }, [&](const ConstantIntegerVariableID & v) -> optional<Integer> { return make_optional(v.const_value); });

    if (raw)
        return apply_view(*raw, negate_first, then_add);
    return nullopt;
}

auto State::has_single_value(const IntegerVariableID var) const -> bool
{
    auto [actual_var, _1, _2] = deview(var);
    return overloaded{
        [&](const SimpleIntegerVariableID & v) { return state_of(v).lower() == state_of(v).upper(); },
        [](const ConstantIntegerVariableID &) { return true; }}
        .visit(actual_var);
}

template <IntegerVariableIDLike VarType_>
auto State::domain_size(const VarType_ & var) const -> Integer
{
    auto [actual_var, _1, _2] = deview(var);
    return visit_actual(actual_var, [&](const SimpleIntegerVariableID & v) { return Integer(state_of(v).size()); }, [](const ConstantIntegerVariableID &) { return Integer{1}; });
}

template <IntegerVariableIDLike VarType_>
auto State::copy_of_values(const VarType_ & var) const -> IntervalSet<Integer>
{
    auto [actual_var, negate_first, then_add] = deview(var);
    auto raw = visit_actual(actual_var, [&](const SimpleIntegerVariableID & v) -> IntervalSet<Integer> { return state_of(v); }, [&](const ConstantIntegerVariableID & v) -> IntervalSet<Integer> { return IntervalSet<Integer>{v.const_value, v.const_value}; });
    if (! negate_first && then_add == 0_i)
        return raw;
    IntervalSet<Integer> result;
    if (negate_first) {
        // Each stored interval [l, u] becomes [-u + then_add, -l + then_add],
        // and negation reverses the order, so iterate in reverse to keep
        // result intervals sorted for insert_at_end.
        std::vector<std::pair<Integer, Integer>> intervals;
        for (auto p : raw.each_interval())
            intervals.push_back(p);
        for (auto it = intervals.rbegin(); it != intervals.rend(); ++it)
            result.insert_at_end(-it->second + then_add, -it->first + then_add);
    }
    else {
        for (const auto & [l, u] : raw.each_interval())
            result.insert_at_end(l + then_add, u + then_add);
    }
    return result;
}

template <IntegerVariableIDLike VarType_>
auto State::domain_intersects_with(const VarType_ & var, const IntervalSet<Integer> & set) const -> bool
{
    auto [actual_var, negate_first, then_add] = deview(var);
    if (negate_first) {
        // Negated views are rare. Fall back to materialising the view's
        // values via copy_of_values, which already handles negation.
        return copy_of_values(var).contains_any_of(set);
    }
    return visit_actual(
        actual_var,
        [&](const SimpleIntegerVariableID & v) -> bool {
            // Common case: SimpleIntegerVariableID with no view offset. Walk
            // the stored interval set against `set` directly via IntervalSet's
            // merge-walk; no copy.
            if (then_add == 0_i)
                return state_of(v).contains_any_of(set);
            // Rare case: a non-trivial offset means we'd need an offset-aware
            // merge-walk. Fall back to materialising the shifted domain — the
            // copy cost is the price of a feature that almost no Element-style
            // caller actually exercises.
            return copy_of_values(var).contains_any_of(set);
        },
        [&](const ConstantIntegerVariableID & v) -> bool {
            return set.contains(v.const_value + then_add);
        });
}

auto State::domains_intersect(const IntegerVariableID & var1, const IntegerVariableID & var2) const -> bool
{
    auto [actual1, neg1, add1] = deview(var1);
    auto [actual2, neg2, add2] = deview(var2);
    if (neg1 || neg2) {
        // Negated views are rare. Materialise one side's values via
        // copy_of_values (which handles negation) and reuse the
        // var-vs-IntervalSet path. Pick the negated side to materialise
        // so the other side stays in its stored form for the merge-walk
        // when possible.
        if (neg1)
            return domain_intersects_with(var2, copy_of_values(var1));
        else
            return domain_intersects_with(var1, copy_of_values(var2));
    }
    return visit_actual(
        actual1,
        [&](const SimpleIntegerVariableID & v1) -> bool {
            return visit_actual(
                actual2,
                [&](const SimpleIntegerVariableID & v2) -> bool {
                    // Common case: both Simple with no view offsets — walk
                    // the two stored interval sets in merge order without
                    // copying either side.
                    if (add1 == 0_i && add2 == 0_i)
                        return state_of(v1).contains_any_of(state_of(v2));
                    // At least one side has an offset; fall back to the
                    // IntervalSet overload. copy_of_values handles the offset.
                    return domain_intersects_with(var1, copy_of_values(var2));
                },
                [&](const ConstantIntegerVariableID & v2) -> bool {
                    return in_domain(var1, v2.const_value + add2);
                });
        },
        [&](const ConstantIntegerVariableID & v1) -> bool {
            return in_domain(var2, v1.const_value + add1);
        });
}

namespace
{
    auto each_value_generator(IntervalSet<Integer> set,
        std::function<auto(Integer)->Integer> apply) -> generator<Integer>
    {
        for (auto i : set.each())
            co_yield apply(i);
    }

    auto each_value_constant_generator(Integer val,
        std::function<auto(Integer)->Integer> apply) -> generator<Integer>
    {
        co_yield apply(val);
    }
}

template <IntegerVariableIDLike VarType_>
auto State::each_value_immutable(const VarType_ & var) const -> generator<Integer>
{
    auto [actual_var, negate_first, then_add] = deview(var);

    auto apply = [negate_first = negate_first, then_add = then_add](Integer v) -> Integer {
        return apply_view(v, negate_first, then_add);
    };

    return visit_actual(
        actual_var,
        [&](const SimpleIntegerVariableID & v) {
            return each_value_generator(state_of(v), apply);
        },
        [&](const ConstantIntegerVariableID & v) {
            return each_value_constant_generator(v.const_value, apply);
        });
}

template <IntegerVariableIDLike VarType_>
auto State::each_value_mutable(const VarType_ & var) const -> generator<Integer>
{
    auto [actual_var, negate_first, then_add] = deview(var);

    auto apply = [negate_first = negate_first, then_add = then_add](Integer v) -> Integer {
        return apply_view(v, negate_first, then_add);
    };

    return visit_actual(
        actual_var,
        [&](const SimpleIntegerVariableID & v) {
            return each_value_generator(state_of(v), apply);
        },
        [&](const ConstantIntegerVariableID & v) {
            return each_value_constant_generator(v.const_value, apply);
        });
}

auto State::operator()(const IntegerVariableID & i) const -> Integer
{
    if (auto result = optional_single_value(i))
        return *result;
    throw VariableDoesNotHaveUniqueValue{"Integer variable " + debug_string(i) + " does not have a unique value"};
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
    return [](const auto & extra_proof_conditions, const auto & guesses) -> generator<Literal> {
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
        using enum VariableConditionOperator;
    case Equal:
        if (! in_domain(cond.var, cond.value))
            return LiteralIs::DefinitelyFalse;
        else if (has_single_value(cond.var))
            return LiteralIs::DefinitelyTrue;
        else
            return LiteralIs::Undecided;

    case Less:
        if (lower_bound(cond.var) < cond.value) {
            if (upper_bound(cond.var) < cond.value)
                return LiteralIs::DefinitelyTrue;
            else
                return LiteralIs::Undecided;
        }
        else
            return LiteralIs::DefinitelyFalse;

    case GreaterEqual:
        if (upper_bound(cond.var) >= cond.value) {
            if (lower_bound(cond.var) >= cond.value)
                return LiteralIs::DefinitelyTrue;
            else
                return LiteralIs::Undecided;
        }
        else
            return LiteralIs::DefinitelyFalse;

    case NotEqual:
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
    _imp->constraint_states.back().push_back(c);
    return ConstraintStateHandle{static_cast<unsigned long>(_imp->constraint_states.back().size() - 1)};
}

auto innards::State::add_persistent_constraint_state(const ConstraintState c) -> ConstraintStateHandle
{
    _imp->persistent_constraint_states.push_back(c);
    return ConstraintStateHandle{static_cast<unsigned long>(_imp->persistent_constraint_states.size() - 1)};
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

    template auto State::domain_intersects_with(const IntegerVariableID &, const IntervalSet<Integer> &) const -> bool;
    template auto State::domain_intersects_with(const SimpleIntegerVariableID &, const IntervalSet<Integer> &) const -> bool;
    template auto State::domain_intersects_with(const ViewOfIntegerVariableID &, const IntervalSet<Integer> &) const -> bool;
    template auto State::domain_intersects_with(const ConstantIntegerVariableID &, const IntervalSet<Integer> &) const -> bool;

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
