#include <gcs/innards/propagators.hh>
#include <gcs/search_heuristics.hh>

#include <algorithm>
#include <random>

using std::generator;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::random_device;
using std::shuffle;
using std::tuple;
using std::uniform_int_distribution;
using std::vector;

using namespace gcs;

auto gcs::branch_with(BranchVariableSelector var, BranchValueGenerator val) -> BranchCallback
{
    return [var = move(var), val = move(val)](const CurrentState & s, const innards::Propagators & p) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, const innards::Propagators & p,
                   BranchVariableSelector select_var, BranchValueGenerator make_val_gen) -> generator<IntegerVariableCondition> {
            auto branch_var = select_var(s, p);
            if (branch_var)
                return make_val_gen(s, p, *branch_var);
            else
                return []() -> generator<IntegerVariableCondition> { co_return; }();
        }(s, p, move(var), move(val));
    };
}

auto gcs::branch_sequence(BranchCallback a, BranchCallback b) -> BranchCallback
{
    return [a = move(a), b = move(b)](const CurrentState & s, const innards::Propagators & p) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, const innards::Propagators & p, BranchCallback a, BranchCallback b) -> generator<IntegerVariableCondition> {
            auto gen_a = a(s, p);
            auto iter_a = gen_a.begin();
            if (iter_a != gen_a.end()) {
                for (; iter_a != gen_a.end(); ++iter_a)
                    co_yield *iter_a;
            }
            else {
                auto gen_b = b(s, p);
                auto iter_b = gen_b.begin();
                for (; iter_b != gen_b.end(); ++iter_b)
                    co_yield *iter_b;
            }
        }(s, p, move(a), move(b));
    };
}

auto gcs::variable_order::random(const Problem & problem) -> BranchVariableSelector
{
    return variable_order::random(problem.all_normal_variables());
}

auto gcs::variable_order::random(vector<IntegerVariableID> vars) -> BranchVariableSelector
{
    random_device rand_dev;
    mt19937 r(rand_dev());
    return [vars = move(vars), rand = move(r)](const CurrentState & state,
               const innards::Propagators &) mutable -> optional<IntegerVariableID> {
        vector<IntegerVariableID> feasible;
        for (auto & var : vars)
            if (state.domain_size(var) >= 2_i)
                feasible.push_back(var);
        if (feasible.empty())
            return nullopt;
        else {
            uniform_int_distribution<size_t> dist(0, feasible.size() - 1);
            return feasible[dist(rand)];
        }
    };
}

auto gcs::variable_order::in_order_of(const Problem & problem, VariableComparator comp) -> BranchVariableSelector
{
    return variable_order::in_order_of(problem.all_normal_variables(), move(comp));
}

auto gcs::variable_order::in_order_of(vector<IntegerVariableID> vars, VariableComparator comp) -> BranchVariableSelector
{
    return [vars = move(vars), comp = move(comp)](
               const CurrentState & state, const innards::Propagators & propagators) -> optional<IntegerVariableID> {
        optional<IntegerVariableID> result;
        for (auto & v : vars) {
            auto size = state.domain_size(v);
            if (size < 2_i)
                continue;
            if ((! result) || comp(state, propagators, v, *result))
                result = v;
        }
        return result;
    };
}

auto gcs::variable_order::in_order(vector<IntegerVariableID> vars) -> BranchVariableSelector
{
    return [vars = move(vars)](
               const CurrentState & state, const innards::Propagators &) -> optional<IntegerVariableID> {
        for (auto & v : vars) {
            auto size = state.domain_size(v);
            if (size < 2_i)
                continue;
            return v;
        }
        return nullopt;
    };
}

auto gcs::variable_order::dom(const Problem & problem) -> BranchVariableSelector
{
    return dom(problem.all_normal_variables());
}

auto gcs::variable_order::dom(vector<IntegerVariableID> vars) -> BranchVariableSelector
{
    return variable_order::in_order_of(vars, [](const CurrentState & state, const innards::Propagators &, const IntegerVariableID & a, const IntegerVariableID & b) {
        return state.domain_size(a) < state.domain_size(b);
    });
}

auto gcs::variable_order::dom_then_deg(const Problem & problem) -> BranchVariableSelector
{
    return dom_then_deg(problem.all_normal_variables());
}

auto gcs::variable_order::dom_then_deg(vector<IntegerVariableID> vars) -> BranchVariableSelector
{
    return variable_order::in_order_of(vars, [](const CurrentState & state, const innards::Propagators & p, const IntegerVariableID & a, const IntegerVariableID & b) {
        return tuple{state.domain_size(a), -p.degree_of(a)} < tuple{state.domain_size(b), -p.degree_of(b)};
    });
}

auto gcs::variable_order::with_smallest_value(const Problem & problem) -> BranchVariableSelector
{
    return with_smallest_value(problem.all_normal_variables());
}

auto gcs::variable_order::with_smallest_value(vector<IntegerVariableID> vars) -> BranchVariableSelector
{
    return variable_order::in_order_of(vars, [](const CurrentState & state, const innards::Propagators &, const IntegerVariableID & a, const IntegerVariableID & b) {
        return state.lower_bound(a) < state.lower_bound(b);
    });
}

auto gcs::value_order::random() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            vector<Integer> values;
            for (auto v : s.each_value(var))
                values.push_back(v);

            random_device rand_dev;
            mt19937 r(rand_dev());
            shuffle(values.begin(), values.end(), r);

            for (auto v : values)
                co_yield var == v;
        }(s, var);
    };
}

auto gcs::value_order::smallest_in() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            auto value = s.lower_bound(var);
            co_yield var == value;
            co_yield var != value;
        }(s, var);
    };
}

auto gcs::value_order::smallest_out() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            auto value = s.lower_bound(var);
            co_yield var != value;
            co_yield var == value;
        }(s, var);
    };
}

auto gcs::value_order::smallest_first() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            auto values = s.copy_of_values(var);
            for (auto v : values.each())
                co_yield var == v;
        }(s, var);
    };
}

auto gcs::value_order::largest_in() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            auto value = s.upper_bound(var);
            co_yield var == value;
            co_yield var != value;
        }(s, var);
    };
}

auto gcs::value_order::largest_out() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            auto value = s.upper_bound(var);
            co_yield var != value;
            co_yield var == value;
        }(s, var);
    };
}

auto gcs::value_order::largest_first() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            auto values = s.copy_of_values(var);
            for (auto v : values.each_reversed())
                co_yield var == v;
        }(s, var);
    };
}

auto gcs::value_order::median() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            vector<Integer> values;
            for (auto v : s.each_value(var))
                values.push_back(v);
            auto v = values.at(values.size() / 2);
            co_yield var == v;
            co_yield var != v;
        }(s, var);
    };
}
