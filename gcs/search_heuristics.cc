#include <gcs/innards/propagators.hh>
#include <gcs/search_heuristics.hh>

#include <algorithm>
#include <random>
#include <tuple>

using std::mt19937;
using std::nullopt;
using std::optional;
using std::random_device;
using std::tuple;
using std::uniform_int_distribution;
using std::vector;

using namespace gcs;

auto gcs::branch_on_smallest_with_respect_to(const vector<IntegerVariableID> & vars, const BranchVariableComparator & comp) -> BranchCallback
{
    return [vars = vars, comp = comp](const CurrentState & state, const innards::Propagators & propagators) -> optional<IntegerVariableID> {
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

auto gcs::branch_in_order(const std::vector<IntegerVariableID> & vars) -> BranchCallback
{
    return [vars = vars](const CurrentState & state, const innards::Propagators &) -> optional<IntegerVariableID> {
        for (auto & v : vars) {
            auto size = state.domain_size(v);
            if (size >= 2_i)
                return v;
        }
        return nullopt;
    };
}

auto gcs::branch_on_dom(const vector<IntegerVariableID> & vars) -> BranchCallback
{
    return [vars = vars](const CurrentState & state, const innards::Propagators &) -> optional<IntegerVariableID> {
        optional<Integer> best_size;
        optional<IntegerVariableID> result;
        for (auto & v : vars) {
            auto size = state.domain_size(v);
            if (size < 2_i)
                continue;
            else if (size == 2_i)
                return v;
            else if ((! best_size) || size < *best_size) {
                best_size = size;
                result = v;
            }
        }
        return result;
    };
}

auto gcs::branch_on_dom(const Problem & problem) -> BranchCallback
{
    return branch_on_dom(problem.all_normal_variables());
}

auto gcs::branch_on_dom_then_deg(const vector<IntegerVariableID> & vars) -> BranchCallback
{
    return branch_on_smallest_with_respect_to(vars, [](const CurrentState & state, const innards::Propagators & p, const IntegerVariableID & a, const IntegerVariableID & b) {
        return tuple{state.domain_size(a), -p.degree_of(a)} < tuple{state.domain_size(b), -p.degree_of(b)};
    });
}

auto gcs::branch_on_dom_then_deg(const Problem & problem) -> BranchCallback
{
    return branch_on_dom_then_deg(problem.all_normal_variables());
}

auto gcs::branch_randomly(const Problem & problem) -> BranchCallback
{
    return branch_randomly(problem.all_normal_variables());
}

auto gcs::branch_randomly(const vector<IntegerVariableID> & vars) -> BranchCallback
{
    random_device rand_dev;
    mt19937 r(rand_dev());
    return [vars = vars, rand = move(r)](const CurrentState & state, const innards::Propagators &) mutable -> optional<IntegerVariableID> {
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

auto gcs::branch_on_dom_with_smallest_value(const vector<IntegerVariableID> & vars) -> BranchCallback
{
    return branch_on_smallest_with_respect_to(vars, [](const CurrentState & state, const innards::Propagators &, const IntegerVariableID & a, const IntegerVariableID & b) {
        return state.lower_bound(a) < state.lower_bound(b);
    });
}

auto gcs::branch_on_dom_with_smallest_value(const Problem & problem) -> BranchCallback
{
    return branch_on_dom_with_smallest_value(problem.all_normal_variables());
}

auto gcs::branch_sequence(const vector<BranchCallback> & branchers) -> BranchCallback
{
    return [branchers = branchers](const CurrentState & state, const innards::Propagators & p) -> optional<IntegerVariableID> {
        for (const auto & b : branchers) {
            auto result = b(state, p);
            if (result)
                return result;
        }
        return nullopt;
    };
}

auto gcs::guess_smallest_value_first() -> GuessCallback
{
    return [](const CurrentState & state, IntegerVariableID var) -> vector<IntegerVariableCondition> {
        vector<IntegerVariableCondition> result;
        for (auto val : state.each_value(var)) {
            result.push_back(var == val);
        }
        return result;
    };
}

auto gcs::guess_largest_value_first() -> GuessCallback
{
    return [](const CurrentState & state, IntegerVariableID var) -> vector<IntegerVariableCondition> {
        vector<IntegerVariableCondition> result;
        for (auto val : state.each_value(var)) {
            result.push_back(var == val);
        }
        reverse(result.begin(), result.end());
        return result;
    };
}

auto gcs::guess_median_value() -> GuessCallback
{
    return [](const CurrentState & state, IntegerVariableID var) -> vector<IntegerVariableCondition> {
        vector<IntegerVariableCondition> result;
        for (auto val : state.each_value(var)) {
            result.push_back(var == val);
        }
        return vector<IntegerVariableCondition>{result.at(result.size() / 2), ! result.at(result.size() / 2)};
    };
}

auto gcs::guess_randomly() -> GuessCallback
{
    return [](const CurrentState & state, IntegerVariableID var) -> vector<IntegerVariableCondition> {
        random_device rand_dev;
        mt19937 r(rand_dev());
        vector<IntegerVariableCondition> result;
        for (auto val : state.each_value(var)) {
            result.push_back(var == val);
        }
        shuffle(result.begin(), result.end(), r);
        return result;
    };
}
