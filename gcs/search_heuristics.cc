#include <gcs/innards/propagators.hh>
#include <gcs/search_heuristics.hh>

#include <tuple>

using std::optional;
using std::tuple;
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

auto gcs::guess_smallest_value_first() -> GuessCallback
{
    return [](const CurrentState & state, IntegerVariableID var) -> vector<IntegerVariableCondition> {
        vector<IntegerVariableCondition> result;
        state.for_each_value(var, [&](Integer val) {
            result.push_back(var == val);
        });
        return result;
    };
}
