/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/innards/propagators.hh>
#include <gcs/search_heuristics.hh>

#include <tuple>

using std::optional;
using std::tuple;
using std::vector;

using namespace gcs;

auto gcs::branch_on_smallest_with_respect_to(const Problem &,
    const vector<IntegerVariableID> & vars, const BranchVariableComparator & comp) -> BranchCallback
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

auto gcs::branch_on_dom(const Problem & problem, const vector<IntegerVariableID> & vars) -> BranchCallback
{
    return branch_on_smallest_with_respect_to(problem, vars, [](const CurrentState & state, const innards::Propagators &, const IntegerVariableID & a, const IntegerVariableID & b) {
        return state.domain_size(a) < state.domain_size(b);
    });
}

auto gcs::branch_on_dom(const Problem & problem) -> BranchCallback
{
    return branch_on_dom(problem, problem.all_normal_variables());
}

auto gcs::branch_on_dom_then_deg(const Problem & problem, const vector<IntegerVariableID> & vars) -> BranchCallback
{
    return branch_on_smallest_with_respect_to(problem, vars, [&problem](const CurrentState & state, const innards::Propagators & p, const IntegerVariableID & a, const IntegerVariableID & b) {
        return tuple{state.domain_size(a), -p.degree_of(a)} < tuple{state.domain_size(b), -p.degree_of(b)};
    });
}

auto gcs::branch_on_dom_then_deg(const Problem & problem) -> BranchCallback
{
    return branch_on_dom_then_deg(problem, problem.all_normal_variables());
}

auto gcs::guess_smallest_value_first() -> GuessCallback
{
    return [](const CurrentState & state, IntegerVariableID var) -> vector<Literal> {
        vector<Literal> result;
        state.for_each_value(var, [&](Integer val) {
            result.push_back(var == val);
        });
        return result;
    };
}
