#include <gcs/constraints/global_cardinality/justify.hh>
#include <gcs/constraints/innards/recover_am1.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>

#include <set>

using namespace gcs;
using namespace gcs::innards;

using std::holds_alternative;
using std::optional;
using std::set;
using std::size_t;
using std::vector;

namespace
{
    auto hall_set(const vector<Integer> & values, const vector<size_t> & cut_values) -> set<Integer>
    {
        set<Integer> hall;
        for (auto v : cut_values)
            hall.insert(values[v]);
        return hall;
    }
}

auto gcs::innards::emit_gcc_capacity_pol(ProofLogger & logger, const State & state,
    const vector<IntegerVariableID> & vars, const vector<Integer> & values,
    const vector<IntegerVariableID> & counts, const GCCCountLines & count_lines,
    const vector<size_t> & cut_values, const vector<IntegerVariableID> & confined) -> void
{
    auto hall = hall_set(values, cut_values);
    auto & tracker = logger.names_and_ids_tracker();
    PolBuilder pb;
    for (auto v : cut_values) {
        pb.add(*count_lines[v].first);
        if (! holds_alternative<ConstantIntegerVariableID>(counts[v]))
            pb.add_for_literal(tracker, counts[v] <= state.bounds(counts[v]).second);
    }
    (void)vars;
    for (const auto & var : confined)
        pb.add(tracker.need_constraint_saying_variable_takes_at_least_one_value(var));
    pb.emit(logger, ProofLevel::Temporary);
}

auto gcs::innards::gcc_capacity_reason(const State & state, const vector<Integer> & values,
    const vector<IntegerVariableID> & counts, const vector<size_t> & cut_values,
    const vector<IntegerVariableID> & confined) -> Reason
{
    auto hall = hall_set(values, cut_values);
    Reason r;
    for (const auto & var : confined) {
        auto [v_lo, v_hi] = state.bounds(var);
        for (Integer s = v_lo; s <= v_hi; ++s)
            if (! hall.contains(s) && ! state.in_domain(var, s))
                r.emplace_back(var != s);
        r.emplace_back(var >= v_lo);
        r.emplace_back(var <= v_hi);
    }
    for (auto v : cut_values)
        if (! holds_alternative<ConstantIntegerVariableID>(counts[v]))
            r.emplace_back(counts[v] <= state.bounds(counts[v]).second);
    return r;
}

auto gcs::innards::emit_gcc_demand_pol(ProofLogger & logger, const State & state,
    const vector<IntegerVariableID> & vars, const vector<Integer> & values,
    const vector<IntegerVariableID> & counts, const GCCCountLines & count_lines,
    const vector<size_t> & cut_values, const vector<IntegerVariableID> & potential,
    optional<IntegerVariableID> pruned_var, optional<size_t> pruned_value) -> void
{
    auto hall = hall_set(values, cut_values);
    PolBuilder pb;
    for (auto v : cut_values) {
        pb.add(*count_lines[v].second);
        if (! holds_alternative<ConstantIntegerVariableID>(counts[v]))
            pb.add_for_literal(logger.names_and_ids_tracker(), counts[v] >= state.bounds(counts[v]).first);
    }
    (void)vars;
    for (const auto & var : potential) {
        vector<IntegerVariableCondition> atoms;
        for (const auto & val : hall)
            atoms.push_back(var == val);
        if (pruned_var == optional<IntegerVariableID>{var} && pruned_value)
            atoms.push_back(var == values[*pruned_value]);
        pb.add(recover_am1<IntegerVariableCondition>(logger, ProofLevel::Temporary, atoms,
            [&](const IntegerVariableCondition & p, const IntegerVariableCondition & q) {
                return logger.emit(RUPProofRule{}, WPBSum{} + 1_i * ! p + 1_i * ! q >= 1_i, ProofLevel::Temporary);
            }));
    }
    pb.emit(logger, ProofLevel::Temporary);
}

auto gcs::innards::gcc_demand_reason(const State & state, const vector<IntegerVariableID> & vars,
    const vector<Integer> & values, const vector<IntegerVariableID> & counts,
    const vector<size_t> & cut_values, const vector<IntegerVariableID> & potential) -> Reason
{
    auto hall = hall_set(values, cut_values);
    auto meets_hall = [&](const IntegerVariableID & var) {
        for (const auto & val : hall)
            if (state.in_domain(var, val))
                return true;
        return false;
    };
    (void)potential;
    Reason r;
    for (const auto & var : vars)
        if (! meets_hall(var))
            for (const auto & val : hall)
                r.emplace_back(var != val);
    for (auto v : cut_values)
        if (! holds_alternative<ConstantIntegerVariableID>(counts[v]))
            r.emplace_back(counts[v] >= state.bounds(counts[v]).first);
    return r;
}
