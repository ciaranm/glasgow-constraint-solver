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

auto gcs::innards::emit_gcc_capacity_pol(ProofLogger & logger, const State & state, const vector<IntegerVariableID> & vars,
    const vector<Integer> & values, const vector<IntegerVariableID> & counts, const GCCCountLines & count_lines, const vector<size_t> & cut_values,
    const vector<IntegerVariableID> & confined) -> void
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
    // A confined variable's at-least-one only has to name the hall values it can
    // still take --- a subset of the hall set, since confinement is exactly the
    // domain lying inside it. The rest of its definition range goes in as runs,
    // which the reason rules out (see gcc_capacity_reason, whose gaps are these
    // very runs clipped to the variable's bounds). Naming a hall value the variable
    // cannot take would cost a term the count lines do cancel, but the cover can be
    // this much smaller for free, and a cover with many values makes that the
    // difference between a line per cover value and a line per domain value.
    vector<Integer> still_possible;
    for (const auto & var : confined) {
        // A constant adds a fixed 0 or 1 to each count line: our OPB folds it into
        // the right-hand side, and cake_pb_cp's pins it with a unit row. Either way
        // it leaves no term here for an at-least-one to cancel, so it needs none
        // (and the tracker has none to give it).
        if (holds_alternative<ConstantIntegerVariableID>(var))
            continue;
        still_possible.clear();
        for (const auto & val : hall)
            if (state.in_domain(var, val))
                still_possible.push_back(val);
        pb.add(tracker.need_constraint_saying_variable_takes_at_least_one_value_over_cover(var, still_possible));
    }
    pb.emit(logger, ProofLevel::Temporary);
}

auto gcs::innards::gcc_capacity_reason(const State & state, const vector<Integer> & values, const vector<IntegerVariableID> & counts,
    const vector<size_t> & cut_values, const vector<IntegerVariableID> & confined) -> ReasonLiterals
{
    auto hall = hall_set(values, cut_values);
    ReasonLiterals r;
    for (const auto & var : confined)
        append_confined_to_hall_reason(state, var, hall.begin(), hall.end(), r);
    for (auto v : cut_values)
        if (! holds_alternative<ConstantIntegerVariableID>(counts[v]))
            r.emplace_back(counts[v] <= state.bounds(counts[v]).second);
    return r;
}

auto gcs::innards::emit_gcc_demand_pol(ProofLogger & logger, const State & state, const vector<IntegerVariableID> & vars,
    const vector<Integer> & values, const vector<IntegerVariableID> & counts, const GCCCountLines & count_lines, const vector<size_t> & cut_values,
    const vector<IntegerVariableID> & potential, optional<IntegerVariableID> pruned_var, optional<Integer> pruned_value) -> void
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
        // As for the capacity pol: a constant's contribution to the count lines is
        // fixed, so it leaves no term for an at-most-one to cancel and needs none.
        // It is never the pruned variable: in the GAC arm's feasible flow a
        // constant's only edge carries flow, so nothing prunes it.
        if (holds_alternative<ConstantIntegerVariableID>(var))
            continue;
        // recover_am1 takes its atoms negated: x != v, with pairwise lines
        // (x != v) + (x != w) >= 1, and gives Sum_v (x != v) >= n - 1.
        vector<IntegerVariableCondition> atoms;
        for (const auto & val : hall)
            atoms.push_back(var != val);
        if (pruned_var == optional<IntegerVariableID>{var} && pruned_value)
            atoms.push_back(var != *pruned_value);
        if (atoms.size() >= 2)
            pb.add(recover_am1<IntegerVariableCondition>(
                logger, ProofLevel::Temporary, atoms, [&](const IntegerVariableCondition & p, const IntegerVariableCondition & q) {
                    return logger.emit(RUPProofRule{}, WPBSum{} + 1_i * p + 1_i * q >= 1_i, ProofLevel::Temporary);
                }));
        else if (atoms.size() == 1)
            // At-most-one over a single atom is the vacuous x <= 1; emit it so
            // the pol still gets the (1 - x) contribution for this variable.
            pb.add(logger.emit(RUPProofRule{}, WPBSum{} + 1_i * atoms[0] >= 0_i, ProofLevel::Temporary));
    }
    pb.emit(logger, ProofLevel::Temporary);
}

auto gcs::innards::gcc_demand_reason(const State & state, const vector<IntegerVariableID> & vars, const vector<Integer> & values,
    const vector<IntegerVariableID> & counts, const vector<size_t> & cut_values, const vector<IntegerVariableID> & potential) -> ReasonLiterals
{
    auto hall = hall_set(values, cut_values);
    auto meets_hall = [&](const IntegerVariableID & var) {
        for (const auto & val : hall)
            if (state.in_domain(var, val))
                return true;
        return false;
    };
    (void)potential;
    ReasonLiterals r;
    for (const auto & var : vars)
        if (! meets_hall(var))
            for (const auto & val : hall)
                r.emplace_back(var != val);
    for (auto v : cut_values)
        if (! holds_alternative<ConstantIntegerVariableID>(counts[v]))
            r.emplace_back(counts[v] >= state.bounds(counts[v]).first);
    return r;
}
