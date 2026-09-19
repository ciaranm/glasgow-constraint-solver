#include <gcs/constraints/all_different/justify.hh>
#include <gcs/innards/proofs/am1_from_pairs.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>

#include <util/enumerate.hh>

using namespace gcs;
using namespace gcs::innards;

using std::map;
using std::vector;

namespace
{
    // At most one variable can take each of these values: the pairwise
    // clauses, and then the shared fold of them into the clique inequality.
    // Emitted at Top and cached, because a Hall argument is replayed for every
    // inference that mentions the value.
    auto need_value_am1s(ProofLogger & logger, const vector<IntegerVariableID> & all_variables, const vector<Integer> & values,
        map<Integer, ProofLine> & value_am1_constraint_numbers) -> void
    {
        for (const auto & val : values) {
            if (value_am1_constraint_numbers.contains(val))
                continue;

            vector<ProofLiteralOrFlag> members;
            vector<vector<ProofLine>> at_most_ones(all_variables.size());
            for (unsigned i = 0; i < all_variables.size(); ++i) {
                members.push_back(ProofLiteral{all_variables[i] == val});
                for (unsigned j = 0; j < i; ++j)
                    at_most_ones[i].push_back(logger.emit_rup_proof_line(
                        WPBSum{} + 1_i * ! (all_variables[i] == val) + 1_i * ! (all_variables[j] == val) >= 1_i, ProofLevel::Temporary));
            }

            value_am1_constraint_numbers.emplace(val, recover_am1_from_pairs(logger, members, at_most_ones, ProofLevel::Top));
        }
    }
}

auto gcs::innards::justify_all_different_hall_set_or_violator(ProofLogger & logger, const State & state,
    const vector<IntegerVariableID> & all_variables, const vector<IntegerVariableID> & hall_variables, const vector<Integer> & hall_values,
    map<Integer, ProofLine> & value_am1_constraint_numbers) -> void
{
    need_value_am1s(logger, all_variables, hall_values, value_am1_constraint_numbers);

    // We are going to need the at least one value variables, and each only has to
    // name the values its own domain still holds. Those are a subset of the hall
    // values (that is what makes these variables a Hall set), so the at-most-ones
    // below still cancel every term this contributes; the hall values a particular
    // variable *cannot* take would contribute a term with nothing to cancel it, and
    // the reason would then have to discharge it separately. Everything else in the
    // definition range goes in as runs, which are exactly the holes the reason
    // states.
    vector<ProofLine> at_least_one_constraints;
    vector<Integer> still_possible;
    for (const auto & var : hall_variables) {
        still_possible.clear();
        for (const auto & val : hall_values)
            if (state.in_domain(var, val))
                still_possible.push_back(val);
        at_least_one_constraints.push_back(
            logger.names_and_ids_tracker().need_constraint_saying_variable_takes_at_least_one_value_over_cover(var, still_possible));
    }

    // each variable in the violator has to take at least one value that is
    // left in its domain, and each value in the component can only be used
    // once.
    PolBuilder pol;
    for (auto & c : at_least_one_constraints)
        pol.add(c);
    for (const auto & val : hall_values)
        pol.add(value_am1_constraint_numbers.at(val));
    pol.emit(logger, ProofLevel::Current);
}

auto gcs::innards::justify_all_different_hall_interval(ProofLogger & logger, const State & state, const vector<IntegerVariableID> & all_variables,
    const vector<IntegerVariableID> & hall_variables, Integer lo, Integer hi, map<Integer, ProofLine> & value_am1_constraint_numbers) -> void
{
    vector<Integer> hall_values;
    for (auto v = lo; v <= hi; ++v)
        hall_values.push_back(v);
    need_value_am1s(logger, all_variables, hall_values, value_am1_constraint_numbers);

    // Each Hall variable takes at least one value between its bounds. Naming
    // all of them, holes and all, is what lets the reason be just the bounds:
    // everything outside them goes in as runs the bounds rule out.
    PolBuilder pol;
    vector<Integer> between_bounds;
    for (const auto & var : hall_variables) {
        between_bounds.clear();
        auto [var_lo, var_hi] = state.bounds(var);
        for (auto v = var_lo; v <= var_hi; ++v)
            between_bounds.push_back(v);
        pol.add(logger.names_and_ids_tracker().need_constraint_saying_variable_takes_at_least_one_value_over_cover(var, between_bounds));
    }
    for (const auto & val : hall_values)
        pol.add(value_am1_constraint_numbers.at(val));
    pol.emit(logger, ProofLevel::Current);
}
