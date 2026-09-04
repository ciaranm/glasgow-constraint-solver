#include <gcs/constraints/all_different/justify.hh>
#include <gcs/innards/proofs/am1_from_pairs.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>

#include <util/enumerate.hh>

using namespace gcs;
using namespace gcs::innards;

using std::map;
using std::vector;

auto gcs::innards::justify_all_different_hall_set_or_violator(ProofLogger & logger, const vector<IntegerVariableID> & all_variables,
    const vector<IntegerVariableID> & hall_variables, const vector<Integer> & hall_values, map<Integer, ProofLine> & value_am1_constraint_numbers)
    -> void
{
    // we are going to need the am1s over values, if they don't exist yet
    for (const auto & val : hall_values) {
        if (value_am1_constraint_numbers.contains(val))
            continue;

        // At most one variable can take this value: the pairwise clauses, and
        // then the shared fold of them into the clique inequality. Emitted at
        // Top and cached here, because the Hall set argument below is replayed
        // for every violator that mentions this value.
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

    // we are going to need the at least one value variables
    vector<ProofLine> at_least_one_constraints;
    for (const auto & var : hall_variables)
        at_least_one_constraints.push_back(logger.names_and_ids_tracker().need_constraint_saying_variable_takes_at_least_one_value(var));

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
