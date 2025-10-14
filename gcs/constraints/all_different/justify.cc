#include <gcs/constraints/all_different/justify.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>

#include <util/enumerate.hh>

#include <sstream>

using namespace gcs;
using namespace gcs::innards;

using std::map;
using std::stringstream;
using std::vector;

auto gcs::innards::justify_all_different_hall_set_or_violator(
    ProofLogger & logger,
    const vector<IntegerVariableID> & all_variables,
    const vector<IntegerVariableID> & hall_variables,
    const vector<Integer> & hall_values,
    map<Integer, ProofLine> & value_am1_constraint_numbers) -> void
{
    // we are going to need the am1s over values, if they don't exist yet
    for (const auto & val : hall_values) {
        if (value_am1_constraint_numbers.contains(val))
            continue;

        // at most one variable can take this value
        stringstream step;
        step << "pol";
        bool first = true;
        int layer = 0;
        for (unsigned i = 1; i < all_variables.size(); ++i) {
            if (++layer >= 2)
                step << " " << layer << " *";

            for (unsigned j = 0; j < i; ++j) {
                auto ne = logger.emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * ! (all_variables[i] == val) + 1_i * ! (all_variables[j] == val) >= 1_i, ProofLevel::Temporary);
                step << " " << ne;
                if (! first)
                    step << " +";
                first = false;
            }

            step << " " << (layer + 1) << " d";
        }

        if (layer != 0)
            value_am1_constraint_numbers.emplace(val, logger.emit_proof_line(step.str(), ProofLevel::Top));
    }

    // we are going to need the at least one value variables
    vector<ProofLine> at_least_one_constraints;
    for (const auto & var : hall_variables)
        at_least_one_constraints.push_back(logger.names_and_ids_tracker().need_constraint_saying_variable_takes_at_least_one_value(var));

    // each variable in the violator has to take at least one value that is
    // left in its domain...
    stringstream proof_step;
    proof_step << "pol";
    bool first = true;
    for (auto & c : at_least_one_constraints) {
        proof_step << " " << c;
        if (! first)
            proof_step << " +";
        first = false;
    }

    // and each value in the component can only be used once
    for (const auto & val : hall_values)
        proof_step << " " << value_am1_constraint_numbers.at(val) << " +";

    logger.emit_proof_line(proof_step.str(), ProofLevel::Current);
}
