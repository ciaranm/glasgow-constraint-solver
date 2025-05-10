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
        const vector<IntegerVariableID> & hall_variables,
        const vector<Integer> & hall_values,
        const map<Integer, ProofLine> * const constraint_numbers) -> void
{
    // we are going to need the at least one value variables
    vector<ProofLine> at_least_one_constraints;
    for (const auto & var : hall_variables)
        at_least_one_constraints.push_back(logger.names_and_ids_tracker().need_constraint_saying_variable_takes_at_least_one_value(var));

    // each variable in the violator has to take at least one value that is
    // left in its domain...
    stringstream proof_step;
    proof_step << "p";
    bool first = true;
    for (auto & c : at_least_one_constraints) {
        proof_step << " " << c;
        if (! first)
            proof_step << " +";
        first = false;
    }

    // and each value in the component can only be used once
    for (const auto & val : hall_values)
        proof_step << " " << constraint_numbers->at(val) << " +";

    logger.emit_proof_line(proof_step.str(), ProofLevel::Current);
}
