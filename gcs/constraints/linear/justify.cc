#include <gcs/constraints/linear/justify.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>

#include <util/enumerate.hh>

#include <sstream>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::pair;
using std::stringstream;
using std::variant;
using std::vector;

auto gcs::innards::justify_linear_bounds(
    ProofLogger & logger,
    const auto & coeff_vars,
    const vector<pair<Integer, Integer>> & bounds,
    const SimpleIntegerVariableID & change_var,
    bool second_constraint_for_equality,
    ProofLine proof_line) -> void
{
    vector<pair<Integer, variant<ProofLine, XLiteral>>> terms_to_sum;
    terms_to_sum.emplace_back(1_i, second_constraint_for_equality ? proof_line + 1 : proof_line);

    Integer change_var_coeff = 0_i;
    for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
        if (get_var(cv) == change_var) {
            change_var_coeff = get_coeff(cv);
            continue;
        }

        // the following line of logic is definitely correct until you inevitably
        // discover otherwise
        bool upper = (get_coeff(cv) < 0_i) != second_constraint_for_equality;

        auto literal_defining_proof_line = logger.names_and_ids_tracker().need_pol_item_defining_literal(
            upper ? get_var(cv) < bounds[idx].second + 1_i : get_var(cv) >= bounds[idx].first);

        terms_to_sum.emplace_back(abs(get_coeff(cv)), literal_defining_proof_line);
    }

    stringstream step;
    step << "pol";
    bool first = true;
    for (auto & c_and_l : terms_to_sum) {
        overloaded{
            [&](const XLiteral & l) {
                if (c_and_l.first == 1_i)
                    step << " " << logger.names_and_ids_tracker().pb_file_string_for(l);
                else
                    step << " " << logger.names_and_ids_tracker().pb_file_string_for(l) << " " << c_and_l.first << " *";
            },
            [&](const ProofLine & l) {
                if (c_and_l.first == 1_i)
                    step << " " << l;
                else
                    step << " " << l << " " << c_and_l.first << " *";
            }}
            .visit(c_and_l.second);
        if (! first)
            step << " +";
        first = false;
    }
    if (change_var_coeff != 1_i)
        step << " " << abs(change_var_coeff) << " d";
    step << ';';
    logger.emit_proof_line(step.str(), ProofLevel::Temporary);
}

template auto gcs::innards::justify_linear_bounds(
    ProofLogger & logger,
    const SumOf<Weighted<SimpleIntegerVariableID>> & coeff_vars,
    const vector<pair<Integer, Integer>> & bounds,
    const SimpleIntegerVariableID & change_var,
    bool second_constraint_for_equality,
    ProofLine proof_line) -> void;

template auto gcs::innards::justify_linear_bounds(
    ProofLogger & logger,
    const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & coeff_vars,
    const vector<pair<Integer, Integer>> & bounds,
    const SimpleIntegerVariableID & change_var,
    bool second_constraint_for_equality,
    ProofLine proof_line) -> void;

template auto gcs::innards::justify_linear_bounds(
    ProofLogger & logger,
    const SumOf<SimpleIntegerVariableID> & coeff_vars,
    const vector<pair<Integer, Integer>> & bounds,
    const SimpleIntegerVariableID & change_var,
    bool second_constraint_for_equality,
    ProofLine proof_line) -> void;
