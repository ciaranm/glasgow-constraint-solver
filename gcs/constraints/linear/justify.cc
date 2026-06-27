#include <gcs/constraints/linear/justify.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>

#include <util/enumerate.hh>

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::pair;

auto gcs::innards::justify_linear_bounds(ProofLogger & logger, const auto & coeff_vars, const LinearBounds & bounds,
    const SimpleIntegerVariableID & change_var, bool second_constraint_for_equality, pair<optional<ProofLine>, optional<ProofLine>> proof_lines)
    -> void
{
    // Deview mode: the propagator's coeff_vars list is the tidy_up_linear-sanitised
    // form (bare SimpleIntegerVariableIDs), but the OPB sum_line is emitted in the
    // user's views' bits. Deview mode substitutes the framework's deview-form line
    // (in X-bits) for proof_lines, matching the reason reifs that add_for_literal
    // pushes for bare SimpleIntegerVariableIDs.
    PolBuilder pol;
    pol.enable_deview_mode(logger.names_and_ids_tracker());
    pol.add(second_constraint_for_equality ? proof_lines.second.value() : proof_lines.first.value());

    Integer change_var_coeff = 0_i;
    for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
        if (get_var(cv) == change_var) {
            change_var_coeff = get_coeff(cv);
            continue;
        }

        // the following line of logic is definitely correct until you inevitably
        // discover otherwise
        bool upper = (get_coeff(cv) < 0_i) != second_constraint_for_equality;
        auto lit = upper ? get_var(cv) <= bounds[idx].second : get_var(cv) >= bounds[idx].first;
        pol.add_for_literal(logger.names_and_ids_tracker(), lit, abs(get_coeff(cv)));
    }

    if (change_var_coeff != 1_i)
        pol.divide_by(abs(change_var_coeff));

    pol.emit(logger, ProofLevel::Temporary);
}

template auto gcs::innards::justify_linear_bounds(ProofLogger & logger, const SumOf<Weighted<SimpleIntegerVariableID>> & coeff_vars,
    const LinearBounds & bounds, const SimpleIntegerVariableID & change_var, bool second_constraint_for_equality,
    pair<optional<ProofLine>, optional<ProofLine>> proof_line) -> void;

template auto gcs::innards::justify_linear_bounds(ProofLogger & logger, const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & coeff_vars,
    const LinearBounds & bounds, const SimpleIntegerVariableID & change_var, bool second_constraint_for_equality,
    pair<optional<ProofLine>, optional<ProofLine>> proof_line) -> void;

template auto gcs::innards::justify_linear_bounds(ProofLogger & logger, const SumOf<SimpleIntegerVariableID> & coeff_vars,
    const LinearBounds & bounds, const SimpleIntegerVariableID & change_var, bool second_constraint_for_equality,
    pair<optional<ProofLine>, optional<ProofLine>> proof_line) -> void;
