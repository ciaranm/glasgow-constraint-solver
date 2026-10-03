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

    bool any_bound_added = false;
    for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
        if (get_var(cv) == change_var)
            continue;

        // the following line of logic is definitely correct until you inevitably
        // discover otherwise
        bool upper = (get_coeff(cv) < 0_i) != second_constraint_for_equality;
        auto lit = upper ? get_var(cv) <= bounds[idx].second : get_var(cv) >= bounds[idx].first;

        // A bound the term's own bits cannot violate (a 0/1 variable at 0, for
        // a positive coefficient) has a defining line that constrains nothing,
        // so adding it only swaps the term's bits for a constant. Leaving them
        // in instead costs the RUP below nothing: unassigned, they add exactly
        // as much to the line's maximum as to its degree, and any assignment
        // only lowers the maximum, so the slack is never more than it would
        // have been with the bound added. On a sum of 0/1 variables this is
        // almost every term (issue #1035).
        if (logger.names_and_ids_tracker().bit_sum_implies(lit))
            continue;

        pol.add_for_literal(logger.names_and_ids_tracker(), lit, abs(get_coeff(cv)));
        any_bound_added = true;
    }

    // There used to be a division by the changing variable's coefficient here.
    // Once every other term has cancelled it buys unit propagation nothing ---
    // what is left is that one variable's bits and false flags, and a line
    // c * x + ... >= d propagates x's bits exactly as its division by c does
    // --- and with the terms above left in, rounding their coefficients up
    // would loosen the line enough to lose the RUP.
    //
    // With no bound added, the pol would only restate its base line, which the
    // RUP can use as it stands.
    if (any_bound_added)
        pol.emit(logger, ProofLevel::Temporary);
}

auto gcs::innards::justify_linear_contrapositive(ProofLogger & logger, const auto & coeff_vars, const LinearBounds & bounds, ProofLine proof_line)
    -> void
{
    // As justify_linear_bounds, but no variable is changing: every term is
    // cancelled against its bound, leaving the half-reified stage line's
    // negated gate alone on the left of an infeasible constraint, from which
    // the gate negation follows by unit propagation.
    PolBuilder pol;
    pol.enable_deview_mode(logger.names_and_ids_tracker());
    pol.add(proof_line);

    bool any_bound_added = false;
    for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
        bool upper = get_coeff(cv) < 0_i;
        auto lit = upper ? get_var(cv) <= bounds[idx].second : get_var(cv) >= bounds[idx].first;
        // As in justify_linear_bounds: a bound the bits cannot violate is left
        // out, and its term's bits with it, at no cost to the slack.
        if (logger.names_and_ids_tracker().bit_sum_implies(lit))
            continue;
        pol.add_for_literal(logger.names_and_ids_tracker(), lit, abs(get_coeff(cv)));
        any_bound_added = true;
    }

    if (any_bound_added)
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

template auto gcs::innards::justify_linear_contrapositive(
    ProofLogger & logger, const SumOf<Weighted<SimpleIntegerVariableID>> & coeff_vars, const LinearBounds & bounds, ProofLine proof_line) -> void;

template auto gcs::innards::justify_linear_contrapositive(ProofLogger & logger, const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & coeff_vars,
    const LinearBounds & bounds, ProofLine proof_line) -> void;

template auto gcs::innards::justify_linear_contrapositive(
    ProofLogger & logger, const SumOf<SimpleIntegerVariableID> & coeff_vars, const LinearBounds & bounds, ProofLine proof_line) -> void;
