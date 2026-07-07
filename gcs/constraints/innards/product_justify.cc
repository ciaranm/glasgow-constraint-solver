#include <gcs/constraints/innards/product_justify.hh>
#include <gcs/exception.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>

#include <util/overloaded.hh>

#include <map>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::product_justify;

using std::vector;

auto gcs::innards::product_justify::def_line_for(ProofLogger & logger, const IntegerVariableCondition & cond) -> std::optional<ProofLine>
{
    // a condition on a constant is literally true or false: no definition
    if (is_constant_variable(cond.var))
        return std::nullopt;
    auto def = logger.names_and_ids_tracker().need_pol_item_defining_literal(cond);
    return overloaded{[&](const ProofLine & line) -> std::optional<ProofLine> { return line; },
        [&](const XLiteral &) -> std::optional<ProofLine> {
            // a primitive atom (say, a declared domain boundary) has no
            // reified definition to cite; callers fall back to RUP
            return std::nullopt;
        }}
        .visit(def);
}

auto gcs::innards::product_justify::add_condition_def_hints(ProofLogger & logger, const IntegerVariableCondition & cond, vector<ProofLine> & hints)
    -> void
{
    auto add = [&](const IntegerVariableCondition & c) {
        if (auto def = def_line_for(logger, c))
            hints.emplace_back(*def);
    };
    add(cond);
    add(! cond);
    switch (cond.op) {
        using enum VariableConditionOperator;
    case Equal:
    case NotEqual:
        add(cond.var >= cond.value);
        add(cond.var < cond.value);
        add(cond.var >= cond.value + 1_i);
        break;
    case GreaterEqual:
    case Less:
    case InRange:
    case NotInRange: break;
    }
}

auto gcs::innards::product_justify::add_order_bridge_hints(ProofLogger & logger, const IntegerVariableCondition & cond, vector<ProofLine> & hints)
    -> void
{
    // Unit propagation cannot cross between two order atoms of the same
    // variable through their bit-level definitions alone (the bits stay
    // unpinned), and the ladder link lines the tracker emits at atom
    // creation are not recorded anywhere we can cite. So pol-derive the
    // needed ladder clause [v>=h] -> [v>=l] from the two atoms' defining
    // rows, exactly as the tracker builds its own chain lines, and hint it.
    auto bridge = [&](IntegerVariableID v, Integer h, Integer l) {
        if (h <= l)
            return;
        if ((! def_line_for(logger, v >= h)) || (! def_line_for(logger, v < l)))
            return;
        PolBuilder b;
        b.add_for_literal(logger.names_and_ids_tracker(), v < l).add_for_literal(logger.names_and_ids_tracker(), v >= h).saturate();
        hints.emplace_back(b.emit(logger, ProofLevel::Temporary));
    };

    // The sign clauses test strictness through [v>=1], [v>=0] and the eq0
    // atoms only, so those are the bridge targets that matter.
    switch (cond.op) {
        using enum VariableConditionOperator;
    case GreaterEqual:
        bridge(cond.var, cond.value, 1_i);
        bridge(cond.var, cond.value, 0_i);
        break;
    case Less:
        // ~[v>=k] with k <= 0 refutes [v>=0] through the same clause
        bridge(cond.var, 0_i, cond.value);
        break;
    case Equal:
        // the eq atom's own defining rows (hinted alongside) pin
        // [v>=k] and ~[v>=k+1]; bridge those onward
        bridge(cond.var, cond.value, 1_i);
        bridge(cond.var, cond.value, 0_i);
        bridge(cond.var, 0_i, cond.value + 1_i);
        break;
    case NotEqual:
    case InRange:
    case NotInRange: break;
    }
}

namespace
{

    // The union of two case sets: premises built from two operands carry
    // both operands' sign-case literals.
    auto merge_cases(const HalfReifyOnConjunctionOf & a, const HalfReifyOnConjunctionOf & b) -> HalfReifyOnConjunctionOf
    {
        auto result = a;
        for (const auto & lit : b)
            result.emplace_back(lit);
        return result;
    }
}

auto gcs::innards::product_justify::derive_operand_bound(
    ProofLogger & logger, const ReasonLiterals & reason, IntegerVariableID v, bool lower, Integer bound, ProofLevel result_level) -> ConditionalBound
{
    // The bound atom's defining row already carries the claim in V-form, so
    // cite it directly rather than restating it: the extra gate term it
    // brings along rides through the downstream pol chains as one more
    // reason-shaped rider, and dies wherever the reason's units pin the
    // atom. Only lines up when the cited bound is itself carried by the
    // reason (the drivers always arrange this); otherwise fall back to RUP.
    auto sum = lower ? WPBSum{} + 1_i * v : WPBSum{} + -1_i * v;
    auto rhs = lower ? bound : -bound;
    auto def = reason.empty() ? std::nullopt : def_line_for(logger, lower ? v >= bound : v < bound + 1_i);
    auto line = def ? *def : logger.emit_rup_proof_line_under_reason(reason, sum >= rhs, result_level);
    return ConditionalBound{sum, rhs, HalfReifyOnConjunctionOf{}, line};
}

auto gcs::innards::product_justify::derive_assumed_operand_bound(
    ProofLogger & logger, IntegerVariableID v, bool lower, Integer bound, ProofLevel result_level) -> ConditionalBound
{
    // One `ia` citing the assumed atom's definition: the claim is exactly
    // that definition's forward half, but the restatement is load-bearing —
    // it renormalises the gate coefficient to reify's choice, which the
    // syntactic `ia` implications in the grid row procedures rely on when
    // this bound composes with view channel rows (Power's factor paths).
    // Citing the definition directly fails verification there.
    auto sum = lower ? WPBSum{} + 1_i * v : WPBSum{} + -1_i * v;
    auto rhs = lower ? bound : -bound;
    auto cases = HalfReifyOnConjunctionOf{lower ? v >= bound : v < bound + 1_i};
    auto def = def_line_for(logger, lower ? v >= bound : v < bound + 1_i);
    auto line = def ? logger.emit(ImpliesProofRule{*def}, logger.reify(sum >= rhs, cases), result_level)
                    : logger.emit_rup_proof_line(logger.reify(sum >= rhs, cases), result_level);
    return ConditionalBound{sum, rhs, cases, line};
}

auto gcs::innards::product_justify::channel_bound_to_magnitude(ProofLogger & logger, const ConditionalBound & operand_bound, IntegerVariableID v,
    const product_enc::MagnitudeChannel & channel, bool negative_branch, bool strengthen_nonzero) -> ConditionalBound
{
    if (operand_bound.sum.terms.size() != 1 || abs(operand_bound.sum.terms[0].coefficient) != 1_i)
        throw UnexpectedException{"operand bound is not a single +/-v term"};
    auto is_lower = operand_bound.sum.terms[0].coefficient == 1_i;

    // Under [v>=0] the channel pins mag = v, so a bound on v maps to the same
    // bound on mag; under [v<0] it pins mag = -v, so the direction flips.
    // Adding the matching channel row cancels the v terms:
    //   pos, lower:  (v >= b)  + ([v>=0] => -v + mag >= 0)  ->   mag >= b
    //   pos, upper:  (-v >= -b) + ([v>=0] => v - mag >= 0)  ->  -mag >= -b
    //   neg, lower:  (v >= b)  + ([v<0] => -v - mag >= 0)   ->  -mag >= b
    //   neg, upper:  (-v >= -b) + ([v<0] => v + mag >= 0)   ->   mag >= -b
    auto row = negative_branch ? (is_lower ? channel.neg_le : channel.neg_ge) : (is_lower ? channel.pos_le : channel.pos_ge);
    auto mag_coeff = (is_lower != negative_branch) ? 1_i : -1_i;

    PolBuilder builder;
    builder.add(operand_bound.line).add(row);
    auto line = builder.emit(logger, ProofLevel::Temporary);

    auto mag_sum = WPBSum{};
    mag_sum += overloaded{[&](const SimpleIntegerVariableID & m) { return Weighted<PseudoBooleanTerm>{mag_coeff, m}; },
        [&](const ProofOnlySimpleIntegerVariableID & m) {
            return Weighted<PseudoBooleanTerm>{mag_coeff, m};
        }}.visit(channel.mag);

    auto cases = merge_cases(operand_bound.cases, HalfReifyOnConjunctionOf{negative_branch ? v < 0_i : v >= 0_i});

    // A magnitude lower bound of zero or less is useless to the grid
    // procedures. When the caller needs strictness (a spanning co-factor
    // whose zero case the driver's final RUP will close through the grid),
    // add [v != 0] to the cases and lift the bound to 1: RUP, since the
    // branch atom plus [v != 0] give |v| >= 1 through the eq0 rows and the
    // channel. (The old code's mysterious RHS clamp did this via reif
    // riders; here it is an explicit, documented choice.)
    if (strengthen_nonzero && mag_coeff == 1_i && operand_bound.rhs < 1_i) {
        cases = merge_cases(cases, HalfReifyOnConjunctionOf{v != 0_i});
        auto strengthened = logger.emit_rup_proof_line(logger.reify(mag_sum >= 1_i, cases), ProofLevel::Temporary);
        return ConditionalBound{mag_sum, 1_i, cases, strengthened};
    }

    return ConditionalBound{mag_sum, operand_bound.rhs, cases, line};
}

auto gcs::innards::product_justify::grid_sum_lower_bound(ProofLogger & logger, const ReasonLiterals & reason,
    const product_enc::BitProductGrid & grid, const SimpleOrProofOnlyIntegerVariableID & bits_a, const ConditionalBound & a_lb,
    const ConditionalBound & b_lb, ProofLevel result_level) -> ConditionalBound
{
    auto cases = merge_cases(a_lb.cases, b_lb.cases);

    // A non-positive magnitude bound multiplies out to the trivial
    // grid-sum >= 0, which every cell's non-negativity gives for free.
    if (a_lb.rhs <= 0_i || b_lb.rhs <= 0_i) {
        auto line = logger.emit_under_reason(ImpliesProofRule{}, logger.reify(grid.sum >= 0_i, cases), result_level, reason);
        return ConditionalBound{grid.sum, 0_i, cases, line};
    }

    // Thesis Justification Subprocedure 7.1, pure cutting planes. Per grid
    // row i: sum the [f] halves (prod_ij >= bit_a_i + bit_b_j - 1) weighted
    // 2^j against |b|'s lower bound; the bit_b terms cancel, leaving
    //   Sum_j 2^j prod_ij >= b_lb  whenever bit_a_i is set,
    // restated crisply as an implied line. The outer sum weights the rows
    // 2^i against |a|'s lower bound, giving grid_sum >= a_lb * b_lb.
    PolBuilder outer;
    auto n_rows = Integer{static_cast<long long>(grid.cells.size())};
    for (Integer i = 0_i; i < n_rows; ++i) {
        const auto & row = grid.cells[i.as_index()];
        PolBuilder inner;
        WPBSum row_sum{};
        auto n_cols = Integer{static_cast<long long>(row.size())};
        for (Integer j = 0_i; j < n_cols; ++j) {
            // the [f] half: prod_ij >= bit_a_i + bit_b_j - 1
            inner.add(row[j.as_index()].reverse_reif, power2(j));
            row_sum += power2(j) * row[j.as_index()].flag;
        }
        inner.add(b_lb.line);
        inner.emit(logger, ProofLevel::Temporary);
        auto implied = logger.emit_under_reason(ImpliesProofRule{std::make_optional<ProofLine>(ProofLineNumber{-1})},
            logger.reify(row_sum + b_lb.rhs * ProofBitVariable{bits_a, i, false} >= b_lb.rhs, cases), ProofLevel::Temporary, reason);
        outer.add(implied, power2(i));
    }
    outer.add(a_lb.line, b_lb.rhs);
    auto line = outer.emit(logger, result_level);

    return ConditionalBound{grid.sum, a_lb.rhs * b_lb.rhs, cases, line};
}

auto gcs::innards::product_justify::grid_sum_upper_bound(ProofLogger & logger, const ReasonLiterals & reason, product_enc::BitProductGrid & grid,
    const SimpleOrProofOnlyIntegerVariableID & bits_a, const SimpleOrProofOnlyIntegerVariableID & bits_b, const ConditionalBound & a_ub,
    const ConditionalBound & b_ub, ProofLevel result_level) -> ConditionalBound
{
    auto cases = merge_cases(a_ub.cases, b_ub.cases);

    // The bounds arrive as -mag >= -value; live sign branches always give a
    // non-negative magnitude bound value.
    auto a_val = -a_ub.rhs, b_val = -b_ub.rhs;
    if (a_val < 0_i || b_val < 0_i)
        throw UnexpectedException{"magnitude upper bound is negative"};

    // A zero magnitude empties the grid outright: under the zero side's bound
    // line its bits are all zero, and the [r] halves then clear every cell,
    // so the claim is plain RUP -- and the pol scaling below would need a
    // zero coefficient, which PolBuilder rightly refuses.
    if (a_val == 0_i || b_val == 0_i) {
        auto line = logger.emit_under_reason(RUPProofRule{}, logger.reify(grid.neg_sum >= 0_i, cases), result_level, reason);
        return ConditionalBound{grid.neg_sum, 0_i, cases, line};
    }

    // Thesis Justification Subprocedure 7.2. Unlike the lower bound there is
    // no known short pure-cutting-planes derivation; each grid row's bound
    //   Sum_j 2^j ~prod_ij + b_val * bit_a_i >= 2^m - 1
    // (row sum <= b_val when bit_a_i is set, all cells clear otherwise) is
    // derived by contradiction in a small subproof, from the per-cell W-lines
    //   w_a: ~prod_ij + ~bit_a_i + bit_b_j >= 1   (prod and a_i force b_j)
    //   w_b: ~prod_ij + bit_a_i >= 1              (prod forces a_i)
    // which are plain RUP off the [r] halves and cached in the cells at Top
    // level, since they do not depend on the bound values. The outer sum then
    // weights the rows 2^i against |a|'s upper bound line.
    PolBuilder outer;
    auto n_rows = Integer{static_cast<long long>(grid.cells.size())};
    for (Integer i = 0_i; i < n_rows; ++i) {
        auto & row = grid.cells[i.as_index()];
        PolBuilder inner_w_a, inner_w_b;
        WPBSum neg_row_sum{};
        auto n_cols = Integer{static_cast<long long>(row.size())};
        for (Integer j = 0_i; j < n_cols; ++j) {
            auto & cell = row[j.as_index()];
            if (! cell.w_a)
                cell.w_a = logger.emit(RUPProofRule{vector<ProofLine>{cell.forwards_reif}},
                    WPBSum{} + 1_i * ! cell.flag + 1_i * ProofBitVariable{bits_a, i, false} + 1_i * ProofBitVariable{bits_b, j, true} >= 1_i,
                    ProofLevel::Top);
            inner_w_a.add(*cell.w_a, power2(j));
            if (! cell.w_b)
                cell.w_b = logger.emit(RUPProofRule{vector<ProofLine>{cell.forwards_reif}},
                    WPBSum{} + 1_i * ! cell.flag + 1_i * ProofBitVariable{bits_a, i, true} >= 1_i, ProofLevel::Top);
            inner_w_b.add(*cell.w_b, power2(j));
            neg_row_sum += power2(j) * ! cell.flag;
        }
        inner_w_a.add(b_ub.line);
        auto line_w_a = inner_w_a.emit(logger, ProofLevel::Temporary);
        auto line_w_b = inner_w_b.emit(logger, ProofLevel::Temporary);

        auto rhs = power2(n_cols) - 1_i;
        auto desired = logger.reify(logger.reify(neg_row_sum + b_val * ProofBitVariable{bits_a, i, true} >= rhs, cases), reason);
        std::map<ProofGoal, Subproof> subproofs{};
        subproofs.emplace("#1", Subproof{[&](ProofLogger & sub_logger) {
            PolBuilder first;
            first.add(line_w_a).add(ProofLineNumber{-2}).saturate();
            first.emit(sub_logger, ProofLevel::Temporary);
            PolBuilder second;
            second.add(line_w_b).add(ProofLineNumber{-3}).saturate();
            second.emit(sub_logger, ProofLevel::Temporary);
            sub_logger.emit_proof_line("rup >= 1 : -1 -2;", ProofLevel::Temporary);
        }});
        auto resolvent = logger.emit_red_proof_line(desired, {}, ProofLevel::Temporary, subproofs);
        outer.add(resolvent, power2(i));
    }
    outer.add(a_ub.line, b_val);
    auto line = outer.emit(logger, result_level);

    return ConditionalBound{grid.neg_sum, -(a_val * b_val), cases, line};
}

auto gcs::innards::product_justify::channel_grid_bound_to_result(ProofLogger & logger, const ReasonLiterals & reason, IntegerVariableID v3,
    const product_enc::ResultChannel & channel, const ConditionalBound & grid_bound, bool result_negative, bool lower,
    const vector<ProofLine> & claim_hints) -> ConditionalBound
{
    // The mag_Z rows pin |z| = grid sum, gated on z's sign atom; the atom
    // itself is entailed by the operand sign-case atoms through the sign
    // clauses (via the eq0 definition rows when an operand's non-negative
    // branch includes zero), so it is discharged by RUP rather than kept in
    // the cases. A magnitude bound flips direction on a negative result,
    // exactly as in the operand channel.
    auto row = lower ? (result_negative ? channel.lt0_le : channel.ge0_ge) : (result_negative ? channel.lt0_ge : channel.ge0_le);
    PolBuilder builder;
    builder.add(grid_bound.line).add(row);
    auto combined = builder.emit(logger, ProofLevel::Temporary);

    // No standalone sign-atom discharge: a mixed sign case does not entail
    // the result's sign when the non-negative operand may be zero (y = 0
    // gives z = 0), so that claim would simply be false. The bound claim
    // itself is RUP instead: its negation either pins the result's sign atom
    // (activating `combined`'s gated row), or unit propagation closes
    // through the sign clauses, the eq0 definition rows and the grid.
    auto coeff = (lower != result_negative) ? 1_i : -1_i;
    auto sum = WPBSum{} + coeff * v3;
    auto hints = claim_hints;
    if (! hints.empty()) {
        hints.emplace_back(combined);
        // the bridges from the negated claim's units to the bit level: the
        // definitions of every reason and case literal (a reason unit only
        // reaches the channel and grid rows through its atom's defining
        // rows), and the ladder clauses linking each such atom to the
        // sign-clause thresholds. The claimed bound itself needs no atom
        // definitions: the claim is stated over the result's bits, so no
        // atom of it appears anywhere the checker propagates -- and minting
        // one would add permanent defining rows for a fresh raw grid value
        // at every inference, growing the live database and turning every
        // later hint-free RUP step quadratic over a search tree.
        for (const auto & cl : grid_bound.cases)
            if (const auto * pl = std::get_if<ProofLiteral>(&cl))
                if (const auto * l = std::get_if<Literal>(pl))
                    if (const auto * cond = std::get_if<IntegerVariableCondition>(l)) {
                        add_condition_def_hints(logger, *cond, hints);
                        add_order_bridge_hints(logger, *cond, hints);
                    }
        for (const auto & rl : reason)
            if (const auto * pl = std::get_if<ProofLiteral>(&rl))
                if (const auto * l = std::get_if<Literal>(pl))
                    if (const auto * cond = std::get_if<IntegerVariableCondition>(l)) {
                        add_condition_def_hints(logger, *cond, hints);
                        add_order_bridge_hints(logger, *cond, hints);
                    }
    }
    // an empty hint list is not "no hints" to the checker: it restricts
    // propagation to nothing at all
    auto rule = hints.empty() ? RUPProofRule{} : RUPProofRule{hints};
    auto line = logger.emit_under_reason(rule, logger.reify(sum >= grid_bound.rhs, grid_bound.cases), ProofLevel::Temporary, reason);
    return ConditionalBound{sum, grid_bound.rhs, grid_bound.cases, line};
}

auto gcs::innards::product_justify::conclude_by_sign_cases(ProofLogger & logger, const ReasonLiterals & reason, const WPBSumLE & conclusion,
    const vector<SignCaseDimension> & dims, const vector<std::optional<ConditionalBound>> & premise_by_pattern,
    const vector<Literal> & zero_refutations, SubproofRUPHints hint_rups) -> ProofLine
{
    if (premise_by_pattern.size() != (1u << dims.size()))
        throw UnexpectedException{"wrong number of case patterns"};

    // Hints for the subproof's RUP steps, assembled outside the subproof so
    // the defining rows and ladder bridges land at the outer level. A dead
    // pattern's clause refutes either shallowly (a branch atom clashes with
    // the reason's units through the order ladder) or numerically (the
    // opposite corner is live, and its premise meets the negated goal), and
    // the closing contradiction propagates between the negated goal and the
    // cut result; when the premises cancel exactly against the goal, the
    // union of premise lines, premise case-literal defs, reason defs and
    // their bridges covers all of these. Hinting keeps the checker off the
    // hint-free path, which costs time proportional to the live database at
    // every step.
    vector<ProofLine> case_hints;
    if (hint_rups == SubproofRUPHints::Assemble) {
        auto add_hints_for = [&](const Literal & l) {
            if (const auto * cond = std::get_if<IntegerVariableCondition>(&l)) {
                add_condition_def_hints(logger, *cond, case_hints);
                add_order_bridge_hints(logger, *cond, case_hints);
            }
        };
        for (const auto & dim : dims)
            add_hints_for(dim.positive_atom);
        for (const auto & rl : reason)
            if (const auto * pl = std::get_if<ProofLiteral>(&rl))
                if (const auto * l = std::get_if<Literal>(pl))
                    add_hints_for(*l);
        for (const auto & premise : premise_by_pattern)
            if (premise) {
                case_hints.emplace_back(premise->line);
                for (const auto & cl : premise->cases)
                    if (const auto * pl = std::get_if<ProofLiteral>(&cl))
                        if (const auto * l = std::get_if<Literal>(pl))
                            add_hints_for(*l);
            }
    }

    auto goal = logger.reify(conclusion, reason);
    std::map<ProofGoal, Subproof> subproofs{};
    subproofs.emplace("#1", Subproof{[&](ProofLogger & sub_logger) {
        // The negated goal is the last line added when the subproof opens.
        auto negation = sub_logger.get_current_proof_line();
        auto sub_hints = case_hints;
        sub_hints.emplace_back(negation);
        // an empty hint list would restrict propagation to nothing at all
        auto rup_rule = [&](const vector<ProofLine> & hints) {
            return hint_rups == SubproofRUPHints::Assemble ? RUPProofRule{hints} : RUPProofRule{};
        };

        // One clause per case pattern: added premise for a live case, plain
        // RUP for a dead one (its branch atoms contradict the reason's units
        // through the order encoding).
        vector<ProofLine> clauses;
        for (std::size_t pattern = 0; pattern < premise_by_pattern.size(); ++pattern) {
            if (premise_by_pattern[pattern] && premise_by_pattern[pattern]->sum.terms.empty()) {
                // Already a refutation clause over its case atoms (a factor
                // bound's clash with the reason's bounds): adding the negated
                // goal would only inject its terms as free slack.
                clauses.emplace_back(premise_by_pattern[pattern]->line);
            }
            else if (premise_by_pattern[pattern]) {
                PolBuilder builder;
                builder.add(premise_by_pattern[pattern]->line).add(negation).saturate();
                clauses.emplace_back(builder.emit(sub_logger, ProofLevel::Temporary));
            }
            else {
                auto clause = WPBSum{};
                for (std::size_t k = 0; k < dims.size(); ++k)
                    clause += 1_i * ((pattern & (1u << k)) ? dims[k].positive_atom : dims[k].negative_atom);
                clauses.emplace_back(sub_logger.emit(rup_rule(sub_hints), clause >= 1_i, ProofLevel::Temporary));
            }
        }

        // The fixed nested cut: pair patterns differing in dimension k and
        // saturate, one dimension at a time, until one line remains.
        for (std::size_t k = 0; k < dims.size(); ++k) {
            vector<ProofLine> next;
            for (std::size_t low = 0; low < clauses.size(); low += 2) {
                PolBuilder builder;
                builder.add(clauses[low]).add(clauses[low + 1]).saturate();
                next.emplace_back(builder.emit(sub_logger, ProofLevel::Temporary));
            }
            clauses = std::move(next);
        }

        // Unit clauses refuting a strengthened co-factor's zero case: [v=0]
        // forces the magnitude, the grid, and hence the result to zero, which
        // the reason's result bounds exclude - all by unit propagation. As
        // units these cascade into the cut result's leftover [v=0] terms,
        // which mere propagation could otherwise satisfy rather than refute.
        // These stay hint-free: their conflict path runs through the whole
        // encoding (channels, w-lines, grid), which no local hint set covers.
        auto closing_hints = sub_hints;
        closing_hints.emplace_back(clauses[0]);
        for (const auto & lit : zero_refutations)
            closing_hints.emplace_back(sub_logger.emit_rup_proof_line(WPBSum{} + 1_i * lit >= 1_i, ProofLevel::Temporary));

        sub_logger.emit(rup_rule(closing_hints), WPBSum{} >= 1_i, ProofLevel::Temporary);
    }});

    return logger.emit_red_proof_line(goal, {}, ProofLevel::Temporary, subproofs);
}
