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
    ProofLogger & logger, const ReasonLiterals & reason, SimpleIntegerVariableID v, bool lower, Integer bound) -> ConditionalBound
{
    // V-form, so the line cancels against the V-form channel rows.
    auto sum = lower ? WPBSum{} + 1_i * v : WPBSum{} + -1_i * v;
    auto rhs = lower ? bound : -bound;
    auto line = logger.emit_rup_proof_line_under_reason(reason, sum >= rhs, ProofLevel::Temporary);
    return ConditionalBound{sum, rhs, HalfReifyOnConjunctionOf{}, line};
}

auto gcs::innards::product_justify::channel_bound_to_magnitude(ProofLogger & logger, const ConditionalBound & operand_bound,
    SimpleIntegerVariableID v, const product_enc::MagnitudeChannel & channel, bool negative_branch) -> ConditionalBound
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
    return ConditionalBound{mag_sum, operand_bound.rhs, cases, line};
}

auto gcs::innards::product_justify::grid_sum_lower_bound(ProofLogger & logger, const ReasonLiterals & reason,
    const product_enc::BitProductGrid & grid, const SimpleOrProofOnlyIntegerVariableID & bits_a, const ConditionalBound & a_lb,
    const ConditionalBound & b_lb) -> ConditionalBound
{
    auto cases = merge_cases(a_lb.cases, b_lb.cases);

    // A non-positive magnitude bound multiplies out to the trivial
    // grid-sum >= 0, which every cell's non-negativity gives for free.
    if (a_lb.rhs <= 0_i || b_lb.rhs <= 0_i) {
        auto line = logger.emit_under_reason(ImpliesProofRule{}, logger.reify(grid.sum >= 0_i, cases), ProofLevel::Temporary, reason);
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
    auto line = outer.emit(logger, ProofLevel::Temporary);

    return ConditionalBound{grid.sum, a_lb.rhs * b_lb.rhs, cases, line};
}

auto gcs::innards::product_justify::grid_sum_upper_bound(ProofLogger & logger, const ReasonLiterals & reason, product_enc::BitProductGrid & grid,
    const SimpleOrProofOnlyIntegerVariableID & bits_a, const SimpleOrProofOnlyIntegerVariableID & bits_b, const ConditionalBound & a_ub,
    const ConditionalBound & b_ub) -> ConditionalBound
{
    auto cases = merge_cases(a_ub.cases, b_ub.cases);

    // The bounds arrive as -mag >= -value; live sign branches always give a
    // non-negative magnitude bound value.
    auto a_val = -a_ub.rhs, b_val = -b_ub.rhs;
    if (a_val < 0_i || b_val < 0_i)
        throw UnexpectedException{"magnitude upper bound is negative"};

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
                cell.w_a = logger.emit_rup_proof_line(
                    WPBSum{} + 1_i * ! cell.flag + 1_i * ProofBitVariable{bits_a, i, false} + 1_i * ProofBitVariable{bits_b, j, true} >= 1_i,
                    ProofLevel::Top);
            inner_w_a.add(*cell.w_a, power2(j));
            if (! cell.w_b)
                cell.w_b = logger.emit_rup_proof_line(WPBSum{} + 1_i * ! cell.flag + 1_i * ProofBitVariable{bits_a, i, true} >= 1_i, ProofLevel::Top);
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
    auto line = outer.emit(logger, ProofLevel::Temporary);

    return ConditionalBound{grid.neg_sum, -(a_val * b_val), cases, line};
}
