#include <gcs/constraints/multiply/hints.hh>
#include <gcs/constraints/multiply/multiply_bc.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/presolvers/auto_table.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/core.h>
#endif

#include <algorithm>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::make_pair;
using std::make_unique;
using std::map;
using std::max;
using std::min;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::unique_ptr;
using std::vector;
using std::ranges::set_union;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
#else
using fmt::format;
#endif

namespace
{
    Integer div_floor(Integer a, Integer b)
    {
        return ((a >= 0_i) != (b >= 0_i)) && (a != 0_i) ? (1_i - abs(a)) / abs(b) - 1_i : a / b;
    }

    Integer div_ceil(Integer a, Integer b)
    {
        return ((a >= 0_i) == (b >= 0_i)) && (a != 0_i) ? (abs(a) - 1_i) / abs(b) + 1_i : a / b;
    }

    using mult_bc::BitProductData;
    using mult_bc::ChannellingData;

    struct DerivedPBConstraint
    {
        WPBSum sum = WPBSum{};
        Integer rhs = 0_i;
        HalfReifyOnConjunctionOf half_reif = HalfReifyOnConjunctionOf{};
        optional<ReasonLiterals> reason = nullopt;
        ProofLine line;
    };

    struct DerivedBounds
    {
        DerivedPBConstraint lower;
        DerivedPBConstraint upper;
    };

    auto result_of_deriving(ProofLogger & logger, ProofRule rule, const WPBSumLE & ineq, const HalfReifyOnConjunctionOf & reif,
        const ProofLevel & proof_level, const ReasonLiterals & reason) -> DerivedPBConstraint
    {
        // Have to flip it again to store in the form lhs >= rhs
        WPBSum ge_lhs{};
        for (const auto & t : ineq.lhs.terms) {
            ge_lhs += -t.coefficient * t.variable;
        }

        auto res =
            DerivedPBConstraint{ge_lhs, -ineq.rhs, reif, reason, logger.emit_under_reason(rule, logger.reify(ineq, reif), proof_level, reason)};
        return res;
    }

    auto get_def_line_for_lit(ProofLogger & logger, const IntegerVariableCondition & cond) -> optional<ProofLine>
    {
        auto lower_def = logger.names_and_ids_tracker().need_pol_item_defining_literal(cond);
        auto proof_line = overloaded{
            [&](const ProofLine & line) -> optional<ProofLine> { return make_optional(line); }, //
            [&](const XLiteral & xlit) -> optional<ProofLine> {
                // Seems like a nonsense way to handle this, but anyway...
                auto axiom =
                    logger.emit_proof_line("ia 1 " + logger.names_and_ids_tracker().pb_file_string_for(xlit) + " >= 0;", ProofLevel::Temporary);
                return make_optional(axiom);
            } //
        }
                              .visit(lower_def);
        return proof_line;
    }

    auto get_rup_hints_for(ProofLogger & logger, const HalfReifyOnConjunctionOf & lits) -> vector<ProofLine>
    {
        auto rup_hints = vector<ProofLine>{};
        for (const auto & lit : lits) {
            if (const auto * p_lit = std::get_if<ProofLiteral>(&lit)) {
                if (const auto * l_lit = std::get_if<Literal>(p_lit)) {
                    if (const auto * cond = std::get_if<IntegerVariableCondition>(l_lit)) {
                        switch (cond->op) {
                        case VariableConditionOperator::Equal:
                            rup_hints.emplace_back(*get_def_line_for_lit(logger, cond->var >= cond->value));
                            rup_hints.emplace_back(*get_def_line_for_lit(logger, cond->var <= cond->value));
                            break;
                        case VariableConditionOperator::NotEqual:
                            rup_hints.emplace_back(*get_def_line_for_lit(logger, cond->var < cond->value));
                            rup_hints.emplace_back(*get_def_line_for_lit(logger, cond->var > cond->value));
                            break;
                        case VariableConditionOperator::GreaterEqual:
                        case VariableConditionOperator::Less: break;
                        case VariableConditionOperator::InRange:
                        case VariableConditionOperator::NotInRange:
                            // MultiplyBC's reasons and reifications are bounds and equalities only
                            throw UnimplementedException{};
                        }
                        rup_hints.emplace_back(*get_def_line_for_lit(logger, *cond));
                    }
                }
            }
        }
        return rup_hints;
    }

    auto add_lines(ProofLogger & logger, ProofLine line1, ProofLine line2, bool saturate = true) -> ProofLine
    {
        PolBuilder b;
        b.add(line1).add(line2);
        if (saturate)
            b.saturate();
        return b.emit(logger, ProofLevel::Temporary);
    }

    SimpleIntegerVariableID require_simple_iv(const PseudoBooleanTerm & var)
    {
        if (auto iv = std::get_if<IntegerVariableID>(&var)) {
            if (auto siv = std::get_if<SimpleIntegerVariableID>(iv)) {
                return *siv;
            }
            else
                throw UnexpectedException("Variant does not contain requested type");
        }
        else
            throw UnexpectedException("Variant does not contain requested type");
    }

    SimpleOrProofOnlyIntegerVariableID require_simple_or_po_iv(const PseudoBooleanTerm & var)
    {
        if (auto iv1 = std::get_if<ProofOnlySimpleIntegerVariableID>(&var)) {
            return *iv1;
        }
        else if (auto iv2 = std::get_if<IntegerVariableID>(&var)) {
            if (auto siv = std::get_if<SimpleIntegerVariableID>(iv2)) {
                return *siv;
            }
            else
                throw UnexpectedException("Variant does not contain requested type");
        }
        else
            throw UnexpectedException("Variant does not contain requested type");
    }

    // keep_sign_atom controls cake's ge0-gated channel only: the reified sign atom
    // ([v>=0] or [v<0]) is kept in the reification for a zero-spanning operand, so
    // the two branches resolve against each other; it is dropped when the operand's
    // sign is fixed by its domain (all-positive or all-negative), since then the
    // atom is entailed and a leftover would block the fusion resolution.
    auto channel_to_sign_bit(ProofLogger & logger, bool is_negative, const DerivedPBConstraint & constr,
        const map<SimpleIntegerVariableID, ChannellingData> & channelling_constraints,
        const map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> & mag_var, const ReasonLiterals & reason, bool keep_sign_atom = false,
        const optional<HalfReifyOnConjunctionOf> & assumption = nullopt) -> DerivedPBConstraint
    {
        if (constr.sum.terms.size() != 1 || abs(constr.sum.terms[0].coefficient) != 1_i)
            throw UnexpectedException{"Constraint not in a form that can be channelled."};

        SimpleIntegerVariableID var = require_simple_iv(constr.sum.terms[0].variable);
        auto is_lower_bound = constr.sum.terms[0].coefficient == 1_i;

        ProofLine channel_line;
        WPBSum channel_sum{};
        Integer channel_rhs = constr.rhs;
        auto reif = HalfReifyOnConjunctionOf{};

        // cake_pb_cp's magnitude channel is gated on the reified sign atom [v>=0]
        // rather than the two's-complement sign bit; reify accordingly.
        auto ge0_gated = channelling_constraints.contains(var) && channelling_constraints.at(var).ge0_gated;

        vector<ProofLine> rup_hints = {};
        if (is_negative && ! channelling_constraints.contains(var)) {
            throw UnexpectedException{"Missing channelling constraints."};
        }
        else if (is_negative) {
            // Negative
            reif = ge0_gated ? (keep_sign_atom ? HalfReifyOnConjunctionOf{var < 0_i} : HalfReifyOnConjunctionOf{})
                             : HalfReifyOnConjunctionOf{ProofBitVariable{var, 0_i, true}};
            // channel_rhs = -channel_rhs;
            if (is_lower_bound) {
                channel_line = channelling_constraints.at(var).neg_le;
                channel_sum += -1_i * mag_var.at(var);
            }
            else {
                channel_line = channelling_constraints.at(var).neg_ge;
                channel_sum += 1_i * mag_var.at(var);
            }

            rup_hints.emplace_back(add_lines(logger, channel_line, constr.line, false));
        }
        else if (channelling_constraints.contains(var)) {
            // A ge0-gated (cake) channel on a fixed-sign operand has its sign atom
            // entailed, so leave it OUT of the reification (keep_sign_atom false) and
            // let RUP discharge it: otherwise the fusion resolution keeps a residual
            // {ge0(x), ge0(y)} it can't eliminate (a fixed-sign operand yields no
            // opposite-sign conditional bound to resolve against). A zero-spanning
            // operand keeps [v>=0] so its two branches resolve. The legacy signed
            // path still conditions on the sign bit.
            reif = ge0_gated ? (keep_sign_atom ? HalfReifyOnConjunctionOf{var >= 0_i} : HalfReifyOnConjunctionOf{})
                             : HalfReifyOnConjunctionOf{ProofBitVariable{var, 0_i, false}};

            if (is_lower_bound) {
                channel_line = channelling_constraints.at(var).pos_le;
                channel_sum += 1_i * mag_var.at(var);
            }
            else {
                channel_line = channelling_constraints.at(var).pos_ge;
                channel_sum += -1_i * mag_var.at(var);
            }

            rup_hints.emplace_back(add_lines(logger, channel_line, constr.line, false));
        }
        else {
            channel_sum = constr.sum;
        }

        reif.emplace_back(var != 0_i);

        if (assumption) {
            for (const auto & a : *assumption) {
                reif.emplace_back(a);
                auto cond = get<IntegerVariableCondition>(get<Literal>(get<ProofLiteral>(a)));
                auto cond_line = get_def_line_for_lit(logger, cond);
                rup_hints.emplace_back(*cond_line);
            }
        }

        if (channel_sum.terms[0].coefficient == -1_i && channel_rhs >= 0_i) {
            channel_rhs = -1_i;
        }
        else if (channel_sum.terms[0].coefficient == 1_i && channel_rhs <= 0_i) {
            channel_rhs = 1_i;
        }

        // logger.emit_proof_comment("Chanelling RUP");
        // This might be a horribly bad idea...
        for (const auto & lit : reason) {
            auto cond = get<IntegerVariableCondition>(get<Literal>(get<ProofLiteral>(lit)));
            auto line = get_def_line_for_lit(logger, cond);
            if (line) {
                rup_hints.emplace_back(*line);
            }
        }

        if (channelling_constraints.contains(var)) {
            rup_hints.emplace_back(channelling_constraints.at(var).neg_ge);
            rup_hints.emplace_back(channelling_constraints.at(var).pos_ge);
            rup_hints.emplace_back(channelling_constraints.at(var).neg_le);
            rup_hints.emplace_back(channelling_constraints.at(var).pos_le);
        }

        for (const auto & lit : {var < 0_i, var != 0_i, var == 0_i, var >= 1_i}) {
            rup_hints.emplace_back(*get_def_line_for_lit(logger, lit));
        }

        return result_of_deriving(logger, RUPProofRule{rup_hints}, channel_sum >= channel_rhs, reif, ProofLevel::Temporary, reason);
    }

    auto channel_z_from_sign_bit(ProofLogger & logger, DerivedPBConstraint & constr, const SimpleIntegerVariableID & x,
        const SimpleIntegerVariableID & y, const SimpleIntegerVariableID & z,
        const map<SimpleIntegerVariableID, ChannellingData> & channelling_constraints, const ReasonLiterals & reason) -> DerivedPBConstraint
    {
        auto channel_reif = HalfReifyOnConjunctionOf{constr.half_reif};
        if (! channelling_constraints.contains(z))
            return result_of_deriving(logger, ImpliesProofRule{constr.line}, constr.sum >= constr.rhs, channel_reif, ProofLevel::Temporary, reason);

        auto is_lower_bound = constr.sum.terms[0].coefficient == 1_i;

        auto positive_sign = [&](ProofLiteralOrFlag condition) -> bool {
            return overloaded{
                [&](ProofLiteral & l) {
                    return overloaded{
                        [&](Literal & ll) { return is_literally_true(ll); }, //
                        [&](ProofVariableCondition &) {
                            throw UnexpectedException{"Sign should be bit, TrueLiteral{} or FalseLiteral{}."};
                            return false;
                        } //
                    }
                        .visit(l);
                }, //
                [&](ProofFlag &) {
                    throw UnexpectedException{"Sign should be bit, TrueLiteral{} or FalseLiteral{}."};
                    return false;
                },                                                 //
                [&](ProofBitVariable & b) { return ! b.positive; } //
            }
                .visit(condition);
        };

        bool z_negative;
        auto bit_assumptions = HalfReifyOnConjunctionOf{};
        for (const auto & cond : constr.half_reif) {
            if (holds_alternative<ProofBitVariable>(cond))
                bit_assumptions.emplace_back(cond);
        }
        if (bit_assumptions.empty())
            z_negative = false;
        else if (bit_assumptions.size() == 1)
            z_negative = ! positive_sign(bit_assumptions[0]);
        else if (bit_assumptions.size() == 2)
            z_negative = (positive_sign(bit_assumptions[0]) ^ positive_sign(bit_assumptions[1]));
        else
            throw UnexpectedException{"Can't channel back to z."};

        auto rup_sign = logger.emit_rup_proof_line(
            logger.reify(WPBSum{} + 1_i * (z_negative ? ProofBitVariable{z, 0_i, true} : ProofBitVariable{z, 0_i, false}) >= 1_i, channel_reif),
            ProofLevel::Temporary);

        ProofLine channel_line;
        if (z_negative) {
            if (is_lower_bound) {
                channel_line = add_lines(logger, constr.line, channelling_constraints.at(z).neg_le);
            }
            else {
                channel_line = add_lines(logger, constr.line, channelling_constraints.at(z).neg_ge);
            }
        }
        else {
            if (is_lower_bound) {
                channel_line = add_lines(logger, constr.line, channelling_constraints.at(z).pos_ge);
            }
            else {
                channel_line = add_lines(logger, constr.line, channelling_constraints.at(z).pos_le);
            }
        }

        auto result = add_lines(logger, channel_line, rup_sign);
        auto channel_sum = WPBSum{} + constr.sum.terms[0].coefficient * (z_negative ? -1_i : 1_i) * z;
        vector<ProofLine> rup_hints = {result};
        for (const auto & lit : reason) {
            auto cond = get<IntegerVariableCondition>(get<Literal>(get<ProofLiteral>(lit)));
            auto line = get_def_line_for_lit(logger, cond);
            if (line) {
                rup_hints.emplace_back(*line);
            }
        }

        for (const auto & var : {x, y, z}) {
            for (const auto & lit : {var < 0_i, var != 0_i, var == 0_i, var >= 1_i}) {
                rup_hints.emplace_back(*get_def_line_for_lit(logger, lit));
            }
        }

        if (channelling_constraints.contains(z)) {
            rup_hints.emplace_back(channelling_constraints.at(z).neg_ge);
            rup_hints.emplace_back(channelling_constraints.at(z).pos_ge);
            rup_hints.emplace_back(channelling_constraints.at(z).neg_le);
            rup_hints.emplace_back(channelling_constraints.at(z).pos_le);
        }

        rup_hints.emplace_back(rup_sign);

        return result_of_deriving(logger, RUPProofRule{rup_hints}, channel_sum >= constr.rhs, channel_reif, ProofLevel::Temporary, reason);
    }

    auto run_resolution(ProofLogger & logger, vector<pair<HalfReifyOnConjunctionOf, ProofLine>> premise_line) -> vector<ProofLine>
    {
        auto resolvable = [&](const HalfReifyOnConjunctionOf & c1, const HalfReifyOnConjunctionOf & c2) -> bool {
            auto opposites = 0;

            for (const auto & l1 : c1) {
                for (const auto & l2 : c2) {
                    if (l1 == ! l2)
                        opposites++;
                }
            }
            return opposites == 1;
        };

        auto resolve = [&](pair<HalfReifyOnConjunctionOf, ProofLine> c1,
                           pair<HalfReifyOnConjunctionOf, ProofLine> c2) -> pair<HalfReifyOnConjunctionOf, ProofLine> {
            auto line = add_lines(logger, c1.second, c2.second);

            auto lits = HalfReifyOnConjunctionOf{};

            auto found = false;
            for (auto l1 = c1.first.begin(); l1 != c1.first.end(); l1++) {
                for (auto l2 = c2.first.begin(); l2 != c2.first.end(); l2++) {
                    if ((*l1) == ! (*l2)) {
                        c1.first.erase(l1);
                        c2.first.erase(l2);
                        found = true;
                        break;
                    }
                }
                if (found)
                    break;
            }

            sort(c1.first);
            sort(c2.first);
            set_union(c1.first, c2.first, back_inserter(lits));
            return {lits, line};
        };

        if (premise_line.size() == 2) {
            auto line = add_lines(logger, premise_line[0].second, premise_line[1].second);
            return {line};
        }

        auto derived_empty = false;
        size_t found_c1;
        size_t found_c2;
        while (! derived_empty) {
            auto found = false;

            // Find two clauses that are resolvable
            for (size_t i = 0; i < premise_line.size(); i++) {
                for (size_t j = 0; j < premise_line.size(); j++) {
                    if (i == j)
                        continue;
                    if (resolvable(premise_line[i].first, premise_line[j].first)) {
                        // Resolve them
                        found = true;
                        found_c1 = i;
                        found_c2 = j;
                        auto c3 = resolve(premise_line[i], premise_line[j]);
                        premise_line.emplace_back(c3);

                        if (c3.first.empty())
                            derived_empty = true;

                        break;
                    }
                }
                if (found)
                    break;
            }

            if (! found)
                // Assume that we've done enough
                break;

            // Remove the resolved clauses
            premise_line[max(found_c1, found_c2)] = premise_line.back();
            premise_line.pop_back();
            premise_line[min(found_c1, found_c2)] = premise_line.back();
            premise_line.pop_back();
        }
        vector<ProofLine> finalised_premises;

        for (const auto & p : premise_line) {
            finalised_premises.emplace_back(p.second);
        }
        return finalised_premises;
    }

    auto derive_by_fusion_resolution(
        ProofLogger & logger, DerivedPBConstraint constr, vector<DerivedPBConstraint> premises, vector<ProofLine> hints = {}) -> DerivedPBConstraint
    {
        auto want_to_derive = logger.reify(logger.reify(constr.sum >= constr.rhs, constr.half_reif), *constr.reason);

        if (premises.empty())
            throw UnexpectedException{"Empty premise set for fusion resolution."};

        map<ProofGoal, Subproof> subproofs{};
        vector<pair<HalfReifyOnConjunctionOf, ProofLine>> premise_line{};

        auto subproof = [&](ProofLogger & logger) {
            auto weakened_premises = vector<DerivedPBConstraint>{};
            // First weaken the premises to match our desired constraint
            ProofLine negation_line = logger.get_current_proof_line();
            for (const auto & p : premises) {
                vector<ProofLine> rup_hints = hints;
                // A lot of mess to get correct rup hints
                auto further_hints = get_rup_hints_for(logger, p.half_reif);
                rup_hints.insert(rup_hints.end(), further_hints.begin(), further_hints.end());
                rup_hints.emplace_back(p.line);
                weakened_premises.emplace_back(result_of_deriving(logger, RUPProofRule{rup_hints}, // implies?
                    want_to_derive, p.half_reif, ProofLevel::Temporary, ReasonLiterals{}));
            }

            //  Then add the negation of our desired constraint to each of the weakened premises
            //  This should give us a collection of clauses
            for (const auto & p : weakened_premises) {
                premise_line.emplace_back(p.half_reif, add_lines(logger, negation_line, p.line, true));
            }

            if (premise_line.size() <= 1) {
                throw UnexpectedException{"Too few premises for fusion resolution."};
            }

            auto before_res = logger.get_current_proof_line().number - 1;
            run_resolution(logger, premise_line);
            auto after_res = logger.get_current_proof_line();
            for (auto & h = before_res; h <= after_res.number; h++) {
                hints.emplace_back(ProofLineNumber{h});
            }
            hints.emplace_back(negation_line);
            logger.emit(RUPProofRule{hints}, WPBSum{} >= 1_i, ProofLevel::Temporary);
        };

        subproofs.emplace("#1", subproof);

        return DerivedPBConstraint{constr.sum, constr.rhs, constr.half_reif, constr.reason,
            logger.emit_red_proof_line(want_to_derive, {}, ProofLevel::Temporary, subproofs)};
    }

    auto prove_positive_product_lower_bound(ProofLogger & logger, DerivedPBConstraint lb_1, DerivedPBConstraint lb_2, const SimpleIntegerVariableID z,
        const map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> & mag_var, const pair<ProofLine, ProofLine> z_eq_product_lines,
        vector<vector<BitProductData>> & bit_products, const ReasonLiterals & reason, bool z_ge0_gated, bool z_negative = false,
        const optional<pair<ProofLine, ProofLine>> & z_eq_product_lines_neg = nullopt) -> DerivedPBConstraint
    {
        // logger.emit_proof_comment("Prove Conditional Product Lower Bound:");
        auto mag_z_sum = WPBSum{};
        if (mag_var.contains(z))
            mag_z_sum += 1_i * mag_var.at(z);
        else
            mag_z_sum += 1_i * z;

        auto reif = HalfReifyOnConjunctionOf{};
        if (! lb_1.half_reif.empty())
            reif.insert(reif.end(), lb_1.half_reif.begin(), lb_1.half_reif.end());

        if (! lb_2.half_reif.empty())
            reif.insert(reif.end(), lb_2.half_reif.begin(), lb_2.half_reif.end());

        if (lb_1.rhs <= 0_i || lb_2.rhs <= 0_i)
            return result_of_deriving(logger, ImpliesProofRule{}, mag_z_sum >= 0_i, reif, ProofLevel::Temporary, reason);

        PolBuilder outer_sum;
        auto mag_x = require_simple_or_po_iv(lb_1.sum.terms[0].variable);

        for (size_t i = 0; i < bit_products.size(); i++) {
            WPBSum bitsum{};
            PolBuilder inner_sum;
            for (size_t j = 0; j < bit_products[i].size(); j++) {
                inner_sum.add(bit_products[i][j].reverse_reif, power2(Integer(j)));
                bitsum += power2(Integer(j)) * bit_products[i][j].flag;
            }
            inner_sum.add(lb_2.line);
            inner_sum.emit(logger, ProofLevel::Temporary);
            auto implied_sum = logger.emit_under_reason(ImpliesProofRule{make_optional<ProofLine>(ProofLineNumber{-1})},
                logger.reify(bitsum + lb_2.rhs * ProofBitVariable{mag_x, Integer(i), false} >= lb_2.rhs, reif), ProofLevel::Temporary, reason);
            outer_sum.add(implied_sum, power2(Integer(i)));
        }

        outer_sum.add(lb_1.line, lb_2.rhs);

        auto bitproducts_bound = outer_sum.emit(logger, ProofLevel::Temporary);

        if (z_ge0_gated) {
            // cake channels the product magnitude to |z| via z_eq rows gated on z's
            // sign atom; z's sign in this branch is sign(x)*sign(y). Pick the row
            // matching that sign (mag_Zge0_ge for z>=0, mag_Zlt0_le for z<0), then
            // discharge the sign atom under the reif (cake's sign clauses entail it):
            // `combined` is a bound on the single variable z, so RUP closes it. A
            // magnitude lower bound is a lower bound on a non-negative z but an upper
            // bound on a negative z, so the coefficient flips.
            if (z_negative && ! z_eq_product_lines_neg)
                throw UnexpectedException{"Signed z channel needs the negative z_eq rows."};
            auto zrow = z_negative ? z_eq_product_lines_neg->second : z_eq_product_lines.first;
            auto combined = add_lines(logger, bitproducts_bound, zrow);
            // z's sign atom holds under the branch reif plus the operand domains
            // (via the reason): cake's sign clauses entail it from sign(x)*sign(y).
            auto zsign = logger.emit_under_reason(
                RUPProofRule{}, logger.reify(WPBSum{} + 1_i * (z_negative ? (z < 0_i) : (z >= 0_i)) >= 1_i, reif), ProofLevel::Temporary, reason);
            auto z_bound_sum = WPBSum{} + (z_negative ? -1_i : 1_i) * z;
            return result_of_deriving(
                logger, RUPProofRule{vector<ProofLine>{combined, zsign}}, z_bound_sum >= lb_1.rhs * lb_2.rhs, reif, ProofLevel::Temporary, reason);
        }

        add_lines(logger, bitproducts_bound, z_eq_product_lines.first);
        return result_of_deriving(logger, ImpliesProofRule{make_optional<ProofLine>(ProofLineNumber{-1})}, mag_z_sum >= lb_1.rhs * lb_2.rhs, reif,
            ProofLevel::Temporary, reason);
    }

    auto prove_positive_product_upper_bound(ProofLogger & logger, DerivedPBConstraint ub_1, DerivedPBConstraint ub_2, const SimpleIntegerVariableID z,
        const map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> & mag_var, const pair<ProofLine, ProofLine> z_eq_product_lines,
        vector<vector<BitProductData>> & bit_products, const ReasonLiterals & reason, bool z_ge0_gated, bool z_negative = false,
        const optional<pair<ProofLine, ProofLine>> & z_eq_product_lines_neg = nullopt) -> DerivedPBConstraint
    {
        auto mag_z_sum = WPBSum{};
        if (mag_var.contains(z))
            mag_z_sum += -1_i * mag_var.at(z);
        else
            mag_z_sum += -1_i * z;

        auto reif = HalfReifyOnConjunctionOf{};
        if (! ub_1.half_reif.empty())
            reif.insert(reif.end(), ub_1.half_reif.begin(), ub_1.half_reif.end());

        if (! ub_2.half_reif.empty())
            reif.insert(reif.end(), ub_2.half_reif.begin(), ub_2.half_reif.end());

        if (ub_1.rhs > 0_i || ub_2.rhs > 0_i)
            return result_of_deriving(logger, ImpliesProofRule{}, mag_z_sum >= 0_i, reif, ProofLevel::Temporary, reason);

        PolBuilder outer_sum;

        auto mag_x = require_simple_or_po_iv(ub_1.sum.terms[0].variable);

        auto mag_y = require_simple_or_po_iv(ub_2.sum.terms[0].variable);

        for (size_t i = 0; i < bit_products.size(); i++) {
            WPBSum bitsum{};
            PolBuilder inner_sum_1;
            PolBuilder inner_sum_2;
            for (size_t j = 0; j < bit_products[i].size(); j++) {
                if (bit_products[i][j].partial_product_1 == nullopt) {
                    bit_products[i][j].partial_product_1 = logger.emit_rup_proof_line(WPBSum{} + 1_i * ! bit_products[i][j].flag +
                                1_i * ProofBitVariable{mag_x, Integer(i), false} + 1_i * ProofBitVariable{mag_y, Integer(j), true} >=
                            1_i,
                        ProofLevel::Top);
                }
                inner_sum_1.add(*bit_products[i][j].partial_product_1, power2(Integer(j)));

                if (bit_products[i][j].partial_product_2 == nullopt) {
                    bit_products[i][j].partial_product_2 = logger.emit_rup_proof_line(
                        WPBSum{} + 1_i * ! bit_products[i][j].flag + 1_i * ProofBitVariable{mag_x, Integer(i), true} >= 1_i, ProofLevel::Top);
                }
                inner_sum_2.add(*bit_products[i][j].partial_product_2, power2(Integer(j)));

                bitsum += power2(Integer(j)) * ! bit_products[i][j].flag;
            }
            inner_sum_1.add(ub_2.line);
            // Actually derive the sums
            auto line1 = inner_sum_1.emit(logger, ProofLevel::Temporary);
            auto line2 = inner_sum_2.emit(logger, ProofLevel::Temporary);

            auto rhs = Integer{(1 << bit_products[i].size()) - 1};
            auto desired_sum = bitsum + -(ub_2.rhs) * ProofBitVariable{mag_x, Integer(i), true};
            auto desired_constraint = logger.reify(logger.reify(desired_sum >= rhs, reif), reason);

            map<ProofGoal, Subproof> subproofs{};
            auto subproof = [&](ProofLogger & logger) {
                add_lines(logger, line1, ProofLineNumber{-2});
                add_lines(logger, line2, ProofLineNumber{-3});
                logger.emit_proof_line("rup >= 1 : -1 -2;", ProofLevel::Temporary);
            };

            subproofs.emplace("#1", subproof);
            auto resolvent_line = logger.emit_red_proof_line(desired_constraint, {}, ProofLevel::Temporary, subproofs);

            outer_sum.add(resolvent_line, power2(Integer(i)));
        }

        outer_sum.add(ub_1.line, -ub_2.rhs);
        auto bitproducts_bound = outer_sum.emit(logger, ProofLevel::Temporary);

        if (z_ge0_gated) {
            // Sign-aware discharge of cake's mag_Z gate (see the lower-bound prover).
            // Pick the row matching z's sign (mag_Zge0_le for z>=0, mag_Zlt0_ge for
            // z<0), discharge the sign atom under the reif, and close the z bound. A
            // magnitude upper bound is an upper bound on a non-negative z but a lower
            // bound on a negative z, so the coefficient flips.
            if (z_negative && ! z_eq_product_lines_neg)
                throw UnexpectedException{"Signed z channel needs the negative z_eq rows."};
            auto zrow = z_negative ? z_eq_product_lines_neg->first : z_eq_product_lines.second;
            auto combined = add_lines(logger, bitproducts_bound, zrow);
            // z's sign atom holds under the branch reif plus the operand domains
            // (via the reason): cake's sign clauses entail it from sign(x)*sign(y).
            auto zsign = logger.emit_under_reason(
                RUPProofRule{}, logger.reify(WPBSum{} + 1_i * (z_negative ? (z < 0_i) : (z >= 0_i)) >= 1_i, reif), ProofLevel::Temporary, reason);
            auto z_bound_sum = WPBSum{} + (z_negative ? 1_i : -1_i) * z;
            return result_of_deriving(
                logger, RUPProofRule{vector<ProofLine>{combined, zsign}}, z_bound_sum >= -ub_1.rhs * ub_2.rhs, reif, ProofLevel::Temporary, reason);
        }

        add_lines(logger, bitproducts_bound, z_eq_product_lines.second);
        return result_of_deriving(logger, ImpliesProofRule{make_optional<ProofLine>(ProofLineNumber{-1})}, mag_z_sum >= -ub_1.rhs * ub_2.rhs, reif,
            ProofLevel::Temporary, reason);
    }

    auto prove_product_bounds(const ReasonLiterals & reason, ProofLogger & logger, vector<vector<BitProductData>> & bit_products,
        const SimpleIntegerVariableID x, const SimpleIntegerVariableID y, const SimpleIntegerVariableID z,
        const map<IntegerVariableID, pair<Integer, Integer>> & var_bounds, const Integer & smallest_product, const Integer & largest_product,
        const map<SimpleIntegerVariableID, ChannellingData> & channelling_constraints,
        const map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> & mag_var, const pair<ProofLine, ProofLine> z_eq_product_lines,
        const vector<ProofLine> & sign_lines, bool z_ge0_gated, const optional<pair<ProofLine, ProofLine>> & z_eq_product_lines_neg) -> void
    {
        // First obtain the current bounds
        // logger.emit_proof_comment("Current Bounds:");
        auto rup_bounds = map<IntegerVariableID, DerivedBounds>{};
        for (const auto & var : {x, y}) {
            auto [lower, upper] = var_bounds.at(var);

            auto var_sum = WPBSum{} + 1_i * var;
            auto neg_var_sum = WPBSum{} + -1_i * var;

            auto lower_def_line = get_def_line_for_lit(logger, var >= lower);
            auto rup_lower = result_of_deriving(logger, ImpliesProofRule{lower_def_line}, var_sum >= lower, {}, ProofLevel::Temporary, reason);

            auto upper_def_line = get_def_line_for_lit(logger, var <= upper);
            auto rup_upper = result_of_deriving(logger, ImpliesProofRule{upper_def_line}, neg_var_sum >= -upper, {}, ProofLevel::Temporary, reason);

            rup_bounds.insert({var, DerivedBounds{rup_lower, rup_upper}});
        }

        // Now channel each to bounds on the magnitude conditioned on the sign bit.
        // Each entry records the branch's sign (true => negative branch) so we can
        // pin z's sign = sign(x)*sign(y) below; the sign atom is kept in the reif
        // only for a zero-spanning operand (spans), so its two branches resolve.
        auto conditional_bounds = map<IntegerVariableID, vector<pair<DerivedPBConstraint, bool>>>{};
        // logger.emit_proof_comment("Channelled Bounds:");
        for (const auto & var : {x, y}) {
            auto [lower, upper] = var_bounds.at(var);
            auto spans = lower < 0_i && upper >= 0_i;
            if (lower < 0_i) {
                conditional_bounds[var].emplace_back(
                    channel_to_sign_bit(logger, true, rup_bounds.at(var).lower, channelling_constraints, mag_var, reason, spans), true);
                conditional_bounds[var].emplace_back(
                    channel_to_sign_bit(logger, true, rup_bounds.at(var).upper, channelling_constraints, mag_var, reason, spans), true);
            }
            if (upper >= 0_i) {
                conditional_bounds[var].emplace_back(
                    channel_to_sign_bit(logger, false, rup_bounds.at(var).lower, channelling_constraints, mag_var, reason, spans), false);
                conditional_bounds[var].emplace_back(
                    channel_to_sign_bit(logger, false, rup_bounds.at(var).upper, channelling_constraints, mag_var, reason, spans), false);
            }
        }

        vector<DerivedPBConstraint> conditional_product_bounds = vector<DerivedPBConstraint>{};
        auto lower_bounds_for_fusion = vector<DerivedPBConstraint>{};
        auto upper_bounds_for_fusion = vector<DerivedPBConstraint>{};

        // Derive upper and lower bounds on z, conditioned on sign bits for x and y
        for (const auto & [x_bound, x_neg] : conditional_bounds.at(x)) {
            for (const auto & [y_bound, y_neg] : conditional_bounds.at(y)) {
                auto z_neg = x_neg != y_neg;
                auto conditional_product_bound = DerivedPBConstraint{};
                if (x_bound.sum.terms[0].coefficient == 1_i && y_bound.sum.terms[0].coefficient == 1_i) {
                    // Both lower bounds
                    auto conditional_product_mag_bound = prove_positive_product_lower_bound(
                        logger, x_bound, y_bound, z, mag_var, z_eq_product_lines, bit_products, reason, z_ge0_gated, z_neg, z_eq_product_lines_neg);
                    conditional_product_bound =
                        channel_z_from_sign_bit(logger, conditional_product_mag_bound, x, y, z, channelling_constraints, reason);
                }
                else if (x_bound.sum.terms[0].coefficient == -1_i && y_bound.sum.terms[0].coefficient == -1_i) {
                    // Both upper bounds
                    auto conditional_product_mag_bound = prove_positive_product_upper_bound(
                        logger, x_bound, y_bound, z, mag_var, z_eq_product_lines, bit_products, reason, z_ge0_gated, z_neg, z_eq_product_lines_neg);
                    conditional_product_bound =
                        channel_z_from_sign_bit(logger, conditional_product_mag_bound, x, y, z, channelling_constraints, reason);
                }
                else
                    continue;

                // Check whether we derived a lower or an upper bound after channelling
                if (conditional_product_bound.sum.terms[0].coefficient == 1_i)
                    lower_bounds_for_fusion.emplace_back(conditional_product_bound);
                else if (conditional_product_bound.sum.terms[0].coefficient == -1_i)
                    upper_bounds_for_fusion.emplace_back(conditional_product_bound);
                else
                    throw UnexpectedException{"Wrong coefficient in derived bounds."};
            }
        }

        auto z_sum = WPBSum{} + 1_i * z;
        auto neg_z_sum = WPBSum{} + -1_i * z;

        auto final_lower_bound = z_sum >= smallest_product;
        auto final_upper_bound = neg_z_sum >= -largest_product;

        for (auto & var : {x, y}) {
            auto reif_eq_0 = HalfReifyOnConjunctionOf{var == 0_i};

            // These are harder to hint as they probably need the full opb definition of multiplication
            lower_bounds_for_fusion.push_back(DerivedPBConstraint{z_sum, smallest_product, reif_eq_0, reason,
                logger.emit_under_reason(RUPProofRule{}, logger.reify(final_lower_bound, reif_eq_0), ProofLevel::Temporary, reason)});

            upper_bounds_for_fusion.push_back(DerivedPBConstraint{neg_z_sum, -largest_product, HalfReifyOnConjunctionOf{var == 0_i}, reason,
                logger.emit_under_reason(RUPProofRule{}, logger.reify(final_upper_bound, reif_eq_0), ProofLevel::Temporary, reason)});
        }

        auto final_lower_constraint = DerivedPBConstraint{z_sum, smallest_product, {}, reason, ProofLineNumber{0}};
        auto final_upper_constraint = DerivedPBConstraint{neg_z_sum, -largest_product, {}, reason, ProofLineNumber{0}};
        auto further_hints =
            vector<ProofLine>{rup_bounds[x].lower.line, rup_bounds[y].lower.line, rup_bounds[x].upper.line, rup_bounds[y].upper.line};
        for (const auto & line : sign_lines) {
            further_hints.emplace_back(line);
        }
        derive_by_fusion_resolution(logger, final_lower_constraint, lower_bounds_for_fusion, further_hints);
        derive_by_fusion_resolution(logger, final_upper_constraint, upper_bounds_for_fusion, further_hints);
    }

    auto prove_quotient_bounds(const ReasonLiterals & reason, ProofLogger & logger, vector<vector<BitProductData>> & bit_products,
        const SimpleIntegerVariableID x, const SimpleIntegerVariableID y, const SimpleIntegerVariableID z,
        const map<IntegerVariableID, pair<Integer, Integer>> & var_bounds, const Integer smallest_quotient, const Integer largest_quotient,
        const map<SimpleIntegerVariableID, ChannellingData> & channelling_constraints,
        const map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> & mag_var, const pair<ProofLine, ProofLine> z_eq_product_lines,
        bool x_is_first, bool assume_upper, bool z_ge0_gated, const optional<pair<ProofLine, ProofLine>> & z_eq_product_lines_neg) -> void
    {
        auto rup_bounds = map<IntegerVariableID, DerivedBounds>{};

        auto x_bits = logger.names_and_ids_tracker().num_bits(x);
        // Whether x's own encoding can be negative (has a sign bit). In the legacy
        // scheme channelling <=> signed; cake channels every operand, so consult the
        // recorded has_negatives instead (a non-negative cake operand has no sign bit).
        auto x_has_neg = channelling_constraints.contains(x) && channelling_constraints.at(x).has_negatives;
        auto min_x = Integer{x_has_neg ? -(power2(x_bits - 1_i)) : 0_i};
        auto max_x = Integer{x_has_neg ? (power2(x_bits - 1_i)) : power2(x_bits)} - 1_i;

        // logger.emit_proof_comment("X bounds for quotient");
        auto upper_x_lit = assume_upper ? x < smallest_quotient : x > largest_quotient;
        auto upper_x_lit_def_line = get_def_line_for_lit(logger, upper_x_lit);
        const auto rup_x_upper = result_of_deriving(logger, ImpliesProofRule{upper_x_lit_def_line},
            WPBSum{} + -1_i * x >= -(! assume_upper ? max_x : smallest_quotient - 1_i), HalfReifyOnConjunctionOf{upper_x_lit}, ProofLevel::Temporary,
            reason);

        auto lower_x_lit = (! assume_upper) ? x > largest_quotient : x < smallest_quotient;
        auto lower_x_lit_def_line = get_def_line_for_lit(logger, lower_x_lit);
        const auto rup_x_lower =
            result_of_deriving(logger, ImpliesProofRule{lower_x_lit_def_line}, WPBSum{} + 1_i * x >= (assume_upper ? min_x : largest_quotient + 1_i),
                HalfReifyOnConjunctionOf{lower_x_lit}, ProofLevel::Temporary, reason);

        rup_bounds.insert({x, DerivedBounds{rup_x_lower, rup_x_upper}});

        auto [y_lower, y_upper] = var_bounds.at(y);

        auto var_sum = WPBSum{} + 1_i * y;
        auto neg_var_sum = WPBSum{} + -1_i * y;

        // logger.emit_proof_comment("Y bounds for quotient");
        auto lower_y_lit_def_line = get_def_line_for_lit(logger, y >= y_lower);
        auto rup_y_lower = result_of_deriving(logger, ImpliesProofRule{lower_y_lit_def_line}, var_sum >= y_lower, {}, ProofLevel::Temporary, reason);

        auto upper_y_lit_def_line = get_def_line_for_lit(logger, y <= y_upper);
        auto rup_y_upper =
            result_of_deriving(logger, ImpliesProofRule{upper_y_lit_def_line}, neg_var_sum >= -y_upper, {}, ProofLevel::Temporary, reason);

        rup_bounds.insert({y, DerivedBounds{rup_y_lower, rup_y_upper}});

        // Now channel each to bounds on the magnitude conditioned on the sign bit;
        // each entry records the branch's sign (true => negative), and the sign atom
        // is kept in the reif only for a zero-spanning operand (see prove_product_bounds).
        auto conditional_bounds = map<IntegerVariableID, vector<pair<DerivedPBConstraint, bool>>>{};

        for (const auto & var : vector{x, y}) {
            auto [lower, upper] = var_bounds.at(var);

            if (var == x) {
                lower = (assume_upper ? min_x : largest_quotient + 1_i);
                upper = (! assume_upper ? max_x : smallest_quotient - 1_i);
            }

            if (lower > upper)
                throw UnexpectedException{format("var == x is {}, lower is {}, upper is {}, assume_upper is {}, min_x is {}, max_x is {}, "
                                                 "largest_quotient is {}, smallest_quotient is {}",
                    var == x, lower, upper, assume_upper, min_x, max_x, largest_quotient, smallest_quotient)};

            auto spans = lower < 0_i && upper >= 0_i;
            if (lower < 0_i) {
                conditional_bounds[var].emplace_back(channel_to_sign_bit(logger, true, rup_bounds.at(var).lower, channelling_constraints, mag_var,
                                                         reason, spans, rup_x_lower.half_reif),
                    true);
                conditional_bounds[var].emplace_back(channel_to_sign_bit(logger, true, rup_bounds.at(var).upper, channelling_constraints, mag_var,
                                                         reason, spans, rup_x_upper.half_reif),
                    true);
            }
            if (upper >= 0_i) {
                conditional_bounds[var].emplace_back(channel_to_sign_bit(logger, false, rup_bounds.at(var).lower, channelling_constraints, mag_var,
                                                         reason, spans, rup_x_lower.half_reif),
                    false);
                conditional_bounds[var].emplace_back(channel_to_sign_bit(logger, false, rup_bounds.at(var).upper, channelling_constraints, mag_var,
                                                         reason, spans, rup_x_upper.half_reif),
                    false);
            }
        }

        vector<DerivedPBConstraint> conditional_product_bounds = vector<DerivedPBConstraint>{};
        auto to_resolve = vector<pair<HalfReifyOnConjunctionOf, ProofLine>>{};

        // logger.emit_proof_comment("RUP actual Z bounds");
        auto [z_lower, z_upper] = var_bounds.at(z);

        auto z_sum = WPBSum{} + 1_i * z;
        auto neg_z_sum = WPBSum{} + -1_i * z;

        auto lower_z_def_line = get_def_line_for_lit(logger, z >= z_lower);
        auto rup_z_lower = result_of_deriving(logger, ImpliesProofRule{lower_z_def_line}, z_sum >= z_lower, {}, ProofLevel::Temporary, reason);
        auto upper_z_def_line = get_def_line_for_lit(logger, z <= z_upper);
        auto rup_z_upper = result_of_deriving(logger, ImpliesProofRule{upper_z_def_line}, neg_z_sum >= -z_upper, {}, ProofLevel::Temporary, reason);

        // Derive upper and lower bounds on z, conditioned on sign bits for x and y
        for (const auto & [x_bound, x_neg] : conditional_bounds.at(x)) {
            for (const auto & [y_bound, y_neg] : conditional_bounds.at(y)) {
                auto z_neg = x_neg != y_neg;
                auto conditional_product_bound = DerivedPBConstraint{};
                if (x_bound.sum.terms[0].coefficient == 1_i && y_bound.sum.terms[0].coefficient == 1_i) {
                    // Both lower bounds
                    DerivedPBConstraint conditional_product_mag_bound{};
                    if (x_is_first)
                        conditional_product_mag_bound = prove_positive_product_lower_bound(logger, x_bound, y_bound, z, mag_var, z_eq_product_lines,
                            bit_products, reason, z_ge0_gated, z_neg, z_eq_product_lines_neg);
                    else
                        conditional_product_mag_bound = prove_positive_product_lower_bound(logger, y_bound, x_bound, z, mag_var, z_eq_product_lines,
                            bit_products, reason, z_ge0_gated, z_neg, z_eq_product_lines_neg);

                    conditional_product_bound =
                        channel_z_from_sign_bit(logger, conditional_product_mag_bound, x, y, z, channelling_constraints, reason);
                }
                else if (x_bound.sum.terms[0].coefficient == -1_i && y_bound.sum.terms[0].coefficient == -1_i) {
                    // Both upper bounds
                    DerivedPBConstraint conditional_product_mag_bound{};
                    if (x_is_first)
                        conditional_product_mag_bound = prove_positive_product_upper_bound(logger, x_bound, y_bound, z, mag_var, z_eq_product_lines,
                            bit_products, reason, z_ge0_gated, z_neg, z_eq_product_lines_neg);
                    else
                        conditional_product_mag_bound = prove_positive_product_upper_bound(logger, y_bound, x_bound, z, mag_var, z_eq_product_lines,
                            bit_products, reason, z_ge0_gated, z_neg, z_eq_product_lines_neg);

                    conditional_product_bound =
                        channel_z_from_sign_bit(logger, conditional_product_mag_bound, x, y, z, channelling_constraints, reason);
                }
                else
                    continue;

                //  Check whether we derived a lower or an upper bound after channelling
                if (conditional_product_bound.sum.terms[0].coefficient == 1_i && conditional_product_bound.rhs > z_upper) {
                    auto res_line = add_lines(logger, conditional_product_bound.line, rup_z_upper.line);
                    auto hints = get_rup_hints_for(logger, conditional_product_bound.half_reif);
                    hints.emplace_back(res_line);
                    auto resolvent = result_of_deriving(
                        logger, RUPProofRule{hints}, WPBSum{} >= 1_i, conditional_product_bound.half_reif, ProofLevel::Temporary, reason);
                    to_resolve.emplace_back(resolvent.half_reif, resolvent.line);
                }

                else if (conditional_product_bound.sum.terms[0].coefficient == -1_i && -conditional_product_bound.rhs < z_lower) {
                    auto res_line = add_lines(logger, conditional_product_bound.line, rup_z_lower.line);
                    auto hints = get_rup_hints_for(logger, conditional_product_bound.half_reif);
                    hints.emplace_back(res_line);
                    auto resolvent = result_of_deriving(
                        logger, RUPProofRule{hints}, WPBSum{} >= 1_i, conditional_product_bound.half_reif, ProofLevel::Temporary, reason);
                    to_resolve.emplace_back(resolvent.half_reif, resolvent.line);
                }
                else if (abs(conditional_product_bound.sum.terms[0].coefficient) != 1_i)
                    throw UnexpectedException{"Wrong coefficient in derived bounds."};
            }
        }

        for (auto & var : {x, y}) {
            auto lower_reif = HalfReifyOnConjunctionOf{var == 0_i, rup_x_lower.half_reif[0]};
            // Again these are harder for hints, unless you want to hint the whole opb definition...
            to_resolve.emplace_back(
                lower_reif, logger.emit_under_reason(RUPProofRule{}, logger.reify(WPBSum{} >= 1_i, lower_reif), ProofLevel::Temporary, reason));
            auto upper_reif = HalfReifyOnConjunctionOf{var == 0_i, rup_x_upper.half_reif[0]};
            to_resolve.emplace_back(
                upper_reif, logger.emit_under_reason(RUPProofRule{}, logger.reify(WPBSum{} >= 1_i, upper_reif), ProofLevel::Temporary, reason));
        }

        run_resolution(logger, to_resolve);
    }

    // Find the bounds for [x_min ... x_max] * [y_min ... y_max]
    // (accounting for the fact x and y can have negative bounds)
    auto get_product_bounds(Integer x_min, Integer x_max, Integer y_min, Integer y_max) -> pair<Integer, Integer>
    {
        auto x1y1 = x_min * y_min;
        auto x2y1 = x_max * y_min;
        auto x1y2 = x_min * y_max;
        auto x2y2 = x_max * y_max;

        auto smallest_possible_product = min({x1y1, x1y2, x2y1, x2y2});
        auto largest_possible_product = max({x1y1, x1y2, x2y1, x2y2});

        return {smallest_possible_product, largest_possible_product};
    }

    // Filter variable x where x * y = z based on bounds of y and z
    auto filter_quotient(SimpleIntegerVariableID x_var, SimpleIntegerVariableID y_var, SimpleIntegerVariableID z_var, Integer z_min, Integer z_max,
        Integer y_min, Integer y_max, const State & state, auto & inference,
        const map<SimpleIntegerVariableID, ChannellingData> & channelling_constraints,
        const map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> & mag_var, const pair<ProofLine, ProofLine> z_eq_product_lines,
        ProofLogger * const logger, vector<vector<BitProductData>> & bit_products, const bool x_is_first, const vector<ProofLine> & sign_lines,
        const ConstraintID & owner, bool z_ge0_gated, const optional<pair<ProofLine, ProofLine>> & z_eq_product_lines_neg) -> void
    {
        // This is based on the case breakdown in JaCoP
        // https://github.com/radsz/jacop/blob/develop/src/main/java/org/jacop/core/IntDomain.java#L1377
        if (z_min <= 0_i && z_max >= 0_i && y_min <= 0_i && y_max >= 0_i) {
            // 0 is in the bounds of both y and z so no filtering possible
            return;
        }
        else if (y_min == 0_i && y_max == 0_i) {
            // y == 0 and 0 not in bounds of z => no possible values for x
            inference.contradiction(logger, JustifyUsingRUP{hints::Multiply{owner}}, ExplicitReason{ReasonLiterals{y_var == 0_i, z_var != 0_i}});
        }
        else if (y_min < 0_i && y_max > 0_i && (z_min > 0_i || z_max < 0_i)) {
            // y contains -1, 0, 1 and z has either all positive or all negative values
            auto largest_possible_quotient = max(abs(z_min), abs(z_max));
            auto smallest_possible_quotient = -largest_possible_quotient;

            auto var_bounds = map<IntegerVariableID, pair<Integer, Integer>>{
                {x_var, state.bounds(x_var)}, {y_var, state.bounds(y_var)}, {z_var, state.bounds(z_var)}};
            auto lower_justf = [&](const ReasonLiterals & reason) {
                prove_quotient_bounds(reason, *logger, bit_products, x_var, y_var, z_var, var_bounds, smallest_possible_quotient,
                    largest_possible_quotient, channelling_constraints, mag_var, z_eq_product_lines, x_is_first, false, z_ge0_gated,
                    z_eq_product_lines_neg);
                logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (x_var <= largest_possible_quotient) >= 1_i, ProofLevel::Current);
            };

            inference.infer(logger, x_var <= largest_possible_quotient, JustifyExplicitly{lower_justf, ThenRUP::No, hints::Multiply{owner}},
                ReasonLiterals{z_var >= var_bounds.at(z_var).first, z_var <= var_bounds.at(z_var).second, y_var >= var_bounds.at(y_var).first,
                    y_var <= var_bounds.at(y_var).second});

            var_bounds.at(x_var).first = min(var_bounds.at(x_var).first, largest_possible_quotient);
            auto upper_justf = [&](const ReasonLiterals & reason) {
                prove_quotient_bounds(reason, *logger, bit_products, x_var, y_var, z_var, var_bounds, smallest_possible_quotient,
                    largest_possible_quotient, channelling_constraints, mag_var, z_eq_product_lines, x_is_first, true, z_ge0_gated,
                    z_eq_product_lines_neg);
                logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (x_var >= smallest_possible_quotient) >= 1_i, ProofLevel::Current);
            };

            inference.infer(logger, x_var >= smallest_possible_quotient, JustifyExplicitly{upper_justf, ThenRUP::No, hints::Multiply{owner}},
                ReasonLiterals{z_var >= var_bounds.at(z_var).first, z_var <= var_bounds.at(z_var).second, y_var >= var_bounds.at(y_var).first,
                    y_var <= var_bounds.at(y_var).second});
        }
        else if (y_min == 0_i && y_max != 0_i && (z_min > 0_i || z_max < 0_i)) {
            // y is either 0 or strictly positive and z has either all positive or all negative values
            filter_quotient(x_var, y_var, z_var, z_min, z_max, 1_i, y_max, state, inference, channelling_constraints, mag_var, z_eq_product_lines,
                logger, bit_products, x_is_first, sign_lines, owner, z_ge0_gated, z_eq_product_lines_neg);
        }
        else if (y_min != 0_i && y_max == 0_i && (z_min > 0_i || z_max < 0_i)) {
            // y is either 0 or strictly negative z has either all positive or all negative values
            filter_quotient(x_var, y_var, z_var, z_min, z_max, y_min, -1_i, state, inference, channelling_constraints, mag_var, z_eq_product_lines,
                logger, bit_products, x_is_first, sign_lines, owner, z_ge0_gated, z_eq_product_lines_neg);
        }
        else if ((y_min > 0_i || y_max < 0_i) && y_min <= y_max) {
            auto smallest_possible_quotient = min({div_ceil(z_min, y_min), div_ceil(z_min, y_max), div_ceil(z_max, y_min), div_ceil(z_max, y_max)});
            auto largest_possible_quotient =
                max({div_floor(z_min, y_min), div_floor(z_min, y_max), div_floor(z_max, y_min), div_floor(z_max, y_max)});

            auto var_bounds = map<IntegerVariableID, pair<Integer, Integer>>{
                {x_var, state.bounds(x_var)}, {y_var, state.bounds(y_var)}, {z_var, state.bounds(z_var)}};
            auto upper_justf = [&](const ReasonLiterals & reason) {
                prove_quotient_bounds(reason, *logger, bit_products, x_var, y_var, z_var, var_bounds, smallest_possible_quotient,
                    largest_possible_quotient, channelling_constraints, mag_var, z_eq_product_lines, x_is_first, false, z_ge0_gated,
                    z_eq_product_lines_neg);
                logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (x_var <= largest_possible_quotient) >= 1_i, ProofLevel::Current);
            };

            auto lower_justf = [&](const ReasonLiterals & reason) {
                prove_quotient_bounds(reason, *logger, bit_products, x_var, y_var, z_var, var_bounds, smallest_possible_quotient,
                    largest_possible_quotient, channelling_constraints, mag_var, z_eq_product_lines, x_is_first, true, z_ge0_gated,
                    z_eq_product_lines_neg);
                logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (x_var >= smallest_possible_quotient) >= 1_i, ProofLevel::Current);
            };

            auto both_justf = [&](const ReasonLiterals & reason) {
                upper_justf(reason);
                lower_justf(reason);
            };

            if (smallest_possible_quotient > largest_possible_quotient) {
                inference.infer(logger, FalseLiteral{}, JustifyExplicitly{both_justf, ThenRUP::No, hints::Multiply{owner}},
                    ReasonLiterals{z_var >= var_bounds.at(z_var).first, z_var <= var_bounds.at(z_var).second, y_var >= var_bounds.at(y_var).first,
                        y_var <= var_bounds.at(y_var).second});
            }
            else {
                inference.infer(logger, x_var <= largest_possible_quotient, JustifyExplicitly{upper_justf, ThenRUP::No, hints::Multiply{owner}},
                    ReasonLiterals{z_var >= var_bounds.at(z_var).first, z_var <= var_bounds.at(z_var).second, y_var >= var_bounds.at(y_var).first,
                        y_var <= var_bounds.at(y_var).second});
                inference.infer(logger, x_var >= smallest_possible_quotient, JustifyExplicitly{lower_justf, ThenRUP::No, hints::Multiply{owner}},
                    ReasonLiterals{z_var >= var_bounds.at(z_var).first, z_var <= var_bounds.at(z_var).second, y_var >= var_bounds.at(y_var).first,
                        y_var <= var_bounds.at(y_var).second});
            }
        }
        else {
            throw UnexpectedException{"Bad interval passed to filter_quotient: z=[" + z_min.to_string() + "," + z_max.to_string() + "] y=[" +
                y_min.to_string() + "," + y_max.to_string() + "] x_is_first=" + std::to_string(x_is_first)};
        }
    }
}

MultiplyBC::MultiplyBC(const SimpleIntegerVariableID v1, const SimpleIntegerVariableID v2, const SimpleIntegerVariableID v3) :
    _v1(v1), _v2(v2), _v3(v3)
{
    // Aliased slots are well-defined semantically (squaring, fixed
    // points) but the bit-product proof encoding doesn't tolerate
    // them: make_magnitude_representation, prove_product_bounds, and
    // the sign_lines accounting all assume distinct underlying
    // variables. See GitHub issue for the deeper fix; until then
    // surface as an InvalidProblemDefinitionException so users get
    // an actionable error instead of a proof-verification failure.
    if (v1 == v2 || v1 == v3 || v2 == v3)
        throw InvalidProblemDefinitionException{"MultiplyBC: operands must be three distinct variable handles"};
}

auto MultiplyBC::clone() const -> unique_ptr<Constraint>
{
    return make_unique<MultiplyBC>(_v1, _v2, _v3);
}

namespace
{
    // cake_pb_cp's multiplication encoding (magnitude bit-products over fresh
    // x[id][axis_i][bin] flags channelled to |X|, reified sign atoms, product
    // channelled to |Z|), for non-negative operands. Populates `result` so the
    // existing bounds propagator's cutting-planes resolve against cake's flags
    // unchanged: the magnitude variables' bits ARE cake's bin flags. See the cake
    // ENCODING_MULTIPLY spec and dev_docs.
    auto define_encoding_cake(ProofModel & model, const State & initial_state, const ConstraintID & constraint_id, const string & label_id,
        SimpleIntegerVariableID v1, SimpleIntegerVariableID v2, SimpleIntegerVariableID v3, mult_bc::EncodingData & result) -> void
    {
        auto & bit_products = result.initial_bit_products;
        auto & channelling_constraints = result.channelling_constraints;
        auto & mag_var = result.mag_var;
        auto & sign_lines = result.sign_lines;
        const auto & mbid = label_id;

        // A magnitude variable per operand: a free bit-sum whose bits are named
        // cake's x[id][axis_i][bin] (use_indices_family), channelled to |v| = v
        // (non-negative) via cake's four sign-gated rows. axis 0 -> "X", 1 -> "Y".
        auto make_mag = [&](SimpleIntegerVariableID v, long long axis, const string & letter) -> ProofOnlySimpleIntegerVariableID {
            // Range [0, max(|lb|, |ub|)] so a signed operand's magnitude has enough
            // bits; for a non-negative operand this is just [0, ub], unchanged.
            auto mag_ub = max(abs(initial_state.lower_bound(v)), abs(initial_state.upper_bound(v)));
            auto mag = model.create_proof_only_integer_variable(0_i, mag_ub, "mult_mag_" + letter, IntegerVariableProofRepresentation::Bits,
                CakeBitNaming{constraint_id, {axis}, "bin", nullopt, false, true});
            auto ge0 = HalfReifyOnConjunctionOf{v >= 0_i};
            auto lt0 = HalfReifyOnConjunctionOf{v < 0_i};
            auto pos_ge = model.add_labelled_constraint(
                mbid, letter + "ge0_ge", "MultiplyBC", "magnitude channel", WPBSum{} + 1_i * v + -1_i * mag >= 0_i, ge0);
            auto pos_le = model.add_labelled_constraint(
                mbid, letter + "ge0_le", "MultiplyBC", "magnitude channel", WPBSum{} + -1_i * v + 1_i * mag >= 0_i, ge0);
            auto neg_ge =
                model.add_labelled_constraint(mbid, letter + "lt0_ge", "MultiplyBC", "magnitude channel", WPBSum{} + 1_i * v + 1_i * mag >= 0_i, lt0);
            auto neg_le = model.add_labelled_constraint(
                mbid, letter + "lt0_le", "MultiplyBC", "magnitude channel", WPBSum{} + -1_i * v + -1_i * mag >= 0_i, lt0);
            channelling_constraints.insert({v, mult_bc::ChannellingData{pos_ge, pos_le, neg_ge, neg_le, true, initial_state.lower_bound(v) < 0_i}});
            mag_var.insert({v, mag});
            return mag;
        };
        auto mag1 = make_mag(v1, 0, "X");
        auto mag2 = make_mag(v2, 1, "Y");

        auto & tracker = model.names_and_ids_tracker();
        auto n1 = tracker.num_bits(mag1);
        auto n2 = tracker.num_bits(mag2);

        // Bit products x[id][i_j][prod] <=> binX_i AND binY_j, summed with 2^(i+j).
        // The two reifying halves carry deterministic labels (create_proof_flag_-
        // fully_reifying): [r] = flag -> ineq ("forwards"), [f] = ~flag -> ~ineq
        // ("reverse"); the propagator references them by those labels.
        auto product_sum = WPBSum{};     // Sum 2^(i+j) prod[i][j]
        auto neg_product_sum = WPBSum{}; // -Sum 2^(i+j) prod[i][j]
        for (Integer i = 0_i; i < n1; ++i) {
            bit_products.emplace_back();
            for (Integer j = 0_i; j < n2; ++j) {
                auto flag = model.create_proof_flag_fully_reifying(constraint_id, {i.raw_value, j.raw_value}, "prod",
                    WPBSum{} + 1_i * ProofBitVariable{mag1, i, true} + 1_i * ProofBitVariable{mag2, j, true} >= 2_i);
                auto base = "x[" + mbid + "][" + std::to_string(i.raw_value) + "_" + std::to_string(j.raw_value) + "][prod]";
                bit_products[i.as_index()].emplace_back(
                    mult_bc::BitProductData{flag, ProofLineLabel{base + "[r]"}, ProofLineLabel{base + "[f]"}, nullopt, nullopt});
                product_sum += power2(i + j) * flag;
                neg_product_sum += -power2(i + j) * flag;
            }
        }

        // Channel the product magnitude to |Z| = Z (non-negative), gated on [Z>=0].
        // The two ge0 halves give Sum(prod) == Z; the propagator uses them as the
        // z_eq_product pair (.first: Z >= product, .second: Z <= product).
        auto zge0 = HalfReifyOnConjunctionOf{v3 >= 0_i};
        auto zlt0 = HalfReifyOnConjunctionOf{v3 < 0_i};
        // Gated on [Z>=0] (byte-matching cake); the product-bound provers discharge
        // the entailed ge0(Z) with the ge0(Z) unit (Z is non-negative here).
        auto mag_z_ge = model.add_labelled_constraint(mbid, "mag_Zge0_ge", "MultiplyBC", "z = product", neg_product_sum + 1_i * v3 >= 0_i, zge0);
        auto mag_z_le = model.add_labelled_constraint(mbid, "mag_Zge0_le", "MultiplyBC", "z = product", product_sum + -1_i * v3 >= 0_i, zge0);
        auto mag_z_neg_ge = model.add_labelled_constraint(mbid, "mag_Zlt0_ge", "MultiplyBC", "z = product", product_sum + 1_i * v3 >= 0_i, zlt0);
        auto mag_z_neg_le = model.add_labelled_constraint(mbid, "mag_Zlt0_le", "MultiplyBC", "z = product", neg_product_sum + -1_i * v3 >= 0_i, zlt0);
        result.v3_eq_product_lines = make_pair(mag_z_ge, mag_z_le);
        result.v3_eq_product_lines_neg = make_pair(mag_z_neg_ge, mag_z_neg_le);
        result.z_product_ge0_gated = true;

        // Sign clauses over reified atoms (all entailed for non-negative operands,
        // but cake always emits them; mirror it so the labels resolve in the chain).
        sign_lines.emplace_back(
            model.add_labelled_constraint(mbid, "sgn_x0", "MultiplyBC", "sign", WPBSum{} + 1_i * (v1 != 0_i) + 1_i * (v3 >= 0_i) >= 1_i));
        sign_lines.emplace_back(
            model.add_labelled_constraint(mbid, "sgn_y0", "MultiplyBC", "sign", WPBSum{} + 1_i * (v2 != 0_i) + 1_i * (v3 >= 0_i) >= 1_i));
        sign_lines.emplace_back(model.add_labelled_constraint(
            mbid, "sgn_pp", "MultiplyBC", "sign", WPBSum{} + 1_i * (v1 < 1_i) + 1_i * (v2 < 1_i) + 1_i * (v3 >= 0_i) >= 1_i));
        sign_lines.emplace_back(model.add_labelled_constraint(
            mbid, "sgn_nn", "MultiplyBC", "sign", WPBSum{} + 1_i * (v1 >= 0_i) + 1_i * (v2 >= 0_i) + 1_i * (v3 >= 0_i) >= 1_i));
        sign_lines.emplace_back(model.add_labelled_constraint(
            mbid, "sgn_np", "MultiplyBC", "sign", WPBSum{} + 1_i * (v1 >= 0_i) + 1_i * (v2 < 1_i) + 1_i * (v3 < 0_i) >= 1_i));
        sign_lines.emplace_back(model.add_labelled_constraint(
            mbid, "sgn_pn", "MultiplyBC", "sign", WPBSum{} + 1_i * (v1 < 1_i) + 1_i * (v2 >= 0_i) + 1_i * (v3 < 0_i) >= 1_i));
    }
}

auto gcs::innards::mult_bc::define_encoding(ProofModel & model, const State & initial_state, const ConstraintID & constraint_id,
    const std::string & label_id, const std::string & role_prefix, SimpleIntegerVariableID v1, SimpleIntegerVariableID v2, SimpleIntegerVariableID v3,
    bool allow_cake_scheme) -> EncodingData
{
    EncodingData result;
    auto & bit_products = result.initial_bit_products;
    auto & channelling_constraints = result.channelling_constraints;
    auto & mag_var = result.mag_var;
    auto & v3_eq_product_lines = result.v3_eq_product_lines;
    auto & sign_lines = result.sign_lines;
    auto * const optional_model = &model;

    // cake_pb_cp's multiplication encoding: fresh magnitude bit-product flags over
    // x[id][axis_i][bin] flags, reified sign atoms, product channelled to |Z|. Cake
    // emits all four sign-gated magnitude rows per operand and the six sign clauses,
    // so this covers signed operands too; the propagator's sign channelling picks
    // the negative rows via cake's [v>=0] atoms. See dev_docs and the cake
    // ENCODING_MULTIPLY spec.
    if (allow_cake_scheme) {
        define_encoding_cake(model, initial_state, constraint_id, label_id, v1, v2, v3, result);
        return result;
    }

    {
        // PB Encoding
        auto make_magnitude_representation = [&](SimpleIntegerVariableID & v,
                                                 const string & name) -> pair<SimpleOrProofOnlyIntegerVariableID, ProofLiteralOrFlag> {
            auto sign_bit = ProofBitVariable{v, 0_i, true};
            if (initial_state.lower_bound(v) < 0_i) {
                auto largest_magnitude = max({abs(initial_state.lower_bound(v)), initial_state.upper_bound(v)});

                auto v_magnitude = optional_model->create_proof_only_integer_variable(
                    0_i, largest_magnitude, name + "_mag", IntegerVariableProofRepresentation::Bits);

                auto bit_sum_without_neg = WPBSum{};
                Integer num_bits = optional_model->names_and_ids_tracker().num_bits(v);

                // Skip the neg bit
                for (Integer pos = 0_i; pos < num_bits - 1_i; pos++)
                    bit_sum_without_neg += power2(pos) * ProofBitVariable{v, pos + 1_i, true};

                // mult_bc does not chain (cake does not encode multiplication), so
                // these bit-decomposition defs take invented @c[id][role] labels.
                const auto & mbid = label_id;
                auto pos_ge = optional_model->add_labelled_constraint(mbid, "posge_" + name, "MultiplyBC", "magnitude channel",
                    bit_sum_without_neg + (-1_i * v_magnitude) >= 0_i, HalfReifyOnConjunctionOf{! sign_bit});
                auto pos_le = optional_model->add_labelled_constraint(mbid, "posle_" + name, "MultiplyBC", "magnitude channel",
                    bit_sum_without_neg + (-1_i * v_magnitude) <= 0_i, HalfReifyOnConjunctionOf{! sign_bit});
                auto neg_ge = optional_model->add_labelled_constraint(mbid, "negge_" + name, "MultiplyBC", "magnitude channel",
                    bit_sum_without_neg + (1_i * v_magnitude) >= power2(num_bits - 1_i), HalfReifyOnConjunctionOf{sign_bit});
                auto neg_le = optional_model->add_labelled_constraint(mbid, "negle_" + name, "MultiplyBC", "magnitude channel",
                    bit_sum_without_neg + (1_i * v_magnitude) <= power2(num_bits - 1_i), HalfReifyOnConjunctionOf{sign_bit});

                channelling_constraints.insert({v, ChannellingData{pos_ge, pos_le, neg_ge, neg_le, false, true}});

                mag_var.insert({v, v_magnitude});

                return make_pair(v_magnitude, sign_bit);
            }
            else {
                return make_pair(v, FalseLiteral{});
            }
        };
        auto [v1_mag, v1_sign] = make_magnitude_representation(v1, role_prefix + "x");
        auto [v2_mag, v2_sign] = make_magnitude_representation(v2, role_prefix + "y");
        auto [v3_mag, v3_sign] = make_magnitude_representation(v3, role_prefix + "z");

        const auto & mbid = label_id;
        auto v1_num_bits = optional_model->names_and_ids_tracker().num_bits(v1_mag);
        auto v2_num_bits = optional_model->names_and_ids_tracker().num_bits(v2_mag);

        auto bit_product_sum = WPBSum{};
        for (Integer i = 0_i; i < v1_num_bits; i++) {
            bit_products.emplace_back();
            for (Integer j = 0_i; j < v2_num_bits; j++) {
                auto flag = optional_model->create_proof_flag(format("xy[{}][{}]", i, j));

                auto ijtag = std::to_string(i.raw_value) + "_" + std::to_string(j.raw_value);
                auto forwards = optional_model->add_labelled_constraint(mbid, role_prefix + "xyfwd_" + ijtag, "MultiplyBC", "bit product",
                    WPBSum{} + 1_i * ProofBitVariable{v1_mag, i, true} + 1_i * ProofBitVariable{v2_mag, j, true} >= 2_i,
                    HalfReifyOnConjunctionOf{flag});

                auto backwards = optional_model->add_labelled_constraint(mbid, role_prefix + "xybwd_" + ijtag, "MultiplyBC", "bit product",
                    WPBSum{} + -1_i * ProofBitVariable{v1_mag, i, true} + -1_i * ProofBitVariable{v2_mag, j, true} >= -1_i,
                    HalfReifyOnConjunctionOf{! flag});

                bit_products[i.as_index()].emplace_back(BitProductData{flag, forwards, backwards, nullopt, nullopt});
                bit_product_sum += power2(i + j) * flag;
            }
        }

        visit(
            [&](auto v3_mag) {
                auto s = optional_model->add_labelled_constraint(mbid, role_prefix + "zprodle", role_prefix + "zprodge", StringLiteral{"MultiplyBC"},
                    StringLiteral{"z = product"}, bit_product_sum + (-1_i * v3_mag) == 0_i);
                v3_eq_product_lines = make_pair(s.first, s.second);
            },
            v3_mag);

        auto xyss = optional_model->create_proof_flag("xy[s][s]");
        sign_lines.emplace_back(optional_model->add_labelled_constraint(
            mbid, role_prefix + "sign_nn", "MultiplyBC", "sign", WPBSum{} + 1_i * ! xyss >= 1_i, HalfReifyOnConjunctionOf{! v1_sign, ! v2_sign}));

        if (mag_var.contains(v1))
            sign_lines.emplace_back(optional_model->add_labelled_constraint(
                mbid, role_prefix + "sign_pn", "MultiplyBC", "sign", WPBSum{} + 1_i * xyss >= 1_i, HalfReifyOnConjunctionOf{v1_sign, ! v2_sign}));
        if (mag_var.contains(v2))
            sign_lines.emplace_back(optional_model->add_labelled_constraint(
                mbid, role_prefix + "sign_np", "MultiplyBC", "sign", WPBSum{} + 1_i * xyss >= 1_i, HalfReifyOnConjunctionOf{! v1_sign, v2_sign}));
        if (mag_var.contains(v1) && mag_var.contains(v2))
            sign_lines.emplace_back(optional_model->add_labelled_constraint(
                mbid, role_prefix + "sign_pp", "MultiplyBC", "sign", WPBSum{} + 1_i * ! xyss >= 1_i, HalfReifyOnConjunctionOf{v1_sign, v2_sign}));

        sign_lines.emplace_back(optional_model->add_labelled_constraint(mbid, role_prefix + "sign_v3pos", "MultiplyBC", "sign",
            WPBSum{} + 1_i * xyss + 1_i * (v1 != 0_i) + 1_i * (v2 != 0_i) >= 3_i, HalfReifyOnConjunctionOf{v3_sign}));

        sign_lines.emplace_back(optional_model->add_labelled_constraint(mbid, role_prefix + "sign_v3neg", "MultiplyBC", "sign",
            WPBSum{} + 1_i * ! xyss + 1_i * (v1 == 0_i) + 1_i * (v2 == 0_i) >= 1_i, HalfReifyOnConjunctionOf{! v3_sign}));
    }

    return result;
}

auto gcs::innards::mult_bc::propagate(SimpleIntegerVariableID v1, SimpleIntegerVariableID v2, SimpleIntegerVariableID v3, const State & state,
    auto & inference, ProofLogger * const logger, const EncodingData & encoding, ConstraintStateHandle bit_products_handle,
    const ConstraintID & owner) -> void
{
    auto var_bounds = map<IntegerVariableID, pair<Integer, Integer>>{{v1, state.bounds(v1)}, {v2, state.bounds(v2)}, {v3, state.bounds(v3)}};
    auto bounds1 = state.bounds(v1), bounds2 = state.bounds(v2);
    auto [smallest_product, largest_product] = get_product_bounds(bounds1.first, bounds1.second, bounds2.first, bounds2.second);
    auto & bit_products = any_cast<vector<vector<BitProductData>> &>(state.get_persistent_constraint_state(bit_products_handle));

    auto justf = [&](const ReasonLiterals & reason) {
        prove_product_bounds(reason, *logger, bit_products, v1, v2, v3, var_bounds, smallest_product, largest_product,
            encoding.channelling_constraints, encoding.mag_var, encoding.v3_eq_product_lines, encoding.sign_lines, encoding.z_product_ge0_gated,
            encoding.v3_eq_product_lines_neg);
        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (v3 <= largest_product) >= 1_i, ProofLevel::Current);
        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (v3 >= smallest_product) >= 1_i, ProofLevel::Current);
    };

    inference.infer_all(logger, {v3 <= largest_product, v3 >= smallest_product}, JustifyExplicitly{justf, ThenRUP::No, hints::Multiply{owner}},
        ReasonLiterals{v1 >= var_bounds.at(v1).first, v1 <= var_bounds.at(v1).second, v2 >= var_bounds.at(v2).first, v2 <= var_bounds.at(v2).second});

    auto bounds3 = state.bounds(v3);
    filter_quotient(v1, v2, v3, bounds3.first, bounds3.second, bounds2.first, bounds2.second, state, inference, encoding.channelling_constraints,
        encoding.mag_var, encoding.v3_eq_product_lines, logger, bit_products, true, encoding.sign_lines, owner, encoding.z_product_ge0_gated,
        encoding.v3_eq_product_lines_neg);

    bounds1 = state.bounds(v1);
    filter_quotient(v2, v1, v3, bounds3.first, bounds3.second, bounds1.first, bounds1.second, state, inference, encoding.channelling_constraints,
        encoding.mag_var, encoding.v3_eq_product_lines, logger, bit_products, false, encoding.sign_lines, owner, encoding.z_product_ge0_gated,
        encoding.v3_eq_product_lines_neg);
}

template auto gcs::innards::mult_bc::propagate(SimpleIntegerVariableID, SimpleIntegerVariableID, SimpleIntegerVariableID, const State &,
    SimpleInferenceTracker &, ProofLogger * const, const EncodingData &, ConstraintStateHandle, const ConstraintID &) -> void;
template auto gcs::innards::mult_bc::propagate(SimpleIntegerVariableID, SimpleIntegerVariableID, SimpleIntegerVariableID, const State &,
    EagerProofLoggingInferenceTracker &, ProofLogger * const, const EncodingData &, ConstraintStateHandle, const ConstraintID &) -> void;

auto MultiplyBC::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    Triggers triggers;
    triggers.on_bounds.emplace_back(_v1);
    triggers.on_bounds.emplace_back(_v2);
    triggers.on_bounds.emplace_back(_v3);

    mult_bc::EncodingData encoding;
    if (optional_model)
        encoding = mult_bc::define_encoding(*optional_model, initial_state, constraint_id(), as_string(constraint_id()), "", _v1, _v2, _v3, true);

    ConstraintStateHandle bit_products_handle = initial_state.add_persistent_constraint_state(encoding.initial_bit_products);

    propagators.install(
        constraint_id(),
        [v1 = _v1, v2 = _v2, v3 = _v3, bit_products_h = bit_products_handle, encoding = encoding, owner = constraint_id()](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            do {
                mult_bc::propagate(v1, v2, v3, state, inference, logger, encoding, bit_products_h, owner);
            } while (inference.did_anything_since_last_call_inside_propagator());

            return PropagatorState::Enable;
        },
        triggers);
}

auto MultiplyBC::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    // Flat primitive shape `(id multiply X Y Z)`, matching cake_pb_cp.
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("multiply"), tracker.s_expr_term_of(_v1), tracker.s_expr_term_of(_v2),
        tracker.s_expr_term_of(_v3)});
}
