
#include <algorithm>
#include <cmath>
#include <gcs/constraints/mult_bc.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/presolvers/auto_table.hh>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::make_pair;
using std::make_unique;
using std::map;
using std::max;
using std::min;
using std::nullopt;
using std::optional;
using std::pair;
using std::set_intersection;
using std::string;
using std::stringstream;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    // Proof Logging for BC Multiplication

    struct BitProductData
    {
        ProofFlag flag;
        ProofLine forwards_reif;
        ProofLine reverse_reif;
        optional<ProofLine> partial_product_1;
        optional<ProofLine> partial_product_2;
    };

    struct ChannellingData
    {
        ProofLine pos_ge;
        ProofLine pos_le;
        ProofLine neg_ge;
        ProofLine neg_le;
    };

    struct DerivedPBConstraint
    {
        WeightedPseudoBooleanSum sum;
        Integer rhs;
        HalfReifyOnConjunctionOf half_reif;
        optional<Reason> reason;
        ProofLine line;

        // Initialise to empty
        explicit DerivedPBConstraint(
            WeightedPseudoBooleanSum sum = WeightedPseudoBooleanSum{},
            const Integer & rhs = 0_i,
            HalfReifyOnConjunctionOf halfReif = HalfReifyOnConjunctionOf{},
            const optional<Reason> & reason = nullopt,
            ProofLine line = 0) :
            sum(std::move(sum)),
            rhs(rhs),
            half_reif(std::move(halfReif)),
            reason(reason),
            line(line)
        {
        }
    };

    struct DerivedBounds
    {
        DerivedPBConstraint lower;
        DerivedPBConstraint upper;
    };

    struct PLine
    {
        // Represents a pol line in the proof that we can add terms to.
        // Maybe this could be generalised (e.g. to other operations) and live in proof.cc?
        stringstream p_line;
        bool first_added;
        int count;

        PLine() :
            first_added(true),
            count(0)
        {
            p_line << "p ";
        }

        auto add(ProofLine line_number, bool and_saturate)
        {
            count++;
            p_line << line_number;
            if (first_added) {
                p_line << " ";
                first_added = false;
            }
            else {
                if (and_saturate)
                    p_line << " + s ";
                else
                    p_line << " + ";
            }
        }

        auto str() const -> string
        {
            return p_line.str();
        }

        auto clear()
        {
            p_line.str("");
            p_line << "p ";
            first_added = true;
            count = 0;
        }

        auto divide_by(long div)
        {
            if (div > 1 && ! first_added)
                p_line << " " << div << " d "
                       << " ";
        }

        auto multiply_by(long mult)
        {
            if (! first_added)
                p_line << " " << mult << " * "
                       << " ";
        }

        auto add_multiplied_by(ProofLine line_number, long mult)
        {
            count++;
            p_line << line_number;
            if (first_added) {
                p_line << " " << mult << " * ";

                first_added = false;
            }
            else {
                p_line << " " << mult << " * + ";
            }
        }
    };

    auto result_of_deriving(ProofLogger & logger, ProofRule rule, const WeightedPseudoBooleanLessEqual & ineq,
        const HalfReifyOnConjunctionOf & reif, const ProofLevel & proof_level, const Reason & reason, const optional<ProofLine> & append_line = nullopt)
    {
        // Have to flip it again to store in the form lhs >= rhs
        WeightedPseudoBooleanSum ge_lhs{};
        for (const auto & t : ineq.lhs.terms) {
            ge_lhs += -t.coefficient * t.variable;
        }
        auto res = DerivedPBConstraint{
            ge_lhs, -ineq.rhs, reif, reason,
            logger.emit_under_reason(rule, logger.reified(ineq, reif), proof_level, reason, append_line)};
        return res;
    }

    auto add_lines(ProofLogger & logger, ProofLine line1, ProofLine line2, bool saturate = true) -> ProofLine
    {
        return logger.emit_proof_line("p " + to_string(line1) + " " + to_string(line2) + " +" + (saturate ? " s " : ""),
            ProofLevel::Temporary);
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

    auto channel_to_sign_bit(
        ProofLogger & logger,
        bool is_negative,
        const DerivedPBConstraint & constr,
        const map<SimpleIntegerVariableID, ChannellingData> & channelling_constraints,
        const map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> & mag_var,
        const Reason & reason,
        const optional<HalfReifyOnConjunctionOf> & assumption = nullopt) -> DerivedPBConstraint
    {
        if (constr.sum.terms.size() != 1 || abs(constr.sum.terms[0].coefficient) != 1_i)
            throw UnexpectedException{"Constraint not in a form that can be channelled."};

        SimpleIntegerVariableID var = require_simple_iv(constr.sum.terms[0].variable);
        auto is_lower_bound = constr.sum.terms[0].coefficient == 1_i;

        ProofLine channel_line;
        WeightedPseudoBooleanSum channel_sum{};
        Integer channel_rhs = constr.rhs;
        auto reif = HalfReifyOnConjunctionOf{};

        if (is_negative && ! channelling_constraints.contains(var)) {
            throw UnexpectedException{"Missing channelling constraints."};
        }
        else if (is_negative) {
            // Negative
            reif = HalfReifyOnConjunctionOf{
                ProofBitVariable{var, 0, true}};
            // channel_rhs = -channel_rhs;
            if (is_lower_bound) {
                channel_line = channelling_constraints.at(var).neg_le;
                channel_sum += -1_i * mag_var.at(var);
            }
            else {
                channel_line = channelling_constraints.at(var).neg_ge;
                channel_sum += 1_i * mag_var.at(var);
            }

            add_lines(logger, channel_line, constr.line, false);
        }
        else if (channelling_constraints.contains(var)) {
            reif = HalfReifyOnConjunctionOf{
                ProofBitVariable{var, 0, false}};

            if (is_lower_bound) {
                channel_line = channelling_constraints.at(var).pos_le;
                channel_sum += 1_i * mag_var.at(var);
            }
            else {
                channel_line = channelling_constraints.at(var).pos_ge;
                channel_sum += -1_i * mag_var.at(var);
            }

            add_lines(logger, channel_line, constr.line, false);
        }
        else {
            channel_sum = constr.sum;
        }

        reif.emplace_back(var != 0_i);

        if (assumption) {
            for (const auto & a : *assumption)
                reif.emplace_back(a);
        }

        if (channel_sum.terms[0].coefficient == -1_i && channel_rhs >= 0_i) {
            channel_rhs = -1_i;
        }
        else if (channel_sum.terms[0].coefficient == 1_i && channel_rhs <= 0_i) {
            channel_rhs = 1_i;
        }

        return result_of_deriving(logger, RUP,
            channel_sum >= channel_rhs,
            reif, ProofLevel::Temporary, reason);
    }

    auto channel_z_from_sign_bit(
        ProofLogger & logger,
        DerivedPBConstraint & constr,
        const SimpleIntegerVariableID & z,
        const map<SimpleIntegerVariableID, ChannellingData> & channelling_constraints,
        const Reason & reason)
        -> DerivedPBConstraint
    {
        // logger.emit_proof_comment("Channel back to z:");

        auto channel_reif = HalfReifyOnConjunctionOf{constr.half_reif};
        //        channel_reif.emplace_back(x != 0_i);
        //        channel_reif.emplace_back(y != 0_i);
        if (! channelling_constraints.contains(z))
            return result_of_deriving(logger, IMPLIES, constr.sum >= constr.rhs, channel_reif, ProofLevel::Temporary, reason);

        auto is_lower_bound = constr.sum.terms[0].coefficient == 1_i;

        auto positive_sign = [&](ProofLiteralOrFlag condition) -> bool {
            return overloaded{
                [&](ProofLiteral & l) {
                    return overloaded{
                        [&](Literal & ll) {
                            return is_literally_true(ll);
                        },
                        [&](ProofVariableCondition &) {
                            throw UnexpectedException{
                                "Sign should be bit, TrueLiteral{} or FalseLiteral{}."};
                            return false;
                        }}
                        .visit(l);
                },
                [&](ProofFlag &) {
                    throw UnexpectedException{
                        "Sign should be bit, TrueLiteral{} or FalseLiteral{}."};
                    return false;
                },
                [&](ProofBitVariable & b) {
                    return ! b.positive;
                }}
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
            throw UnexpectedException{
                "Can't channel back to z."};

        auto z_largest_power = Integer{1 << (logger.variable_constraints_tracker().num_bits(z) - 1)};

        auto rup_sign = logger.emit_rup_proof_line(
            logger.reified(WeightedPseudoBooleanSum{} +
                        1_i * (z_negative ? ProofBitVariable{z, 0, true} : ProofBitVariable{z, 0, false}) >=
                    1_i,
                channel_reif),
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

        add_lines(logger, channel_line, rup_sign);
        auto channel_sum = WeightedPseudoBooleanSum{} + constr.sum.terms[0].coefficient * (z_negative ? -1_i : 1_i) * z;
        return result_of_deriving(logger, RUP, channel_sum >= constr.rhs, channel_reif, ProofLevel::Temporary, reason);
    }

    auto run_resolution(ProofLogger & logger, vector<pair<HalfReifyOnConjunctionOf, ProofLine>> premise_line)
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

        auto resolve = [&](pair<HalfReifyOnConjunctionOf, ProofLine> c1, pair<HalfReifyOnConjunctionOf, ProofLine> c2)
            -> pair<HalfReifyOnConjunctionOf, ProofLine> {
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
                if (found) break;
            }

            set_union(c1.first.begin(), c1.first.end(), c2.first.begin(), c2.first.end(), back_inserter(lits));
            return {lits, line};
        };

        if (premise_line.size() == 2) {
            add_lines(logger, premise_line[0].second, premise_line[1].second);
            return;
        }

        auto derived_empty = false;
        size_t found_c1;
        size_t found_c2;
        while (! derived_empty) {
            auto found = false;

            // Find two clauses that are resolvable
            for (size_t i = 0; i < premise_line.size(); i++) {
                for (size_t j = 0; j < premise_line.size(); j++) {
                    if (i == j) continue;
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
                if (found) break;
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
    }
    auto derive_by_fusion_resolution(ProofLogger & logger, DerivedPBConstraint constr, vector<DerivedPBConstraint> premises)
        -> DerivedPBConstraint
    {
        auto want_to_derive = logger.reified(logger.reified(constr.sum >= constr.rhs, constr.half_reif), *constr.reason);

        if (premises.empty())
            throw UnexpectedException{"Empty premise set for fusion resolution."};

        map<string, JustifyExplicitly> subproof{};
        vector<pair<HalfReifyOnConjunctionOf, ProofLine>> premise_line{};

        auto justf = [&](const Reason & dummy_reason) {
            auto weakened_premises = vector<DerivedPBConstraint>{};
            // First weaken the premises to match our desired constraint
            // logger.emit_proof_comment("Weakened premises");
            auto negation_line = -2;
            for (const auto & p : premises) {
                weakened_premises.emplace_back(result_of_deriving(logger, RUP, // implies?
                    want_to_derive, p.half_reif, ProofLevel::Temporary, dummy_reason));
                negation_line--;
            }

            // logger.emit_proof_comment("Convert to clauses");
            //  Then add the negation of our desired constraint to each of the weakened premises
            //  This should give us a collection of clauses
            for (const auto & p : weakened_premises) {
                premise_line.emplace_back(p.half_reif, add_lines(logger, negation_line, p.line, true));
                negation_line--;
            }

            if (premise_line.size() <= 1) {
                throw UnexpectedException{
                    "Too few premises for fusion resolution."};
            }

            // logger.emit_proof_comment("Resolve:");
            run_resolution(logger, premise_line);
            logger.emit_proof_line("u >= 1 ;", ProofLevel::Temporary);
        };

        subproof.emplace("#1", JustifyExplicitly{justf});

        return DerivedPBConstraint{
            constr.sum,
            constr.rhs,
            constr.half_reif,
            constr.reason,
            logger.emit_red_proof_line(
                want_to_derive,
                {},
                ProofLevel::Temporary,
                subproof)};
    }

    auto prove_positive_product_lower_bound(
        ProofLogger & logger, DerivedPBConstraint lb_1, DerivedPBConstraint lb_2,
        const SimpleIntegerVariableID z,
        const map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> & mag_var,
        const pair<ProofLine, ProofLine> z_eq_product_lines,
        const vector<vector<BitProductData>> & bit_products,
        const Reason & reason)
        -> DerivedPBConstraint
    {
        // logger.emit_proof_comment("Prove Conditional Product Lower Bound:");
        auto mag_z_sum = WeightedPseudoBooleanSum{};
        if (mag_var.contains(z))
            mag_z_sum += 1_i * mag_var.at(z);
        else
            mag_z_sum += 1_i * z;

        auto reif = HalfReifyOnConjunctionOf{};
        if (! lb_1.half_reif.empty())
            reif.insert(reif.end(), lb_1.half_reif.begin(), lb_1.half_reif.end());

        if (! lb_2.half_reif.empty())
            reif.insert(reif.end(), lb_2.half_reif.begin(), lb_2.half_reif.end());

        if (lb_1.rhs <= 0_i || lb_2.rhs <= 0_i) return result_of_deriving(logger, IMPLIES,
            mag_z_sum >= 0_i, reif,
            ProofLevel::Temporary, reason);

        PLine outer_sum{};
        auto mag_x = require_simple_or_po_iv(lb_1.sum.terms[0].variable);

        for (size_t i = 0; i < bit_products.size(); i++) {
            WeightedPseudoBooleanSum bitsum{};
            PLine inner_sum{};
            for (size_t j = 0; j < bit_products[i].size(); j++) {
                inner_sum.add_multiplied_by(bit_products[i][j].reverse_reif, 1 << j);
                bitsum += Integer{1 << (j)} * bit_products[i][j].flag;
            }
            inner_sum.add(lb_2.line, false);
            logger.emit_proof_line(inner_sum.str(), ProofLevel::Temporary);
            auto implied_sum = logger.emit_under_reason(IMPLIES,
                logger.reified(bitsum + lb_2.rhs * ProofBitVariable{mag_x, i, false} >= lb_2.rhs, reif),
                ProofLevel::Temporary, reason, -1);
            outer_sum.add_multiplied_by(implied_sum, 1 << i);
        }

        outer_sum.add_multiplied_by(lb_1.line, lb_2.rhs.raw_value);

        auto bitproducts_bound = logger.emit_proof_line(outer_sum.str(), ProofLevel::Temporary);
        add_lines(logger, bitproducts_bound, z_eq_product_lines.first);

        return result_of_deriving(logger, IMPLIES,
            mag_z_sum >= lb_1.rhs * lb_2.rhs, reif,
            ProofLevel::Temporary, reason, -1);
    }

    auto prove_positive_product_upper_bound(ProofLogger & logger, DerivedPBConstraint ub_1, DerivedPBConstraint ub_2,
        const SimpleIntegerVariableID z,
        const map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> & mag_var,
        const pair<ProofLine, ProofLine> z_eq_product_lines,
        vector<vector<BitProductData>> & bit_products,
        const Reason & reason)
        -> DerivedPBConstraint
    {
        // logger.emit_proof_comment("Prove Conditional Product Upper Bound:");

        auto mag_z_sum = WeightedPseudoBooleanSum{};
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
            return result_of_deriving(logger, IMPLIES,
                mag_z_sum >= 0_i, reif,
                ProofLevel::Temporary, reason);

        PLine outer_sum{};

        auto mag_x = require_simple_or_po_iv(ub_1.sum.terms[0].variable);

        auto mag_y = require_simple_or_po_iv(ub_2.sum.terms[0].variable);

        for (size_t i = 0; i < bit_products.size(); i++) {
            WeightedPseudoBooleanSum bitsum{};
            PLine inner_sum_1{};
            PLine inner_sum_2{};
            for (size_t j = 0; j < bit_products[i].size(); j++) {
                if (bit_products[i][j].partial_product_1 == nullopt) {
                    bit_products[i][j].partial_product_1 = logger.emit_rup_proof_line(
                        WeightedPseudoBooleanSum{} +
                                1_i * ! bit_products[i][j].flag +
                                1_i * ProofBitVariable{mag_x, i, false} +
                                1_i * ProofBitVariable{mag_y, j, true} >=
                            1_i,
                        ProofLevel::Top);
                }
                inner_sum_1.add_multiplied_by(*bit_products[i][j].partial_product_1, 1 << j);

                if (bit_products[i][j].partial_product_2 == nullopt) {
                    bit_products[i][j].partial_product_2 = logger.emit_rup_proof_line(
                        WeightedPseudoBooleanSum{} +
                                1_i * ! bit_products[i][j].flag +
                                1_i * ProofBitVariable{mag_x, i, true} >=
                            1_i,
                        ProofLevel::Top);
                }
                inner_sum_2.add_multiplied_by(*bit_products[i][j].partial_product_2, 1 << j);

                bitsum += Integer{1 << (j)} * ! bit_products[i][j].flag;
            }
            inner_sum_1.add(ub_2.line, false);
            logger.emit_proof_line(inner_sum_1.str(), ProofLevel::Temporary);
            logger.emit_proof_line(inner_sum_2.str(), ProofLevel::Temporary);

            auto rhs = Integer{(1 << bit_products[i].size()) - 1} + ub_2.rhs;

            auto desired_sum = bitsum + -(ub_2.rhs) * ProofBitVariable{mag_x, i, true};
            auto desired_constraint =
                logger.reified(logger.reified(desired_sum >= rhs, reif), reason);

            auto fusion_premise_1 = result_of_deriving(logger, IMPLIES,
                desired_constraint, HalfReifyOnConjunctionOf{ProofBitVariable{mag_x, i, false}},
                ProofLevel::Temporary, reason, -1);

            rhs = Integer{(1 << bit_products[i].size()) - 1};

            auto fusion_premise_2 = result_of_deriving(logger, IMPLIES,
                desired_constraint, HalfReifyOnConjunctionOf{ProofBitVariable{mag_x, i, true}},
                ProofLevel::Temporary, reason, -2);

            // We now know a slightly cleaner way to do this, but this still works fine
            auto fusion_resolvent = derive_by_fusion_resolution(
                logger,
                DerivedPBConstraint{desired_sum, rhs, reif, reason, 0},
                {fusion_premise_1, fusion_premise_2});

            outer_sum.add_multiplied_by(fusion_resolvent.line, 1 << i);
        }

        logger.emit_proof_line(outer_sum.str(), ProofLevel::Temporary);
        outer_sum.add_multiplied_by(ub_1.line, -ub_2.rhs.raw_value);

        auto bitproducts_bound = logger.emit_proof_line(outer_sum.str(), ProofLevel::Temporary);

        add_lines(logger, bitproducts_bound, z_eq_product_lines.second);

        return result_of_deriving(logger, IMPLIES,
            mag_z_sum >= -ub_1.rhs * ub_2.rhs, reif,
            ProofLevel::Temporary, reason, -1);
    }

    auto prove_product_bounds(const Reason & reason, ProofLogger & logger,
        State & state, const SimpleIntegerVariableID x, const SimpleIntegerVariableID y, const SimpleIntegerVariableID z,
        const Integer & smallest_product, const Integer & largest_product,
        const ConstraintStateHandle & bit_products_handle, const map<SimpleIntegerVariableID, ChannellingData> & channelling_constraints,
        const map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> & mag_var,
        const pair<ProofLine, ProofLine> z_eq_product_lines)
    {
        // logger.emit_proof_comment("BEGIN PROVE PRODUCT BOUNDS");
        auto & bit_products = any_cast<vector<vector<BitProductData>> &>(state.get_constraint_state(bit_products_handle));

        // First RUP the current bounds
        // logger.emit_proof_comment("Current Bounds:");
        auto rup_bounds = map<IntegerVariableID, DerivedBounds>{};
        for (const auto & var : {x, y}) {
            Integer lower = 0_i, upper = 0_i;
            auto bounds = state.bounds(var);

            lower = bounds.first;
            upper = bounds.second;

            auto var_sum = WeightedPseudoBooleanSum{} + 1_i * var;
            auto neg_var_sum = WeightedPseudoBooleanSum{} + -1_i * var;

            auto rup_lower = result_of_deriving(logger, RUP, var_sum >= lower, {}, ProofLevel::Temporary, reason);

            auto rup_upper = result_of_deriving(logger, RUP, neg_var_sum >= -upper, {}, ProofLevel::Temporary, reason);

            rup_bounds.insert({var, DerivedBounds{rup_lower, rup_upper}});
        }

        // Now channel each to bounds on the magnitude conditioned on the sign bit
        auto conditional_bounds = map<IntegerVariableID, vector<DerivedPBConstraint>>{};
        // logger.emit_proof_comment("Channelled Bounds:");
        for (const auto & var : {x, y}) {
            auto [lower, upper] = state.bounds(var);
            if (lower < 0_i) {
                conditional_bounds[var].emplace_back(
                    channel_to_sign_bit(logger, true, rup_bounds.at(var).lower, channelling_constraints, mag_var, reason));
                conditional_bounds[var].emplace_back(
                    channel_to_sign_bit(logger, true, rup_bounds.at(var).upper, channelling_constraints, mag_var, reason));
            }
            if (upper >= 0_i) {
                conditional_bounds[var].emplace_back(
                    channel_to_sign_bit(logger, false, rup_bounds.at(var).lower, channelling_constraints, mag_var, reason));
                conditional_bounds[var].emplace_back(
                    channel_to_sign_bit(logger, false, rup_bounds.at(var).upper, channelling_constraints, mag_var, reason));
            }
        }

        vector<DerivedPBConstraint> conditional_product_bounds = vector<DerivedPBConstraint>{};
        auto lower_bounds_for_fusion = vector<DerivedPBConstraint>{};
        auto upper_bounds_for_fusion = vector<DerivedPBConstraint>{};

        // Derive upper and lower bounds on z, conditioned on sign bits for x and y
        for (const auto & x_bound : conditional_bounds.at(x)) {
            for (const auto & y_bound : conditional_bounds.at(y)) {
                auto conditional_product_bound = DerivedPBConstraint{};
                if (x_bound.sum.terms[0].coefficient == 1_i && y_bound.sum.terms[0].coefficient == 1_i) {
                    // Both lower bounds
                    auto conditional_product_mag_bound = prove_positive_product_lower_bound(logger, x_bound, y_bound,
                        z, mag_var, z_eq_product_lines, bit_products, reason);
                    conditional_product_bound = channel_z_from_sign_bit(
                        logger,
                        conditional_product_mag_bound,
                        z,
                        channelling_constraints, reason);
                }
                else if (x_bound.sum.terms[0].coefficient == -1_i && y_bound.sum.terms[0].coefficient == -1_i) {
                    // Both upper bounds
                    auto conditional_product_mag_bound = prove_positive_product_upper_bound(logger, x_bound, y_bound,
                        z, mag_var, z_eq_product_lines, bit_products, reason);
                    conditional_product_bound = channel_z_from_sign_bit(
                        logger,
                        conditional_product_mag_bound,
                        z,
                        channelling_constraints, reason);
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

        auto z_sum = WeightedPseudoBooleanSum{} + 1_i * z;
        auto neg_z_sum = WeightedPseudoBooleanSum{} + -1_i * z;

        auto final_lower_bound = z_sum >= smallest_product;
        auto final_upper_bound = neg_z_sum >= -largest_product;

        for (auto & var : {x, y}) {
            auto reif_eq_0 = HalfReifyOnConjunctionOf{var == 0_i};

            lower_bounds_for_fusion.emplace_back(
                z_sum, smallest_product, reif_eq_0, reason,
                logger.emit_under_reason(RUP,
                    logger.reified(final_lower_bound, reif_eq_0),
                    ProofLevel::Temporary, reason));

            upper_bounds_for_fusion.emplace_back(
                neg_z_sum, -largest_product, HalfReifyOnConjunctionOf{var == 0_i}, reason,
                logger.emit_under_reason(RUP,
                    logger.reified(final_upper_bound, reif_eq_0),
                    ProofLevel::Temporary, reason));
        }

        auto final_lower_constraint = DerivedPBConstraint{z_sum, smallest_product, {}, reason, 0};
        auto final_upper_constraint = DerivedPBConstraint{neg_z_sum, -largest_product, {}, reason, 0};

        // logger.emit_proof_comment("Final fusion lower bounds:");
        derive_by_fusion_resolution(logger, final_lower_constraint, lower_bounds_for_fusion);

        // logger.emit_proof_comment("Final fusion upper bounds:");
        derive_by_fusion_resolution(logger, final_upper_constraint, upper_bounds_for_fusion);
    }

    auto prove_quotient_bounds(
        const Reason & reason,
        ProofLogger & logger,
        State & state, const SimpleIntegerVariableID x, const SimpleIntegerVariableID y, const SimpleIntegerVariableID z,
        const Integer smallest_quotient, const Integer largest_quotient,
        const ConstraintStateHandle & bit_products_handle, const map<SimpleIntegerVariableID, ChannellingData> & channelling_constraints,
        const map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> & mag_var,
        const pair<ProofLine, ProofLine> z_eq_product_lines,
        bool x_is_first,
        bool assume_upper)
    {
        // logger.emit_proof_comment("BEGIN PROVE QUOTIENT BOUNDS");
        auto rup_bounds = map<IntegerVariableID, DerivedBounds>{};
        auto & bit_products = any_cast<vector<vector<BitProductData>> &>(state.get_constraint_state(bit_products_handle));

        auto x_bits = logger.variable_constraints_tracker().num_bits(x);
        auto x_has_neg = channelling_constraints.contains(x);
        auto min_x = Integer{x_has_neg ? -(1 << (x_bits - 1)) : 0};
        auto max_x = Integer{x_has_neg ? (1 << (x_bits - 1)) : 1 << (x_bits)} - 1_i;

        const auto rup_x_upper = result_of_deriving(logger, RUP,
            WeightedPseudoBooleanSum{} + -1_i * x >= -(! assume_upper ? max_x : smallest_quotient - 1_i),
            assume_upper ? HalfReifyOnConjunctionOf{x < smallest_quotient} : HalfReifyOnConjunctionOf{x >= largest_quotient + 1_i}, ProofLevel::Temporary, reason);

        const auto rup_x_lower = result_of_deriving(logger, RUP,
            WeightedPseudoBooleanSum{} + 1_i * x >= (assume_upper ? min_x : largest_quotient + 1_i),
            ! assume_upper ? HalfReifyOnConjunctionOf{x >= largest_quotient + 1_i} : HalfReifyOnConjunctionOf{x < smallest_quotient}, ProofLevel::Temporary, reason);

        rup_bounds.insert({x, DerivedBounds{rup_x_lower, rup_x_upper}});

        auto [y_lower, y_upper] = state.bounds(y);

        auto var_sum = WeightedPseudoBooleanSum{} + 1_i * y;
        auto neg_var_sum = WeightedPseudoBooleanSum{} + -1_i * y;

        auto rup_y_lower = result_of_deriving(logger, RUP, var_sum >= y_lower, {}, ProofLevel::Temporary, reason);

        auto rup_y_upper = result_of_deriving(logger, RUP, neg_var_sum >= -y_upper, {}, ProofLevel::Temporary, reason);

        rup_bounds.insert({y, DerivedBounds{rup_y_lower, rup_y_upper}});

        // Now channel each to bounds on the magnitude conditioned on the sign bit
        auto conditional_bounds = map<IntegerVariableID, vector<DerivedPBConstraint>>{};
        // logger.emit_proof_comment("Channelled Bounds:");

        for (const auto & var : {x, y}) {

            auto bounds = state.bounds(var);
            auto lower = bounds.first;
            auto upper = bounds.second;

            if (var == x) {
                lower = (assume_upper ? min_x : largest_quotient + 1_i);
                upper = (! assume_upper ? max_x : smallest_quotient - 1_i);
            }

            if (lower < 0_i) {
                conditional_bounds[var].emplace_back(
                    channel_to_sign_bit(logger, true, rup_bounds.at(var).lower, channelling_constraints, mag_var, reason, rup_x_lower.half_reif));
                conditional_bounds[var].emplace_back(
                    channel_to_sign_bit(logger, true, rup_bounds.at(var).upper, channelling_constraints, mag_var, reason, rup_x_upper.half_reif));
            }
            if (upper >= 0_i) {
                conditional_bounds[var].emplace_back(
                    channel_to_sign_bit(logger, false, rup_bounds.at(var).lower, channelling_constraints, mag_var, reason, rup_x_lower.half_reif));
                conditional_bounds[var].emplace_back(
                    channel_to_sign_bit(logger, false, rup_bounds.at(var).upper, channelling_constraints, mag_var, reason, rup_x_upper.half_reif));
            }
        }

        vector<DerivedPBConstraint> conditional_product_bounds = vector<DerivedPBConstraint>{};
        auto to_resolve = vector<pair<HalfReifyOnConjunctionOf, ProofLine>>{};

        // logger.emit_proof_comment("RUP actual Z bounds");
        auto [z_lower, z_upper] = state.bounds(z);

        auto z_sum = WeightedPseudoBooleanSum{} + 1_i * z;
        auto neg_z_sum = WeightedPseudoBooleanSum{} + -1_i * z;

        auto rup_z_lower = result_of_deriving(logger, RUP, z_sum >= z_lower, {}, ProofLevel::Temporary, reason);

        auto rup_z_upper = result_of_deriving(logger, RUP, neg_z_sum >= -z_upper, {}, ProofLevel::Temporary, reason);

        // Derive upper and lower bounds on z, conditioned on sign bits for x and y
        for (const auto & x_bound : conditional_bounds.at(x)) {
            for (const auto & y_bound : conditional_bounds.at(y)) {
                auto conditional_product_bound = DerivedPBConstraint{};
                if (x_bound.sum.terms[0].coefficient == 1_i && y_bound.sum.terms[0].coefficient == 1_i) {
                    // Both lower bounds
                    DerivedPBConstraint conditional_product_mag_bound{};
                    if (x_is_first)
                        conditional_product_mag_bound = prove_positive_product_lower_bound(logger, x_bound, y_bound,
                            z, mag_var, z_eq_product_lines, bit_products, reason);
                    else
                        conditional_product_mag_bound = prove_positive_product_lower_bound(logger, y_bound, x_bound,
                            z, mag_var, z_eq_product_lines, bit_products, reason);

                    conditional_product_bound = channel_z_from_sign_bit(
                        logger,
                        conditional_product_mag_bound,
                        z,
                        channelling_constraints, reason);
                }
                else if (x_bound.sum.terms[0].coefficient == -1_i && y_bound.sum.terms[0].coefficient == -1_i) {
                    // Both upper bounds
                    DerivedPBConstraint conditional_product_mag_bound{};
                    if (x_is_first)
                        conditional_product_mag_bound = prove_positive_product_upper_bound(logger, x_bound, y_bound,
                            z, mag_var, z_eq_product_lines, bit_products, reason);
                    else
                        conditional_product_mag_bound = prove_positive_product_upper_bound(logger, y_bound, x_bound,
                            z, mag_var, z_eq_product_lines, bit_products, reason);

                    conditional_product_bound = channel_z_from_sign_bit(
                        logger,
                        conditional_product_mag_bound,
                        z,
                        channelling_constraints, reason);
                }
                else
                    continue;

                // logger.emit_proof_comment("Should we resolve?");
                //  Check whether we derived a lower or an upper bound after channelling
                if (conditional_product_bound.sum.terms[0].coefficient == 1_i && conditional_product_bound.rhs > z_upper) {
                    add_lines(logger, conditional_product_bound.line, rup_z_upper.line);
                    auto resolvent = result_of_deriving(logger, RUP, WeightedPseudoBooleanSum{} >= 1_i, conditional_product_bound.half_reif, ProofLevel::Temporary, reason);
                    to_resolve.emplace_back(resolvent.half_reif, resolvent.line);
                }

                else if (conditional_product_bound.sum.terms[0].coefficient == -1_i && -conditional_product_bound.rhs < z_lower) {
                    add_lines(logger, conditional_product_bound.line, rup_z_lower.line);
                    auto resolvent = result_of_deriving(logger, RUP, WeightedPseudoBooleanSum{} >= 1_i, conditional_product_bound.half_reif, ProofLevel::Temporary, reason);
                    to_resolve.emplace_back(resolvent.half_reif, resolvent.line);
                }
                else if (abs(conditional_product_bound.sum.terms[0].coefficient) != 1_i)
                    throw UnexpectedException{"Wrong coefficient in derived bounds."};
            }
        }

        // logger.emit_proof_comment("Want to resolve " + to_string(to_resolve.size()));
        for (auto & var : {x, y}) {
            auto lower_reif = HalfReifyOnConjunctionOf{var == 0_i, rup_x_lower.half_reif[0]};

            to_resolve.emplace_back(lower_reif, logger.emit_under_reason(RUP, logger.reified(WeightedPseudoBooleanSum{} >= 1_i, lower_reif), ProofLevel::Temporary, reason));
            auto upper_reif = HalfReifyOnConjunctionOf{var == 0_i, rup_x_upper.half_reif[0]};
            to_resolve.emplace_back(upper_reif, logger.emit_under_reason(RUP, logger.reified(WeightedPseudoBooleanSum{} >= 1_i, upper_reif), ProofLevel::Temporary, reason));
        }

        // logger.emit_proof_comment("Resolve for lower");
        // logger.emit_proof_comment("want  to resolve = " + to_string(to_resolve.size()));

        run_resolution(logger, to_resolve);
    }

    auto or_use_rup_if(const Justification & just, bool use_rup) -> Justification
    {
        return use_rup ? Justification{JustifyUsingRUP{}} : just;
    }
}
// End of Proof-Logging related code for BC Multiplication.

// Find the bounds for [x_min ... x_max] * [y_min ... y_max]
// (accounting for the fact x and y can have negative bounds)
auto get_product_bounds(Integer x_min, Integer x_max, Integer y_min, Integer y_max)
    -> pair<Integer, Integer>
{
    auto x1y1 = x_min * y_min;
    auto x2y1 = x_max * y_min;
    auto x1y2 = x_min * y_max;
    auto x2y2 = x_max * y_max;

    auto smallest_possible_product = min(
        min(x1y1, x1y2),
        min(x2y1, x2y2));

    auto largest_possible_product = max(
        max(x1y1, x1y2),
        max(x2y1, x2y2));

    return {smallest_possible_product, largest_possible_product};
}

// Filter variable x where x * y = z based on bounds of y and z
auto filter_quotient(SimpleIntegerVariableID x_var, SimpleIntegerVariableID y_var, SimpleIntegerVariableID z_var,
    Integer z_min, Integer z_max, Integer y_min, Integer y_max,
    const vector<IntegerVariableID> & all_vars, State & state,
    const ConstraintStateHandle & bit_products_handle, const map<SimpleIntegerVariableID, ChannellingData> & channelling_constraints,
    const map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> & mag_var,
    const pair<ProofLine, ProofLine> z_eq_product_lines,
    ProofLogger * const logger,
    const bool x_is_first,
    const bool use_rup)
    -> Inference
{
    // This is based on the case breakdown in JaCoP
    // https://github.com/radsz/jacop/blob/develop/src/main/java/org/jacop/core/IntDomain.java#L1377
    if (z_min <= 0_i && z_max >= 0_i && y_min <= 0_i && y_max >= 0_i) {
        // 0 is in the bounds of both y and z so no filtering possible
        return Inference::NoChange;
    }
    else if (y_min == 0_i && y_max == 0_i) {
        // y == 0 and 0 not in bounds of z => no possible values for x
        // No justification needed?
        return Inference::Contradiction;
    }
    else if (y_min < 0_i && y_max > 0_i && (z_min > 0_i || z_max < 0_i)) {
        // y contains -1, 0, 1 and z has either all positive or all negative values
        auto largest_possible_quotient = max(abs(z_min), abs(z_max));
        auto smallest_possible_quotient = -largest_possible_quotient;
        auto inf = Inference::NoChange;

        auto upper_justf = [&](const Reason & reason) {
            prove_quotient_bounds(reason, *logger, state, x_var, y_var, z_var,
                smallest_possible_quotient, largest_possible_quotient,
                bit_products_handle, channelling_constraints, mag_var, z_eq_product_lines, x_is_first, false);
            logger->emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} + 1_i * (x_var < largest_possible_quotient + 1_i) >= 1_i, ProofLevel::Current);
        };

        inf = state.infer(logger, x_var < largest_possible_quotient + 1_i,
            or_use_rup_if(JustifyExplicitly{upper_justf}, use_rup), generic_reason(state, {y_var, z_var}));

        auto lower_justf = [&](const Reason & reason) {
            prove_quotient_bounds(reason, *logger, state, x_var, y_var, z_var,
                smallest_possible_quotient, largest_possible_quotient,
                bit_products_handle, channelling_constraints, mag_var, z_eq_product_lines, x_is_first, true);
            logger->emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} + 1_i * (x_var >= smallest_possible_quotient) >= 1_i, ProofLevel::Current);
        };

        increase_inference_to(inf,
            state.infer(logger, x_var >= smallest_possible_quotient, or_use_rup_if(JustifyExplicitly{lower_justf}, use_rup), generic_reason(state, {y_var, z_var})));
        return inf;
    }
    else if (y_min == 0_i && y_max != 0_i && (z_min > 0_i || z_max < 0_i)) {
        // y is either 0 or strictly positive and z has either all positive or all negative values
        return filter_quotient(x_var, y_var, z_var, z_min, z_max, 1_i, y_max, all_vars,
            state, bit_products_handle, channelling_constraints, mag_var, z_eq_product_lines, logger, x_is_first, use_rup);
    }
    else if (y_min != 0_i && y_max == 0_i && (z_min > 0_i || z_max < 0_i)) {
        // y is either 0 or strictly negative z has either all positive or all negative values
        return filter_quotient(x_var, y_var, z_var, z_min, z_max, y_min, -1_i, all_vars, state,
            bit_products_handle, channelling_constraints, mag_var, z_eq_product_lines, logger, x_is_first, use_rup);
    }
    else if ((y_min > 0_i || y_max < 0_i) && y_min <= y_max) {
        auto x1y1 = (double)z_min.raw_value / (double)y_min.raw_value;
        auto x1y2 = (double)z_min.raw_value / (double)y_max.raw_value;
        auto x2y1 = (double)z_max.raw_value / (double)y_min.raw_value;
        auto x2y2 = (double)z_max.raw_value / (double)y_max.raw_value;

        double smallest_real_quotient = min(min(x1y1, x1y2), min(x2y1, x2y2));
        double largest_real_quotient = max(max(x1y1, x1y2), max(x2y1, x2y2));
        auto smallest_possible_quotient = Integer{(long long)ceil(smallest_real_quotient)};
        auto largest_possible_quotient = Integer{(long long)floor(largest_real_quotient)};

        auto upper_justf = [&](const Reason & reason) {
            prove_quotient_bounds(reason, *logger, state, x_var, y_var, z_var,
                smallest_possible_quotient, largest_possible_quotient,
                bit_products_handle, channelling_constraints, mag_var, z_eq_product_lines, x_is_first, false);
            logger->emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} + 1_i * (x_var < largest_possible_quotient + 1_i) >= 1_i, ProofLevel::Current);
        };

        auto lower_justf = [&](const Reason & reason) {
            prove_quotient_bounds(reason, *logger, state, x_var, y_var, z_var,
                smallest_possible_quotient, largest_possible_quotient,
                bit_products_handle, channelling_constraints, mag_var, z_eq_product_lines, x_is_first, true);
            logger->emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} + 1_i * (x_var >= smallest_possible_quotient) >= 1_i, ProofLevel::Current);
        };

        auto both_justf = [&](const Reason & reason) {
            upper_justf(reason);
            lower_justf(reason);
        };

        if (smallest_possible_quotient > largest_possible_quotient) {
            return state.infer(logger, FalseLiteral{}, or_use_rup_if(JustifyExplicitly{both_justf}, use_rup), generic_reason(state, {y_var, z_var}));
        }
        auto inf = state.infer(logger, x_var < largest_possible_quotient + 1_i,
            or_use_rup_if(JustifyExplicitly{upper_justf}, use_rup), generic_reason(state, {y_var, z_var}));

        increase_inference_to(inf,
            state.infer(logger, x_var >= smallest_possible_quotient,
                or_use_rup_if(JustifyExplicitly{lower_justf}, use_rup), generic_reason(state, {y_var, z_var})));
        return inf;
    }
    else {
        throw UnexpectedException{
            "Bad interval passed to filter_quotient."};
    }
}

MultBC::MultBC(const SimpleIntegerVariableID v1, const SimpleIntegerVariableID v2, const SimpleIntegerVariableID v3, bool use_gac_justifications) :
    _v1(v1),
    _v2(v2), _v3(v3), _use_gac_justifications(use_gac_justifications)
{
}

auto MultBC::clone() const -> unique_ptr<Constraint>
{
    return make_unique<MultBC>(_v1, _v2, _v3, _use_gac_justifications);
}

auto MultBC::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    Triggers triggers;
    triggers.on_bounds.emplace_back(_v1);
    triggers.on_bounds.emplace_back(_v2);
    triggers.on_bounds.emplace_back(_v3);
    vector<vector<BitProductData>> bit_products{};

    map<SimpleIntegerVariableID, ChannellingData> channelling_constraints{};
    map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> mag_var{};

    pair<ProofLine, ProofLine> v3_eq_product_lines;
    if (optional_model) {
        // PB Encoding
        auto make_magnitude_term = [&](SimpleIntegerVariableID & v, const string & name)
            -> pair<SimpleOrProofOnlyIntegerVariableID, ProofLiteralOrFlag> {
            auto sign_bit = ProofBitVariable{v, 0, true};
            if (initial_state.lower_bound(v) < 0_i) {
                auto largest_magnitude = max({abs(initial_state.lower_bound(v)), initial_state.upper_bound(v)});

                auto v_magnitude = optional_model->create_proof_only_integer_variable(
                    0_i, largest_magnitude, name + "'", IntegerVariableProofRepresentation::Bits);

                auto bit_sum_without_neg = WeightedPseudoBooleanSum{};
                auto num_bits = optional_model->variable_constraints_tracker().num_bits(v);

                // Skip the neg bit
                for (unsigned int pos = 0; pos < num_bits - 1; pos++)
                    bit_sum_without_neg += Integer{1 << pos} * ProofBitVariable{v, pos + 1, true};

                auto pos_ge = optional_model->add_constraint(
                    bit_sum_without_neg + (-1_i * v_magnitude) >= 0_i, HalfReifyOnConjunctionOf{! sign_bit});
                auto pos_le = optional_model->add_constraint(
                    bit_sum_without_neg + (-1_i * v_magnitude) <= 0_i, HalfReifyOnConjunctionOf{! sign_bit});
                auto neg_ge = optional_model->add_constraint(
                    bit_sum_without_neg + (1_i * v_magnitude) >= Integer{1 << (num_bits - 1)}, HalfReifyOnConjunctionOf{sign_bit});
                auto neg_le = optional_model->add_constraint(
                    bit_sum_without_neg + (1_i * v_magnitude) <= Integer{1 << (num_bits - 1)}, HalfReifyOnConjunctionOf{sign_bit});

                channelling_constraints.insert({v, ChannellingData{*pos_ge, *pos_le, *neg_ge, *neg_le}});

                mag_var.insert({v, v_magnitude});

                return make_pair(v_magnitude, sign_bit);
            }
            else {
                return make_pair(v, FalseLiteral{});
            }
        };
        auto [v1_mag, v1_sign] = make_magnitude_term(_v1, "x");
        auto [v2_mag, v2_sign] = make_magnitude_term(_v2, "y");
        auto [v3_mag, v3_sign] = make_magnitude_term(_v3, "z");

        auto v1_num_bits = optional_model->variable_constraints_tracker().num_bits(v1_mag);
        auto v2_num_bits = optional_model->variable_constraints_tracker().num_bits(v2_mag);

        auto bit_product_sum = WeightedPseudoBooleanSum{};
        for (unsigned int i = 0; i < v1_num_bits; i++) {
            bit_products.emplace_back();
            for (unsigned int j = 0; j < v2_num_bits; j++) {
                auto flag = optional_model->create_proof_flag("xy[" + to_string(i) + "," + to_string(j) + "]");

                auto forwards = optional_model->add_constraint(
                    WeightedPseudoBooleanSum{} + 1_i * ProofBitVariable{v1_mag, i, true} + 1_i * ProofBitVariable{v2_mag, j, true} >= 2_i,
                    HalfReifyOnConjunctionOf{flag});

                auto backwards = optional_model->add_constraint(
                    WeightedPseudoBooleanSum{} + -1_i * ProofBitVariable{v1_mag, i, true} + -1_i * ProofBitVariable{v2_mag, j, true} >= -1_i,
                    HalfReifyOnConjunctionOf{! flag});

                bit_products[i].emplace_back(BitProductData{flag, *forwards, *backwards, nullopt, nullopt});
                bit_product_sum += Integer{1 << (i + j)} * flag;
            }
        }

        overloaded{
            [&](SimpleIntegerVariableID v3) {
                auto s = optional_model->add_constraint(bit_product_sum + (-1_i * v3) == 0_i);
                v3_eq_product_lines = make_pair(*s.first, *s.second);
            },
            [&](ProofOnlySimpleIntegerVariableID v3) {
                auto s = optional_model->add_constraint(bit_product_sum + (-1_i * v3) == 0_i);
                v3_eq_product_lines = make_pair(*s.first, *s.second);
            }}
            .visit(v3_mag);
        auto xyss = optional_model->create_proof_flag("xy[s,s]");
        optional_model->add_constraint(
            WeightedPseudoBooleanSum{} + 1_i * ! xyss >= 1_i, HalfReifyOnConjunctionOf{! v1_sign, ! v2_sign});

        // Need to avoid duplicate constraints or else VeriPB segfaults
        if (mag_var.contains(_v1))
            optional_model->add_constraint(
                WeightedPseudoBooleanSum{} + 1_i * xyss >= 1_i, HalfReifyOnConjunctionOf{v1_sign, ! v2_sign});
        if (mag_var.contains(_v2))
            optional_model->add_constraint(
                WeightedPseudoBooleanSum{} + 1_i * xyss >= 1_i, HalfReifyOnConjunctionOf{! v1_sign, v2_sign});
        if (mag_var.contains(_v1) && mag_var.contains(_v2))
            optional_model->add_constraint(
                WeightedPseudoBooleanSum{} + 1_i * ! xyss >= 1_i, HalfReifyOnConjunctionOf{v1_sign, v2_sign});

        optional_model->add_constraint(
            WeightedPseudoBooleanSum{} + 1_i * xyss + 1_i * (_v1 != 0_i) + 1_i * (_v2 != 0_i) >= 3_i,
            HalfReifyOnConjunctionOf{v3_sign});

        optional_model->add_constraint(
            WeightedPseudoBooleanSum{} + 1_i * ! xyss + 1_i * (_v1 == 0_i) + 1_i * (_v2 == 0_i) >= 1_i,
            HalfReifyOnConjunctionOf{! v3_sign});
    }

    ConstraintStateHandle bit_products_handle = initial_state.add_constraint_state(bit_products);

    propagators.install([v1 = _v1, v2 = _v2, v3 = _v3, bit_products_h = bit_products_handle,
                            channelling_constraints = channelling_constraints,
                            mag_var = mag_var, v3_eq_product_lines = v3_eq_product_lines,
                            use_rup = _use_gac_justifications](State & state,
                            ProofLogger * const logger) -> pair<Inference, PropagatorState> {
        vector<IntegerVariableID> all_vars = {v1, v2, v3};

        auto overall_result = Inference::NoChange;
        auto inf = Inference::NoChange;
        do {
            inf = Inference::NoChange;
            auto bounds1 = state.bounds(v1), bounds2 = state.bounds(v2);
            auto [smallest_product, largest_product] = get_product_bounds(bounds1.first, bounds1.second, bounds2.first, bounds2.second);

            auto upper_justf = [&](const Reason & reason) {
                prove_product_bounds(reason, *logger, state, v1, v2, v3,
                    smallest_product, largest_product, bit_products_h, channelling_constraints, mag_var, v3_eq_product_lines);
                logger->emit_rup_proof_line_under_reason(state, reason,
                    WeightedPseudoBooleanSum{} + 1_i * (v3 < largest_product + 1_i) >= 1_i, ProofLevel::Current);
                logger->emit_rup_proof_line_under_reason(state, reason,
                    WeightedPseudoBooleanSum{} + 1_i * (v3 >= smallest_product) >= 1_i, ProofLevel::Current);
            };

            increase_inference_to(inf,
                state.infer(logger, v3 < largest_product + 1_i, or_use_rup_if(JustifyExplicitly{upper_justf}, use_rup), generic_reason(state, {v1, v2})));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            auto lower_justf = JustifyExplicitly{[&](const Reason & reason) {
                if (inf == Inference::NoChange) {
                    prove_product_bounds(reason, *logger, state, v1, v2, v3,
                        smallest_product, largest_product, bit_products_h, channelling_constraints, mag_var, v3_eq_product_lines);
                    logger->emit_rup_proof_line_under_reason(state, reason,
                        WeightedPseudoBooleanSum{} + 1_i * (v3 >= smallest_product) >= 1_i, ProofLevel::Current);
                }
            }};

            increase_inference_to(inf,
                state.infer(logger, v3 >= smallest_product, or_use_rup_if(JustifyExplicitly{lower_justf}, use_rup), generic_reason(state, {v1, v2})));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            auto bounds3 = state.bounds(v3);
            increase_inference_to(inf,
                filter_quotient(v1, v2, v3, bounds3.first, bounds3.second, bounds2.first, bounds2.second, all_vars, state,
                    bit_products_h, channelling_constraints, mag_var, v3_eq_product_lines, logger, true, use_rup));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            bounds1 = state.bounds(v1);
            increase_inference_to(inf,
                filter_quotient(v2, v1, v3, bounds3.first, bounds3.second, bounds1.first, bounds1.second, all_vars, state,
                    bit_products_h, channelling_constraints, mag_var, v3_eq_product_lines, logger, false, use_rup));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            increase_inference_to(overall_result, inf);
        } while (inf != Inference::NoChange);

        return {overall_result, PropagatorState::Enable};
    },
        triggers, "mult");
}

auto MultBC::describe_for_proof() -> string
{
    return "mult";
}
