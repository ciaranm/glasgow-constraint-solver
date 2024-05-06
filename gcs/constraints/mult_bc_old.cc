
#include <algorithm>
#include <cmath>
#include <gcs/constraints/mult_bc.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/propagators.hh>

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
using std::string;
using std::stringstream;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
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

    auto prove_product_bounds(const Reason & reason, ProofLogger & logger, State & state, const SimpleIntegerVariableID x, const SimpleIntegerVariableID y, const SimpleIntegerVariableID z,
        const ConstraintStateHandle & bit_products_handle, const map<SimpleIntegerVariableID, ChannellingData> & channelling_constraints, const map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> & mag_var,
        const pair<ProofLine, ProofLine> z_eq_product_lines)
    {
        auto & bit_products = any_cast<vector<vector<BitProductData>> &>(state.get_constraint_state(bit_products_handle));

        auto bounds1 = state.bounds(x), bounds2 = state.bounds(y);
        auto bounds3 = state.bounds(z);

        auto final_bounds = get_product_bounds(bounds1.first, bounds1.second, bounds2.first, bounds2.second);

        auto wts_lower = final_bounds.first;
        auto wts_upper = final_bounds.second;

        logger.emit_proof_comment("Bounds on product FROM " + to_string(bounds1.first.raw_value) + " " + to_string(bounds1.second.raw_value) + " " + to_string(bounds2.first.raw_value) + " " + to_string(bounds2.second.raw_value) + " ----------");

        auto x_lower_bound = logger.emit_under_reason(RUP, WeightedPseudoBooleanSum{} + 1_i * x >= bounds1.first, ProofLevel::Temporary, reason);
        auto x_upper_bound = logger.emit_under_reason(RUP, WeightedPseudoBooleanSum{} + -1_i * x >= -bounds1.second, ProofLevel::Temporary, reason);
        auto y_lower_bound = logger.emit_under_reason(RUP, WeightedPseudoBooleanSum{} + 1_i * y >= bounds2.first, ProofLevel::Temporary, reason);
        auto y_upper_bound = logger.emit_under_reason(RUP, WeightedPseudoBooleanSum{} + -1_i * y >= -bounds2.second, ProofLevel::Temporary, reason);

        struct ConditionalBoundData
        {
            ProofLine line;
            Integer bound;
            ProofLiteralOrFlag condition;
        };

        vector<ConditionalBoundData> x_cond_lower{};
        vector<ConditionalBoundData> x_cond_upper{};
        vector<ConditionalBoundData> y_cond_lower{};
        vector<ConditionalBoundData> y_cond_upper{};

        WeightedPseudoBooleanSum neg_reason{};
        for (const auto & r : logger.reason_to_lits(reason)) {
            overloaded{
                [&](const ProofLiteral & l) {
                    neg_reason += 1_i * ! l;
                },
                [&](const ProofFlag & f) {
                    neg_reason += 1_i * ! f;
                },
                [&](const ProofBitVariable & b) {
                    neg_reason += 1_i * ! b;
                }}
                .visit(r);
        }

        auto push_bounds_constraints = [&](const SimpleIntegerVariableID & var, const pair<Integer, Integer> & bounds, ProofLine lower, ProofLine upper,
                                           vector<ConditionalBoundData> & cond_lower, vector<ConditionalBoundData> & cond_upper, const SimpleIntegerVariableID & other_var) {
            auto [var_lower_bound, var_upper_bound] = state.bounds(var);
            if (bounds.first < 0_i) {
                //                if (channelling_constraints.contains(z)) {
                //                    logger.emit(RUP, WeightedPseudoBooleanSum{} + 1_i * ProofBitVariable{z, 0, true} + 1_i * ! (other_var >= 1_i) + 1_i * ProofBitVariable{var, 0, false} >= 1_i, ProofLevel::Temporary);
                //                }
                //                else {
                //                    logger.emit(RUP, WeightedPseudoBooleanSum{} + 1_i * ! (other_var >= 1_i) + 1_i * ProofBitVariable{var, 0, false} >= 1_i, ProofLevel::Temporary);
                //                }

                if (bounds.second < 0_i) {
                    // var is negative -> flip upper and lower after channelling
                    if (channelling_constraints.contains(var)) {
                        logger.emit_proof_line("p " + to_string(lower) + " " + to_string(channelling_constraints.at(var).neg_le) + " + ", ProofLevel::Temporary);
                        lower = logger.emit_under_reason(IMPLIES,
                            logger.reified(WeightedPseudoBooleanSum{} + (-1_i * mag_var.at(var)) >= min(var_lower_bound, 0_i), HalfReifyOnConjunctionOf{ProofBitVariable{var, 0, true}}),
                            ProofLevel::Temporary, reason);
                        logger.emit_proof_line("p " + to_string(upper) + " " + to_string(channelling_constraints.at(var).neg_ge) + " + ", ProofLevel::Temporary);
                        upper = logger.emit_under_reason(IMPLIES,
                            logger.reified(WeightedPseudoBooleanSum{} + (1_i * mag_var.at(var)) >= max(-var_upper_bound, 0_i), HalfReifyOnConjunctionOf{ProofBitVariable{var, 0, true}}),
                            ProofLevel::Temporary, reason);
                    }
                    cond_lower.emplace_back(ConditionalBoundData{ConditionalBoundData{upper, max(-var_upper_bound, 0_i), ProofBitVariable{var, 0, true}}});
                    cond_upper.emplace_back(ConditionalBoundData{lower, max(-var_lower_bound, 0_i), ProofBitVariable{var, 0, true}});
                }
                else {
                    // var either non-negative or negative -> flip for negative, same for positive
                    if (channelling_constraints.contains(var)) {
                        logger.emit_proof_comment("Channelled bounds:");

                        logger.emit_proof_line("p " + to_string(lower) + " " + to_string(channelling_constraints.at(var).neg_le) + " + ", ProofLevel::Temporary);
                        auto upper_if_neg = logger.emit_under_reason(IMPLIES,
                            logger.reified(WeightedPseudoBooleanSum{} + (-1_i * mag_var.at(var)) >= min(var_lower_bound, 0_i), HalfReifyOnConjunctionOf{ProofBitVariable{var, 0, true}}),
                            ProofLevel::Temporary, reason);
                        cond_upper.emplace_back(ConditionalBoundData{upper_if_neg, max(-var_lower_bound, 0_i), ProofBitVariable{var, 0, true}});

                        logger.emit_proof_line("p " + to_string(upper) + " " + to_string(channelling_constraints.at(var).neg_ge) + " + ", ProofLevel::Temporary);
                        auto lower_if_neg = logger.emit_under_reason(IMPLIES,
                            logger.reified(WeightedPseudoBooleanSum{} + (1_i * mag_var.at(var)) >= max(-var_upper_bound, 0_i), HalfReifyOnConjunctionOf{ProofBitVariable{var, 0, true}}),
                            ProofLevel::Temporary, reason);
                        cond_lower.emplace_back(ConditionalBoundData{lower_if_neg, max(-var_upper_bound, 0_i), ProofBitVariable{var, 0, true}});

                        logger.emit_proof_line("p " + to_string(lower) + " " + to_string(channelling_constraints.at(var).pos_le) + " + ", ProofLevel::Temporary);
                        auto lower_if_pos = logger.emit_under_reason(IMPLIES,
                            logger.reified(WeightedPseudoBooleanSum{} + (1_i * mag_var.at(var)) >= max(var_lower_bound, 0_i), HalfReifyOnConjunctionOf{ProofBitVariable{var, 0, false}}),
                            ProofLevel::Temporary, reason);
                        cond_lower.emplace_back(ConditionalBoundData{lower_if_pos, max(var_lower_bound, 0_i), ProofBitVariable{var, 0, false}});

                        logger.emit_proof_line("p " + to_string(upper) + " " + to_string(channelling_constraints.at(var).pos_ge) + " + ", ProofLevel::Temporary);
                        auto upper_if_pos = logger.emit_under_reason(IMPLIES,
                            logger.reified(WeightedPseudoBooleanSum{} + (-1_i * mag_var.at(var)) >= min(-var_upper_bound, 0_i), HalfReifyOnConjunctionOf{ProofBitVariable{var, 0, false}}),
                            ProofLevel::Temporary, reason);
                        cond_upper.emplace_back(ConditionalBoundData{upper_if_pos, max(var_upper_bound, 0_i), ProofBitVariable{var, 0, false}});
                    }
                    else {
                        throw UnexpectedException{
                            "Missing channelling constraints."};
                    }
                }
            }
            else {
                // var is non-negative
                if (channelling_constraints.contains(var)) {
                    logger.emit_proof_line("p " + to_string(lower) + " " + to_string(channelling_constraints.at(var).pos_le) + " + s", ProofLevel::Temporary);
                    lower = logger.emit_under_reason(IMPLIES,
                        logger.reified(WeightedPseudoBooleanSum{} + (1_i * mag_var.at(var)) >= max(var_lower_bound, 0_i), HalfReifyOnConjunctionOf{ProofBitVariable{var, 0, false}}),
                        ProofLevel::Temporary, reason);
                    logger.emit_proof_line("p " + to_string(upper) + " " + to_string(channelling_constraints.at(var).pos_ge) + " + s", ProofLevel::Temporary);
                    upper = logger.emit_under_reason(IMPLIES,
                        logger.reified(WeightedPseudoBooleanSum{} + (-1_i * mag_var.at(var)) >= min(-var_upper_bound, 0_i), HalfReifyOnConjunctionOf{ProofBitVariable{var, 0, false}}),
                        ProofLevel::Temporary, reason);
                    cond_lower.emplace_back(ConditionalBoundData{lower, var_lower_bound, ProofBitVariable{var, 0, false}});
                    cond_upper.emplace_back(ConditionalBoundData{upper, var_upper_bound, ProofBitVariable{var, 0, false}});
                }
                else {
                    cond_lower.emplace_back(ConditionalBoundData{lower, var_lower_bound, TrueLiteral{}});
                    cond_upper.emplace_back(ConditionalBoundData{upper, var_upper_bound, TrueLiteral{}});
                }
            }
        };

        push_bounds_constraints(x, bounds1, x_lower_bound, x_upper_bound, x_cond_lower, x_cond_upper, y);
        push_bounds_constraints(y, bounds2, y_lower_bound, y_upper_bound, y_cond_lower, y_cond_upper, x);

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
                [&](ProofFlag & f) {
                    throw UnexpectedException{
                        "Sign should be bit, TrueLiteral{} or FalseLiteral{}."};
                    return false;
                },
                [&](ProofBitVariable & b) {
                    return ! b.positive;
                }}
                .visit(condition);
        };

        auto prove_positive_product_lower_bounds = [&](ConditionalBoundData lb_1, ConditionalBoundData lb_2) -> ProofLine {
            logger.emit_proof_comment("Conditional Product Lower Bounds: " + to_string(lb_1.bound.raw_value) + " " + to_string(lb_2.bound.raw_value));
            PLine outer_sum{};
            SimpleOrProofOnlyIntegerVariableID mag_x = x;
            if (mag_var.contains(x))
                mag_x = mag_var.at(x);

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
                    logger.reified(bitsum + lb_2.bound * ProofBitVariable{mag_x, i, false} >= lb_2.bound, HalfReifyOnConjunctionOf{lb_1.condition, lb_2.condition}),
                    ProofLevel::Temporary, reason);
                outer_sum.add_multiplied_by(implied_sum, 1 << i);
            }

            outer_sum.add_multiplied_by(lb_1.line, lb_2.bound.raw_value);

            auto bitproducts_bound = logger.emit_proof_line(outer_sum.str(), ProofLevel::Temporary);
            logger.emit_proof_comment("Obtained bound:");
            auto mag_bound = logger.emit_proof_line("p " + to_string(bitproducts_bound) + " " + to_string(z_eq_product_lines.first) + " + ", ProofLevel::Temporary);
            if (channelling_constraints.contains(z)) {
                logger.emit_proof_comment("Channelled bound:");
                if (! (positive_sign(lb_1.condition) ^ positive_sign(lb_2.condition))) {
                    auto rup_sign = logger.emit_rup_proof_line(
                        logger.reified(WeightedPseudoBooleanSum{} + -Integer{1 << (logger.variable_constraints_tracker().num_bits(z) - 1)} * ProofBitVariable{z, 0, true} >= 0_i,
                            HalfReifyOnConjunctionOf{lb_1.condition, lb_2.condition, x != 0_i, y != 0_i}),
                        ProofLevel::Temporary);

                    logger.emit_proof_line("p " + to_string(mag_bound) + " " + to_string(channelling_constraints.at(z).pos_ge) + " + ", ProofLevel::Temporary);
                    logger.weaken_lits(-1, {ProofBitVariable{z, 0, true}}, ProofLevel::Temporary);
                    logger.emit_proof_line("p -1 " + to_string(rup_sign) + " + ", ProofLevel::Temporary);

                    return logger.emit_under_reason(IMPLIES,
                        logger.reified(WeightedPseudoBooleanSum{} + 1_i * z >= wts_lower, HalfReifyOnConjunctionOf{lb_1.condition, lb_2.condition, x != 0_i, y != 0_i}),
                        ProofLevel::Temporary, reason);
                }
                else {
                    auto rup_sign = logger.emit_rup_proof_line(
                        logger.reified(WeightedPseudoBooleanSum{} + Integer{1 << (logger.variable_constraints_tracker().num_bits(z) - 1)} * ProofBitVariable{z, 0, true} >= Integer{1 << (logger.variable_constraints_tracker().num_bits(z) - 1)},
                            HalfReifyOnConjunctionOf{lb_1.condition, lb_2.condition, x != 0_i, y != 0_i}),
                        ProofLevel::Temporary);

                    logger.emit_proof_line("p " + to_string(mag_bound) + " " + to_string(channelling_constraints.at(z).neg_le) + " + ",
                        ProofLevel::Temporary);
                    logger.weaken_lits(-1, {ProofBitVariable{z, 0, true}}, ProofLevel::Temporary);
                    logger.emit_proof_line("p -1 " + to_string(rup_sign) + " + ", ProofLevel::Temporary);
                    return logger.emit_under_reason(IMPLIES,
                        logger.reified(WeightedPseudoBooleanSum{} + -1_i * z >= -wts_upper, HalfReifyOnConjunctionOf{lb_1.condition, lb_2.condition, x != 0_i, y != 0_i}),
                        ProofLevel::Temporary, reason);
                }
            }
            else {
                if (! (positive_sign(lb_1.condition) ^ positive_sign(lb_2.condition))) {
                    return logger.emit_under_reason(IMPLIES,
                        logger.reified(WeightedPseudoBooleanSum{} + 1_i * z >= wts_lower, HalfReifyOnConjunctionOf{lb_1.condition, lb_2.condition, x != 0_i, y != 0_i}),
                        ProofLevel::Temporary, reason);
                }
                else {
                    return logger.emit_under_reason(RUP,
                        logger.reified(WeightedPseudoBooleanSum{} + -1_i * z >= -wts_upper, HalfReifyOnConjunctionOf{lb_1.condition, lb_2.condition, x != 0_i, y != 0_i}),
                        ProofLevel::Temporary, reason);
                }
            }
        };

        auto prove_positive_product_upper_bounds = [&](ConditionalBoundData ub_1, ConditionalBoundData ub_2) -> ProofLine {
            logger.emit_proof_comment("Conditional Product Upper Bounds: " + to_string(ub_1.bound.raw_value) + " " + to_string(ub_2.bound.raw_value));
            PLine outer_sum{};
            SimpleOrProofOnlyIntegerVariableID mag_x = x;
            if (mag_var.contains(x))
                mag_x = mag_var.at(x);

            SimpleOrProofOnlyIntegerVariableID mag_y = y;
            if (mag_var.contains(y))
                mag_y = mag_var.at(y);

            for (size_t i = 0; i < bit_products.size(); i++) {
                WeightedPseudoBooleanSum bitsum{};
                PLine inner_sum_1{};
                PLine inner_sum_2{};
                for (size_t j = 0; j < bit_products[i].size(); j++) {
                    if (bit_products[i][j].partial_product_1 == nullopt) {
                        bit_products[i][j].partial_product_1 = logger.emit_rup_proof_line(
                            WeightedPseudoBooleanSum{} + 1_i * ! bit_products[i][j].flag + 1_i * ProofBitVariable{mag_x, i, false} + 1_i * ProofBitVariable{mag_y, j, true} >= 1_i, ProofLevel::Top);
                    }
                    inner_sum_1.add_multiplied_by(*bit_products[i][j].partial_product_1, 1 << j);

                    if (bit_products[i][j].partial_product_2 == nullopt) {
                        bit_products[i][j].partial_product_2 = logger.emit_rup_proof_line(
                            WeightedPseudoBooleanSum{} + 1_i * ! bit_products[i][j].flag + 1_i * ProofBitVariable{mag_x, i, true} >= 1_i, ProofLevel::Top);
                    }
                    inner_sum_2.add_multiplied_by(*bit_products[i][j].partial_product_2, 1 << j);

                    bitsum += Integer{1 << (j)} * ! bit_products[i][j].flag;
                }
                inner_sum_1.add(ub_2.line, false);
                logger.emit_proof_line(inner_sum_1.str(), ProofLevel::Temporary);
                logger.emit_proof_line(inner_sum_2.str(), ProofLevel::Temporary);
                auto rhs = Integer{(1 << bit_products[i].size()) - 1} - ub_2.bound;
                logger.emit_proof_comment("Fusion resolution constraints: ");
                logger.emit_under_reason(IMPLIES,
                    logger.reified(bitsum + (rhs)*ProofBitVariable{mag_x, i, false} >= rhs, HalfReifyOnConjunctionOf{ub_1.condition, ub_2.condition}),
                    ProofLevel::Temporary, reason);
                rhs = Integer{(1 << bit_products[i].size()) - 1};
                logger.emit_under_reason(IMPLIES,
                    logger.reified(bitsum + (rhs + ub_2.bound) * ProofBitVariable{mag_x, i, true} >= rhs, HalfReifyOnConjunctionOf{ub_1.condition, ub_2.condition}),
                    ProofLevel::Temporary, reason);

                map<string, JustifyExplicitly> subproof{};

                auto justf = [&](const Reason & reason) {
                    logger.emit_proof_line("p -2 -4 + s", ProofLevel::Temporary);
                    logger.emit_proof_line("p -3 -4 + s", ProofLevel::Temporary);
                    logger.emit_proof_line("u >= 1 ;", ProofLevel::Temporary);
                };

                subproof.emplace("#1", JustifyExplicitly{justf});

                auto fusion_resolvent = logger.emit_red_proof_line(
                    logger.reified(
                        logger.reified(bitsum + (ub_2.bound) * ProofBitVariable{mag_x, i, true} >= rhs, HalfReifyOnConjunctionOf{ub_1.condition, ub_2.condition}),
                        reason),
                    {},
                    ProofLevel::Temporary,
                    subproof);
                outer_sum.add_multiplied_by(fusion_resolvent, 1 << i);
            }

            logger.emit_proof_line(outer_sum.str(), ProofLevel::Temporary);
            outer_sum.add_multiplied_by(ub_1.line, ub_2.bound.raw_value);

            auto bitproducts_bound = logger.emit_proof_line(outer_sum.str(), ProofLevel::Temporary);
            logger.emit_proof_comment("Obtained bound:");
            auto mag_bound = logger.emit_proof_line("p " + to_string(bitproducts_bound) + " " + to_string(z_eq_product_lines.second) + " + ", ProofLevel::Temporary);
            if (channelling_constraints.contains(z)) {
                logger.emit_proof_comment("Channelled obtained bound:");
                if (! (positive_sign(ub_1.condition) ^ positive_sign(ub_2.condition))) {
                    auto rup_sign = logger.emit_rup_proof_line(
                        logger.reified(WeightedPseudoBooleanSum{} + Integer{1 << (logger.variable_constraints_tracker().num_bits(z) - 1)} * ProofBitVariable{z, 0, true} >= Integer{1 << logger.variable_constraints_tracker().num_bits(z)},
                            HalfReifyOnConjunctionOf{ub_1.condition, ub_2.condition, x != 0_i, y != 0_i}),
                        ProofLevel::Temporary);
                    logger.emit_proof_line("p " + to_string(mag_bound) + " " + to_string(channelling_constraints.at(z).pos_le) + " + ", ProofLevel::Temporary);
                    logger.weaken_lits(-1, {ProofBitVariable{z, 0, true}}, ProofLevel::Temporary);
                    logger.emit_proof_line("p -1 + " + to_string(rup_sign) + " + ", ProofLevel::Temporary);

                    return logger.emit_under_reason(IMPLIES,
                        logger.reified(WeightedPseudoBooleanSum{} + -1_i * z >= -wts_upper, HalfReifyOnConjunctionOf{ub_1.condition, ub_2.condition, x != 0_i, y != 0_i}),
                        ProofLevel::Temporary, reason);
                }
                else {
                    auto rup_sign = logger.emit_rup_proof_line(
                        logger.reified(WeightedPseudoBooleanSum{} + -Integer{1 << (logger.variable_constraints_tracker().num_bits(z) - 1)} * ProofBitVariable{z, 0, true} >= 0_i,
                            HalfReifyOnConjunctionOf{ub_1.condition, ub_2.condition, x != 0_i, y != 0_i}),
                        ProofLevel::Temporary);
                    logger.emit_proof_line("p " + to_string(mag_bound) + " " + to_string(channelling_constraints.at(z).neg_ge) + " + ", ProofLevel::Temporary);
                    logger.weaken_lits(-1, {ProofBitVariable{z, 0, true}}, ProofLevel::Temporary);
                    logger.emit_proof_line("p -1 " + to_string(rup_sign) + " + ", ProofLevel::Temporary);

                    return logger.emit_under_reason(IMPLIES,
                        logger.reified(WeightedPseudoBooleanSum{} + 1_i * z >= wts_lower, HalfReifyOnConjunctionOf{ub_1.condition, ub_2.condition, x != 0_i, y != 0_i}),
                        ProofLevel::Temporary, reason);
                }
            }
            else {
                if (! (positive_sign(ub_1.condition) ^ positive_sign(ub_2.condition))) {
                    return logger.emit_under_reason(IMPLIES,
                        logger.reified(WeightedPseudoBooleanSum{} + -1_i * z >= -wts_upper, HalfReifyOnConjunctionOf{ub_1.condition, ub_2.condition, x != 0_i, y != 0_i}),
                        ProofLevel::Temporary, reason);
                }
                else {
                    return logger.emit_under_reason(RUP,
                        logger.reified(WeightedPseudoBooleanSum{} + 1_i * z >= wts_lower, HalfReifyOnConjunctionOf{ub_1.condition, ub_2.condition, x != 0_i, y != 0_i}),
                        ProofLevel::Temporary, reason);
                }
            }
        };

        vector<ProofLine> fusion_resolvents_lower{};
        vector<ProofLine> fusion_resolvents_upper{};

        for (const auto & l1 : x_cond_lower) {
            for (const auto & l2 : y_cond_lower) {
                if (! (positive_sign(l1.condition) ^ positive_sign(l2.condition)))
                    fusion_resolvents_lower.emplace_back(prove_positive_product_lower_bounds(l1, l2));
                else
                    fusion_resolvents_upper.emplace_back(prove_positive_product_lower_bounds(l1, l2));
            }
        }

        for (const auto & u1 : x_cond_upper) {
            for (const auto & u2 : y_cond_upper) {
                if (! (positive_sign(u1.condition) ^ positive_sign(u2.condition)))
                    fusion_resolvents_upper.emplace_back(prove_positive_product_upper_bounds(u1, u2));
                else
                    fusion_resolvents_lower.emplace_back(prove_positive_product_upper_bounds(u1, u2));
            }
        }

        fusion_resolvents_lower.emplace_back(logger.emit_rup_proof_line_under_reason(state, reason,
            logger.reified(WeightedPseudoBooleanSum{} + 1_i * z >= final_bounds.first, HalfReifyOnConjunctionOf{x == 0_i}),
            ProofLevel::Temporary));
        fusion_resolvents_upper.emplace_back(logger.emit_rup_proof_line_under_reason(state, reason,
            logger.reified(WeightedPseudoBooleanSum{} + -1_i * z >= -final_bounds.second, HalfReifyOnConjunctionOf{x == 0_i}),
            ProofLevel::Temporary));

        map<string, JustifyExplicitly> subproof1{};

        auto justf1 = [&](const Reason &) {
            // logger.weaken_lits(-1, logger.reason_to_lits(reason), ProofLevel::Temporary);

            auto resolvents = vector<ProofLine>{};
            auto count = 1;
            for (auto & l : fusion_resolvents_lower) {
                resolvents.emplace_back(
                    logger.emit_proof_line("p -" + to_string(count) + " " + to_string(l) + " + s ", ProofLevel::Temporary));
                count++;
            }

            if (resolvents.size() == 4) {
                auto last = logger.emit_proof_line("p " + to_string(resolvents[0]) + " " + to_string(resolvents[1]) + " + s", ProofLevel::Temporary);
            }
            else if (resolvents.size() == 6) {
                auto r1 = logger.emit_proof_line("p " + to_string(resolvents[0]) + " " + to_string(resolvents[2]) + " + s", ProofLevel::Temporary);
                auto r2 = logger.emit_proof_line("p " + to_string(resolvents[1]) + " " + to_string(resolvents[3]) + " + s", ProofLevel::Temporary);
                logger.emit_proof_line("p " + to_string(r1) + " " + to_string(r2) + " + s", ProofLevel::Temporary);
            }

            logger.emit_proof_line("u >= 1 ;", ProofLevel::Temporary);
        };

        subproof1.emplace("#1", JustifyExplicitly{justf1});

        logger.emit_red_proof_line(
            logger.reified(WeightedPseudoBooleanSum{} + 1_i * z >= final_bounds.first, reason),
            {},
            ProofLevel::Current,
            subproof1);

        fusion_resolvents_lower.emplace_back(logger.emit_rup_proof_line_under_reason(state, reason,
            logger.reified(WeightedPseudoBooleanSum{} + 1_i * z >= final_bounds.first, HalfReifyOnConjunctionOf{y == 0_i}),
            ProofLevel::Temporary));
        fusion_resolvents_upper.emplace_back(logger.emit_rup_proof_line_under_reason(state, reason,
            logger.reified(WeightedPseudoBooleanSum{} + -1_i * z >= -final_bounds.second, HalfReifyOnConjunctionOf{y == 0_i}),
            ProofLevel::Temporary));

        map<string, JustifyExplicitly> subproof2{};

        auto justf2 = [&](const Reason &) {
            auto resolvents = vector<ProofLine>{};
            auto count = 1;
            for (auto & l : fusion_resolvents_upper) {
                resolvents.emplace_back(
                    logger.emit_proof_line("p -" + to_string(count) + " " + to_string(l) + " + s ", ProofLevel::Temporary));
                count++;
            }

            if (resolvents.size() == 4) {
                auto last = logger.emit_proof_line("p " + to_string(resolvents[0]) + " " + to_string(resolvents[1]) + " + s", ProofLevel::Temporary);
            }
            else if (resolvents.size() == 6) {
                auto r1 = logger.emit_proof_line("p " + to_string(resolvents[0]) + " " + to_string(resolvents[2]) + " + s", ProofLevel::Temporary);
                auto r2 = logger.emit_proof_line("p " + to_string(resolvents[1]) + " " + to_string(resolvents[3]) + " + s", ProofLevel::Temporary);
                logger.emit_proof_line("p " + to_string(r1) + " " + to_string(r2) + " + s", ProofLevel::Temporary);
            }

            logger.emit_proof_line("u >= 1 ;", ProofLevel::Temporary);
        };

        subproof2.emplace("#1", JustifyExplicitly{justf2});

        logger.emit_red_proof_line(
            logger.reified(WeightedPseudoBooleanSum{} + -1_i * z >= -final_bounds.second, reason),
            {},
            ProofLevel::Current,
            subproof2);
    }

    // Filter variable q where q * y = x based on bounds of x and y
    auto filter_quotient(SimpleIntegerVariableID q_var, Integer x_min, Integer x_max, Integer y_min, Integer y_max, const vector<IntegerVariableID> & all_vars, State & state, ProofLogger * const logger)
        -> Inference
    {
        // This is based on the case breakdown in JaCoP
        // https://github.com/radsz/jacop/blob/develop/src/main/java/org/jacop/core/IntDomain.java#L1377
        if (x_min <= 0_i && x_max >= 0_i && y_min <= 0_i && y_max >= 0_i) {
            // 0 is in the bounds of both x and y so no filtering possible
            return Inference::NoChange;
        }
        else if (y_min == 0_i && y_max == 0_i) {
            // y == 0 and 0 not in bounds of x => no possible values for q
            // No justification needed?
            return Inference::Contradiction;
        }
        else if (y_min < 0_i && y_max > 0_i && (x_min > 0_i || x_max < 0_i)) {
            // y contains -1, 0, 1 and x has either all positive or all negative values
            auto largest_possible_quotient = max(abs(x_min), abs(x_max));
            auto smallest_possible_quotient = -largest_possible_quotient;
            auto inf = state.infer(logger, q_var < largest_possible_quotient + 1_i, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
            increase_inference_to(inf, state.infer(logger, q_var >= smallest_possible_quotient, AssertRatherThanJustifying{}, generic_reason(state, all_vars)));
            return inf;
        }
        else if (y_min == 0_i && y_max != 0_i && (x_min > 0_i || x_max < 0_i)) {
            // y is either 0 or strictly positive and x has either all positive or all negative values
            return filter_quotient(q_var, x_min, x_max, 1_i, y_max, all_vars, state, logger);
        }
        else if (y_min != 0_i && y_max == 0_i && (x_min > 0_i || x_max < 0_i)) {
            // y is either 0 or strictly negative x has either all positive or all negative values
            return filter_quotient(q_var, x_min, x_max, y_min, -1_i, all_vars, state, logger);
        }
        else if ((y_min > 0_i || y_max < 0_i) && y_min <= y_max) {
            auto x1y1 = (double)x_min.raw_value / (double)y_min.raw_value;
            auto x1y2 = (double)x_min.raw_value / (double)y_max.raw_value;
            auto x2y1 = (double)x_max.raw_value / (double)y_min.raw_value;
            auto x2y2 = (double)x_max.raw_value / (double)y_max.raw_value;

            double smallest_real_quotient = min(min(x1y1, x1y2), min(x2y1, x2y2));
            double largest_real_quotient = max(max(x1y1, x1y2), max(x2y1, x2y2));
            auto smallest_possible_quotient = Integer{(long long)ceil(smallest_real_quotient)};
            auto largest_possible_quotient = Integer{(long long)floor(largest_real_quotient)};
            if (smallest_possible_quotient > largest_possible_quotient) {
                state.infer(logger, FalseLiteral{}, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
                return Inference::Contradiction;
            }
            auto inf = state.infer(logger, q_var < largest_possible_quotient + 1_i, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
            increase_inference_to(inf, state.infer(logger, q_var >= smallest_possible_quotient, AssertRatherThanJustifying{}, generic_reason(state, all_vars)));
            return inf;
        }
        else {
            throw UnexpectedException{
                "Bad interval passed to filter_quotient."};
        }
    }
}

MultBC::MultBC(const SimpleIntegerVariableID v1, const SimpleIntegerVariableID v2, const SimpleIntegerVariableID v3) :
    _v1(v1),
    _v2(v2), _v3(v3)
{
}

auto MultBC::clone() const -> unique_ptr<Constraint>
{
    return make_unique<MultBC>(_v1, _v2, _v3);
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
        auto make_magnitude_term = [&](SimpleIntegerVariableID & v, const string & name) -> pair<SimpleOrProofOnlyIntegerVariableID, ProofLiteralOrFlag> {
            auto sign_bit = ProofBitVariable{v, 0, true};
            if (initial_state.lower_bound(v) < 0_i) {
                auto largest_magnitude = max({abs(initial_state.lower_bound(v)), initial_state.upper_bound(v)});
                auto v_magnitude = optional_model->create_proof_only_integer_variable(0_i, largest_magnitude, name + "'", IntegerVariableProofRepresentation::Bits);

                auto bit_sum_without_neg = WeightedPseudoBooleanSum{};
                auto num_bits = optional_model->variable_constraints_tracker().num_bits(v);
                // Skip the neg bit
                for (unsigned int pos = 0; pos < num_bits - 1; pos++)
                    bit_sum_without_neg += Integer{1 << pos} * ProofBitVariable{v, pos + 1, true};

                auto [pos_le, pos_ge] = optional_model->add_constraint(bit_sum_without_neg + (-1_i * v_magnitude) == 0_i, HalfReifyOnConjunctionOf{! sign_bit});
                auto [neg_le, neg_ge] = optional_model->add_constraint(bit_sum_without_neg + (1_i * v_magnitude) == Integer{1 << (num_bits - 1)}, HalfReifyOnConjunctionOf{sign_bit});
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
                    WeightedPseudoBooleanSum{} + 1_i * ProofBitVariable{v1_mag, i, true} + 1_i * ProofBitVariable{v2_mag, j, true} >= 2_i, HalfReifyOnConjunctionOf{flag});

                auto backwards = optional_model->add_constraint(
                    WeightedPseudoBooleanSum{} + -1_i * ProofBitVariable{v1_mag, i, true} + -1_i * ProofBitVariable{v2_mag, j, true} >= -1_i, HalfReifyOnConjunctionOf{! flag});

                bit_products[i].emplace_back(BitProductData{flag, *forwards, *backwards, nullopt, nullopt});
                bit_product_sum += Integer{1 << (i + j)} * flag;
            }
        }

        // Seems like there ought to be a better way to do this...
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
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! xyss >= 1_i, HalfReifyOnConjunctionOf{! v1_sign, ! v2_sign});

        // Need to avoid duplicate constraints or else VeriPB segfaults
        if (mag_var.contains(_v1))
            optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * xyss >= 1_i, HalfReifyOnConjunctionOf{v1_sign, ! v2_sign});
        if (mag_var.contains(_v2))
            optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * xyss >= 1_i, HalfReifyOnConjunctionOf{! v1_sign, v2_sign});
        if (mag_var.contains(_v1) && mag_var.contains(_v2))
            optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! xyss >= 1_i, HalfReifyOnConjunctionOf{v1_sign, v2_sign});

        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * xyss + 1_i * (_v1 != 0_i) + 1_i * (_v2 != 0_i) >= 3_i, HalfReifyOnConjunctionOf{v3_sign});
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! xyss + 1_i * (_v1 == 0_i) + 1_i * (_v2 == 0_i) >= 1_i, HalfReifyOnConjunctionOf{! v3_sign});
    }

    ConstraintStateHandle bit_products_handle = initial_state.add_constraint_state(bit_products);
    propagators.install([v1 = _v1, v2 = _v2, v3 = _v3, bit_products_h = bit_products_handle, channelling_constraints = channelling_constraints,
                            mag_var = mag_var, v3_eq_product_lines = v3_eq_product_lines](State & state, ProofLogger * const logger) -> pair<Inference, PropagatorState> {
        vector<IntegerVariableID> all_vars = {v1, v2, v3};
        auto overall_result = Inference::NoChange;
        auto inf = Inference::NoChange;
        do {
            inf = Inference::NoChange;
            auto bounds1 = state.bounds(v1), bounds2 = state.bounds(v2);
            auto [smallest_product, largest_product] = get_product_bounds(bounds1.first, bounds1.second, bounds2.first, bounds2.second);

            auto upper_justf = [&, largest_product = largest_product, mag_var = mag_var](const Reason & reason) {
                prove_product_bounds(reason, *logger, state, v1, v2, v3, bit_products_h, channelling_constraints, mag_var, v3_eq_product_lines);
                logger->emit_proof_comment("Final bound RUP: ");
                logger->emit_rup_proof_line_under_reason(state, reason, WeightedPseudoBooleanSum{} + 1_i * (v3 < largest_product + 1_i) >= 1_i, ProofLevel::Current);
                logger->emit_rup_proof_line_under_reason(state, reason, WeightedPseudoBooleanSum{} + 1_i * (v3 >= smallest_product) >= 1_i, ProofLevel::Current);
            };

            increase_inference_to(inf, state.infer(logger, v3 < largest_product + 1_i, JustifyExplicitly{upper_justf}, generic_reason(state, all_vars)));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            auto lower_justf = JustifyExplicitly{[&, largest_product = largest_product, mag_var = mag_var](const Reason & reason) {
                prove_product_bounds(reason, *logger, state, v1, v2, v3, bit_products_h, channelling_constraints, mag_var, v3_eq_product_lines);

                logger->emit_rup_proof_line_under_reason(state, reason, WeightedPseudoBooleanSum{} + 1_i * (v3 < largest_product + 1_i) >= 1_i, ProofLevel::Current);
            }};

            if (Inference::NoChange != inf)
                lower_justf = JustifyExplicitly{[&, smallest_product = smallest_product, mag_var = mag_var](const Reason & reason) {
                    logger->emit_rup_proof_line_under_reason(state, reason, WeightedPseudoBooleanSum{} + 1_i * (v3 >= smallest_product) >= 1_i, ProofLevel::Current);
                }};

            increase_inference_to(inf, state.infer(logger, v3 >= smallest_product, lower_justf, generic_reason(state, all_vars)));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            auto bounds3 = state.bounds(v3);
            increase_inference_to(inf, filter_quotient(v1, bounds3.first, bounds3.second, bounds2.first, bounds2.second, all_vars, state, logger));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            bounds1 = state.bounds(v1);
            increase_inference_to(inf, filter_quotient(v2, bounds3.first, bounds3.second, bounds1.first, bounds1.second, all_vars, state, logger));

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
