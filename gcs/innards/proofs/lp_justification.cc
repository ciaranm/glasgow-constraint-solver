#include <Highs.h>
#include <gcs/innards/proofs/lp_justification.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>
#include <map>
#include <optional>
#include <vector>

// Temporary for DEBUGGING ONLY
#include "simplify_literal.hh"
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>

using std::cout;
using std::endl;
using std::function;
using std::make_pair;
using std::map;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::to_string;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

namespace
{
    template <typename Var_>
    [[nodiscard]] auto make_term_positive(Integer coeff, VariableConditionFrom<Var_> cond)
        -> pair<Weighted<VariableConditionFrom<Var_>>, Integer>
    {
        switch (cond.op) {
        case VariableConditionOperator::NotEqual:
            return make_pair(-coeff * (cond.var == cond.value), -coeff);
        case VariableConditionOperator::Less:
            return make_pair(-coeff * (cond.var >= cond.value), -coeff);
        case VariableConditionOperator::Equal:
        case VariableConditionOperator::GreaterEqual:
            return make_pair(coeff * (cond), 0_i);
        }
    }

    // Ensure that a PB constraint are in a consistent variable normalised form
    // i.e. all eqvars are var==val or var>=val and all proof flags are un-negated
    // Also apply any known assignments from state
    auto variable_normalise(const WeightedPseudoBooleanLessEqual & constraint, const optional<State> & state = nullopt) -> WeightedPseudoBooleanLessEqual
    {
        WeightedPseudoBooleanSum normalised_lhs{};
        auto normalised_rhs = constraint.rhs;

        for (const auto & term : constraint.lhs.terms) {
            // Aghh..
            overloaded{
                [&](const ProofLiteral & proof_lit) {
                    overloaded{
                        [&](const Literal & lit) {
                            overloaded{
                                [&](const TrueLiteral &) {
                                    normalised_rhs -= term.coefficient;
                                },
                                [&](const FalseLiteral &) {},
                                [&](const IntegerVariableCondition & cond) {
                                    if (state.has_value()) {
                                        switch (cond.op) {
                                        case VariableConditionOperator::NotEqual:
                                            if (! state->in_domain(cond.var, cond.value)) {
                                                normalised_rhs -= term.coefficient;
                                            }
                                            else if (state->has_single_value(cond.var) && *state->optional_single_value(cond.var) == cond.value) {
                                                normalised_rhs += term.coefficient;
                                            }
                                            break;
                                        case VariableConditionOperator::Equal:
                                            if (! state->in_domain(cond.var, cond.value)) {
                                                normalised_rhs += term.coefficient;
                                            }
                                            else if (state->has_single_value(cond.var) && *state->optional_single_value(cond.var) == cond.value) {
                                                normalised_rhs -= term.coefficient;
                                            }
                                            break;
                                        case VariableConditionOperator::Less:
                                            normalised_lhs += -term.coefficient * (cond.var >= cond.value);
                                            normalised_rhs += -term.coefficient;
                                            break;

                                        case VariableConditionOperator::GreaterEqual:
                                            normalised_lhs += term.coefficient * cond;
                                            break;
                                        }
                                    }
                                    else {
                                        const auto & [pos_term, modify_rhs] = make_term_positive(term.coefficient, cond);
                                        normalised_lhs += pos_term;
                                        normalised_rhs += modify_rhs;
                                    }
                                }}
                                .visit(lit);
                        },
                        [&](const ProofVariableCondition & cond) {
                            const auto & [pos_term, modify_rhs] = make_term_positive(term.coefficient, cond);
                            normalised_lhs += pos_term;
                            normalised_rhs += modify_rhs;
                        }}
                        .visit(proof_lit);
                },
                [&](const ProofFlag & flag) {
                    if (! flag.positive) {
                        normalised_lhs += -term.coefficient * ! flag;
                        normalised_rhs += -term.coefficient;
                    }
                    else {
                        normalised_lhs += term.coefficient * flag;
                    }
                },
                [&](const IntegerVariableID & iv) {
                    normalised_lhs += term.coefficient * iv;
                },
                [&](const ProofOnlySimpleIntegerVariableID & poiv) {
                    normalised_lhs += term.coefficient * poiv;
                }}
                .visit(term.variable);
        }
        return (normalised_lhs <= normalised_rhs);
    }

    auto recover_am1_constraint(const Reason & reason, ProofLogger & logger, const WeightedPseudoBooleanSum & sum) -> ProofLine
    {
        stringstream proofline;
        auto terms = sum.terms;
        logger.emit_proof_comment("Prove AM1:");
        if (terms.size() > 1) {
            auto k = ++terms.begin();
            auto l = terms.begin();
            proofline << "p "
                      << logger.emit_rup_proof_line_under_reason(
                             reason, WeightedPseudoBooleanSum{} + 1_i * (*l).variable + 1_i * (*k).variable <= 1_i,
                             ProofLevel::Temporary);
            k++;
            auto k_count = 2;
            while (k != terms.end()) {
                proofline << " " << k_count << " * ";
                l = terms.begin();
                while (l != k) {
                    proofline << logger.emit_rup_proof_line_under_reason(
                                     reason, WeightedPseudoBooleanSum{} + 1_i * (*l).variable + 1_i * (*k).variable <= 1_i,
                                     ProofLevel::Temporary)
                              << " + ";
                    l++;
                }
                proofline << k_count + 1 << " d ";
                k++;
                k_count++;
            }
            return logger.emit_proof_line(proofline.str(), ProofLevel::Temporary);
        }
        else if (terms.size() == 1) {
            return logger.emit_rup_proof_line_under_reason(
                reason, sum <= 1_i,
                ProofLevel::Temporary);
        }
        else
            throw UnexpectedException{"trying to prove an AM1 over zero values?"};
    }
}
auto gcs::innards::compute_lp_justification(
    const State & state,
    ProofLogger & logger,
    const WeightedPseudoBooleanLessEqual & inference,
    const vector<SimpleIntegerVariableID> & dom_vars,
    const vector<SimpleIntegerVariableID> & bound_vars,
    const map<ProofLine, WeightedPseudoBooleanLessEqual> & pb_constraints,
    bool compute_reason) -> pair<ExplicitJustificationFunction, Reason>
{
    map<PseudoBooleanTerm, int> col_number{};
    map<long, function<string(const Reason &)>> p_line_output_for_row{};
    auto col_count = 0;

    // Create a HiGHS (LP Solver) instance
    Highs highs;

    // Now populate the model
    // I wonder if I can avoid doing this from scratch every time
    HighsModel model;

    vector<int> start;
    vector<int> index;
    vector<double> value;
    auto non_zero_count = 0;
    auto row_count = 0;
    vector<double> rhs;

    // Use 0-1 direct vars for dom_vars
    for (const auto & var : dom_vars) {

        WeightedPseudoBooleanSum dom_sum{};
        vector<int> dom_index;

        state.for_each_value_immutable(var, [&](Integer val) {
            // Lit axioms: var != val >= 0
            // i.e. var==var <= 1
            start.emplace_back(non_zero_count);
            index.emplace_back(col_count);
            value.emplace_back(1);
            rhs.emplace_back(1);
            non_zero_count++;
            p_line_output_for_row[row_count++] = [&](const Reason &) {
                logger.variable_constraints_tracker().need_proof_name(var != val);
                return logger.variable_constraints_tracker().proof_name(var != val);
            };

            // Lit axioms: var == val >= 0
            // i.e. -var==var <= -1
            start.emplace_back(non_zero_count);
            index.emplace_back(col_count);
            value.emplace_back(-1);
            rhs.emplace_back(-1);
            non_zero_count++;
            p_line_output_for_row[row_count++] = [&](const Reason &) {
                logger.variable_constraints_tracker().need_proof_name(var == val);
                return logger.variable_constraints_tracker().proof_name(var == val);
            };

            dom_index.emplace_back(col_count);
            col_number[var == val] = col_count++;
            dom_sum += 1_i * (var == val);
        });

        // AM1 constraint
        start.emplace_back(non_zero_count);
        index.insert(index.end(), dom_index.begin(), dom_index.end());
        value.insert(value.end(), dom_index.size(), 1);
        rhs.emplace_back(1);
        non_zero_count += int(dom_index.size());
        p_line_output_for_row[row_count++] = [&](const Reason & reason) {
            return to_string(recover_am1_constraint(reason, logger, dom_sum));
        };

        // AL1 constraints
        start.emplace_back(non_zero_count);
        index.insert(index.end(), dom_index.begin(), dom_index.end());
        value.insert(value.end(), dom_index.size(), -1);
        rhs.emplace_back(-1);
        non_zero_count += int(dom_index.size());
        p_line_output_for_row[row_count++] = [&](const Reason & reason) {
            return to_string(logger.emit_rup_proof_line_under_reason(reason, dom_sum >= 1_i, ProofLevel::Temporary)));
        };
    }

    // And the actual variables for the bound_vars
    for (const auto & var : bound_vars) {
        auto [lower, upper] = state.bounds(var);

        // Upper bound
        start.emplace_back(non_zero_count);
        index.emplace_back(col_count);
        value.emplace_back(1);
        rhs.emplace_back(upper.raw_value);
        non_zero_count++;
        p_line_output_for_row[row_count++] = [&](const Reason & reason) {
            return to_string(logger.emit_rup_proof_line_under_reason(reason,
                WeightedPseudoBooleanSum{} + 1_i * var <= upper, ProofLevel::Temporary));
        };

        // Lower bound
        start.emplace_back(non_zero_count);
        index.emplace_back(col_count);
        value.emplace_back(-1);
        rhs.emplace_back(-lower.raw_value);
        non_zero_count++;
        p_line_output_for_row[row_count++] = [&](const Reason & reason) {
            return to_string(logger.emit_rup_proof_line_under_reason(reason,
                WeightedPseudoBooleanSum{} + 1_i * var >= lower, ProofLevel::Temporary));
        };

        col_number[var] = col_count++;
    }

    // LP rows from PB constraints
    for (const auto & [line, constraint] : pb_constraints) {
        auto normalised_constraint = variable_normalise(constraint);
        start.emplace_back(non_zero_count);
        for (const auto & term : constraint.lhs.terms) {
            int col;
            if (col_number.find(term.variable) != col_number.end()) {
                col = col_number[term.variable];
            }
            else {
                col = col_count;
                col_number[term.variable] = col_count++;
            }
            index.emplace_back(col);
            value.emplace_back(term.coefficient.raw_value);
            non_zero_count++;
        }
        rhs.emplace_back(constraint.rhs.raw_value);
        p_line_output_for_row[row_count++] = [&](const Reason &) { return to_string(line); };
    }

    // Mark the end of the matrix
    start.emplace_back(non_zero_count);

    bool inferring_contradiction = inference.lhs.terms.empty() && inference.rhs <= -1_i;

    if (inferring_contradiction) {
        // Add an extra column for the rhs
        for (int row = 0; row < row_count; row++) {
            index.insert(index.begin() + start[row + 1], row);
            value.insert(value.begin() + start[row + 1], rhs[row]);
            col_count++;
        }
    }
    // Use the transpose for the dual problem
    model.lp_.a_matrix_.format_ = MatrixFormat::kColwise;
    model.lp_.num_row_ = col_count + 1;
    model.lp_.num_col_ = row_count;
    model.lp_.sense_ = ObjSense::kMinimize;
    model.lp_.offset_ = 0;
    model.lp_.a_matrix_.start_ = start;
    model.lp_.a_matrix_.index_ = index;
    model.lp_.a_matrix_.value_ = value;

    // The solution will be the coefficients in the pol step, so should be positive
    model.lp_.col_lower_ = vector<double>(model.lp_.num_col_, 0.0);
    model.lp_.col_upper_ = vector<double>(model.lp_.num_col_, highs.getInfinity());

    if (inferring_contradiction) {
        // Solving {min 0 : A^Ty = 0, b^Ty <= -1}
        model.lp_.col_cost_ = vector<double>(model.lp_.num_col_, 0.0);
        model.lp_.row_lower_ = vector<double>(model.lp_.num_row_, 0.0);
        model.lp_.row_upper_ = vector<double>(model.lp_.num_row_, 0.0);
        model.lp_.row_lower_.back() = -highs.getInfinity();
        model.lp_.row_upper_.back() = -1;
    }
    else {
        // Solving {min b^Ty : A^Ty = c},
        model.lp_.col_cost_ = rhs;
        vector<double> row_bounds{};
        for (const auto & term : inference.lhs.terms) {
            row_bounds.emplace_back(term.coefficient.raw_value);
        }
        model.lp_.row_upper_ = row_bounds;
        model.lp_.row_lower_ = row_bounds;
    }

    HighsStatus return_status;
    return_status = highs.passModel(model);
    if (return_status != HighsStatus::kOk) {
        throw UnexpectedException{"Failed to create model for LP justification"};
    }
    const HighsLp & lp = highs.getLp();

    // Now solve the model
    return_status = highs.run();

    // Check it worked
    const HighsModelStatus & model_status = highs.getModelStatus();
    const HighsInfo & info = highs.getInfo();
    const bool has_values = info.primal_solution_status;
    if (return_status != HighsStatus::kOk || model_status != HighsModelStatus::kOptimal || ! has_values) {
        throw UnexpectedException{"Failed to correctly solve model for LP justification"};
    }

    const HighsSolution & solution = highs.getSolution();

    // A question is whether to do all of the above in the justification function or not
    // Probably important for lazy justifications but doesn't make a difference for now I don't think.
    ExplicitJustificationFunction just = [&](const Reason & reason) {
        // Turn the solution into a pol step
        stringstream p_line;
        p_line << "p ";
        bool first = true;
        for (int col = 0; col < lp.num_col_; col++) {
            auto coeff = solution.col_value[col];
            if (coeff != 0) {
                p_line << p_line_output_for_row[col](reason) << " " << to_string(coeff) << " * ";
            }
            if (! first) {
                p_line << "+ ";
            }
            else {
                first = false;
            }
        }
        logger.emit_proof_line(p_line.str(), ProofLevel::Current);
    };

    vector<IntegerVariableID> all_vars{};
    all_vars.insert(all_vars.end(), dom_vars.begin(), dom_vars.end());
    all_vars.insert(all_vars.end(), bound_vars.begin(), bound_vars.end());

    auto reason = generic_reason(state, all_vars);
    return make_pair(just, reason);
}

namespace
{
    // For sanity checking / debugging only
    auto test_variable_normalisation() -> void
    {
        ProofOptions proof_options{"normalisation_test.opb", "normalisation_test.pbp"};

        VariableConstraintsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);

        tracker.start_writing_model(&model);

        vector<PseudoBooleanTerm> terms = {
            TrueLiteral{},
            model.create_proof_flag("t"),
            model.create_proof_only_integer_variable(1_i, 10_i, "x", IntegerVariableProofRepresentation::Bits)};

        auto reif = HalfReifyOnConjunctionOf{FalseLiteral{}, model.create_proof_flag("r")};

        auto x = model.create_proof_only_integer_variable(1_i, 10_i, "z", IntegerVariableProofRepresentation::Bits);
        auto y = model.create_proof_only_integer_variable(1_i, 10_i, "w", IntegerVariableProofRepresentation::Bits);

        auto constr =
            WeightedPseudoBooleanSum{} +
                5_i * TrueLiteral{} +
                -10_i * FalseLiteral{} +
                3_i * model.create_proof_flag("q") +
                10_i * (x >= 2_i) +
                2_i * y >=
            4_i;

        model.emit_model_comment("test constraint:");
        model.add_constraint(constr);
        model.emit_model_comment("normalised constraint:");
        model.add_constraint(variable_normalise(constr));
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);

        logger.conclude_none();
    }
}

auto main() -> int
{
    test_variable_normalisation();
}