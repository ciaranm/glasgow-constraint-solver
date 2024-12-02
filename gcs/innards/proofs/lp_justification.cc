#include <Highs.h>
#include <gcs/innards/proofs/lp_justification.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>
#include <map>
#include <vector>

// Temporary for DEBUGGING ONLY
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>

using std::cout;
using std::endl;
using std::function;
using std::make_pair;
using std::map;
using std::pair;
using std::string;
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
            break;
        case VariableConditionOperator::Less:
            return make_pair(-coeff * (cond.var >= cond.value), -coeff);
            break;
        case VariableConditionOperator::Equal:
        case VariableConditionOperator::GreaterEqual:
            return make_pair(coeff * (cond), 0_i);
        }
    }

    // Ensure that a PB constraint are in a consistent variable normalised form
    // i.e. all eqvars are var==val or var>=val and all proof flags are unnegated
    auto variable_normalise(const WeightedPseudoBooleanLessEqual & constraint) -> WeightedPseudoBooleanLessEqual
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
                                    const auto & [pos_term, modify_rhs] = make_term_positive(term.coefficient, cond);
                                    normalised_lhs += pos_term;
                                    normalised_rhs += modify_rhs;
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

}
auto gcs::innards::compute_lp_justification(
    const State & state,
    ProofLogger & logger,
    const WeightedPseudoBooleanLessEqual & inference,
    const vector<IntegerVariableID> & dom_vars,
    const vector<IntegerVariableID> & bound_vars,
    map<ProofLine, WeightedPseudoBooleanLessEqual> pb_constraints,
    bool compute_reason) -> pair<ExplicitJustificationFunction, Reason>
{
    map<PseudoBooleanTerm, long> col_number{};
    map<long, string> p_line_output_for_row{};
    auto col_count = 0;

    // Create a HiGHS instance
    Highs highs;
    HighsModel model;

    // Define the columns of the LP
    // Use 0-1 direct vars for dom_vars
    for (const auto & var : dom_vars) {
        state.for_each_value_immutable(var, [&](Integer val) {
            col_number[var == val] = col_count++;
        });
    }

    // And the actual variables for the bound_vars
    for (const auto & var : bound_vars) {
        col_number[var] = col_count++;
    }

    model.lp_.num_col_ = col_count;
    model.lp_.sense_ = ObjSense::kMinimize;
    model.lp_.offset_ = 0;
    model.lp_.col_cost_ = vector<double>(model.lp_.num_col_, 0.0);
    model.lp_.col_upper_ = vector<double>(model.lp_.num_col_, highs.getInfinity());
    model.lp_.col_lower_ = vector<double>(model.lp_.num_col_, 0.0);

    model.lp_.a_matrix_.format_ = MatrixFormat::kColwise;

    vector<int> start;
    vector<int> index;
    vector<double> value;

    auto non_zero_count = 0;
    for (const auto & [line, constraint] : pb_constraints) {
        auto normalised_constraint = variable_normalise(constraint);
        start.emplace_back(non_zero_count);
        for (const auto & term : constraint.lhs.terms) {
        }
    }

    ExplicitJustificationFunction just = [&](const Reason & reason) {
        logger.emit_under_reason(ProofRule::ASSERT, inference, ProofLevel::Current, reason);
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