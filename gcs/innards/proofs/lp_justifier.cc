#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/lp_justifier.hh>

#include <Highs.h>
#include <algorithm>
#include <map>

// TODO: Remove later
#include <iomanip>
//

using std::iota;
using std::make_optional;
using std::make_pair;
using std::map;
using std::max;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::vector;

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::lp_innards;

namespace
{
    // Helper functions: defined later.
    auto recover_am1_constraint(ProofLogger & logger, const WeightedPseudoBooleanSum & sum) -> ProofLine;
    auto variable_normalise(const WeightedPseudoBooleanLessEqual & constraint) -> WeightedPseudoBooleanLessEqual;
}

struct LPJustifier::Imp
{
    Highs highs;      // The HiGHs LP solver
    HighsModel model; // The base LP to solve
                      // (this is basically the transpose of the constraint's LP relaxation and
                      // will be restricted appropriately for each justification).

    ConstraintStateHandle last_basis_handle; // For hot-starts: currently unused

    vector<IntegerVariableID> dom_vars;   // CP Variables seen as 0-1 [var==val] variables by the LP solver
    vector<IntegerVariableID> bound_vars; // CP Variables seen as finite domain variables [var] by the LP solver

    vector<double> constraints_rhs; // base right-hand-side of the <= constraints that the LP solver sees

    map<long, ProofLine> known_proof_line_for_constraint; // Store lines of constraints already derived
    map<long, DerivationFunction> derive_constraint;      // Store how to derive other constraints

    map<PseudoBooleanTerm, long> var_number;                 // Each PB term has a unique col/row number (col in the primal, row in the dual)
    map<IntegerVariableID, long> upper_bound_constraint_num; // For the bound vars, the number of the upper bound constraint

    /*
     * Example LP Matrix Structure (before we take the transpose):
     *
     * var_number  ->    0    1    2    3    4
     *                 xe1  xe2  xe3   y1   y2
     *(con numbers)v + -----------------------       v(constraints_rhs)
     *             0 |  1    0    0    0    0 |  <=  1
     *             1 |  0    1    0    0    0 |  <=  1
     *             2 |  0    0    1    0    0 |  <=  1
     *               |          [...]         |
     *             6 |  1    1    1    0    0 |  <=  1
     *             7 | -1   -1   -1    0    0 |  <= -1
     *             8 |  0    0    0    1    0 |  <=  3
     *             9 |  0    0    0    0    1 |  <=  5
     *               |          [...]         |
     *               +------------------------+
     */
    explicit Imp(const LPJustificationOptions &)
    {
    }

    auto pass_and_solve_model(const WeightedPseudoBooleanLessEqual & inference,
        HighsModel & restricted_model, vector<double> rhs_updated, vector<long> new_row_num) -> const HighsSolution;
};

LPJustifier::LPJustifier(const LPJustificationOptions & o) :
    _imp(new Imp{o})
{
    // Make HiGHs shut up
    _imp->highs.setOptionValue("output_flag", false);

    // Does this affect anything? Doesn't seem to...
    //_imp->highs.setOptionValue("solver", "simplex");

    // Think these might be the defaults anyway, but just in case.
    _imp->model.lp_.sense_ = ObjSense::kMinimize;
    _imp->model.lp_.offset_ = 0;
}

LPJustifier::~LPJustifier() = default;

void LPJustifier::initialise_with_vars(State & state, vector<IntegerVariableID> dom_vars, vector<IntegerVariableID> bound_vars)
{
    /*
     * Initialise the base LP model with:
     * - 0-1 bounds on the 0-1 variables (dom_vars)
     * - AL1 and AM1 constraints on the 0-1 variables
     * - Actual bounds on the bound vars
     */

    // We now know which variables we will be dealing with as 0-1 literals
    // and which we use the actual vars for.
    _imp->dom_vars = move(dom_vars);
    _imp->bound_vars = move(bound_vars);

    int var_count = 0;
    int constr_count = 0;
    int non_zero_count = 0;

    // The right-hand-side bounds of the underlying constraints.
    vector<double> rhs;

    // HiGHs LPs are stored using sparse matrices, either row- or col-wise.
    // We will start with col-wise as it means we end up with the transpose by default.
    _imp->model.lp_.a_matrix_.format_ = MatrixFormat::kColwise;
    vector<int> start;    // start[c] is the position in index and value that column c starts on
    vector<int> index;    // index[j] is the (column) index of the jth non-zero
    vector<double> value; // value[j] is the value of the jth non-zero

    // So e.g. index[start[3]] is the index of the first non-zero in the 3rd column,
    // which is value[start[3]]

    // Okay, deal with the 0-1 literals first
    for (const auto & var : _imp->dom_vars) {
        WeightedPseudoBooleanSum dom_sum{};
        vector<int> var_numbers_for_dom_var;

        state.for_each_value(var, [&](Integer val) {
            _imp->var_number[var == val] = var_count;
            var_numbers_for_dom_var.emplace_back(var_count);
            dom_sum += 1_i * (var == val);

            // Literal axiom x <= 1
            start.emplace_back(non_zero_count);
            index.emplace_back(var_count);
            value.emplace_back(1);
            rhs.emplace_back(1);
            non_zero_count++;

            // We will never need to actually derive literal axioms,
            // even if the LPJustifier thinks they are necessary.
            // Why? Because if (C + literal axioms) propagates something
            // then certainly C propagates that something,
            // as literal axioms cannot affect slack.

            // -1 will be treated as "ignore" in this map
            _imp->known_proof_line_for_constraint[constr_count++] = -1;

            // Literal axiom -x <= 0
            start.emplace_back(non_zero_count);
            index.emplace_back(var_count);
            value.emplace_back(-1);
            rhs.emplace_back(0);
            non_zero_count++;
            _imp->known_proof_line_for_constraint[constr_count++] = -1;

            var_count++;
        });

        // AM1 constraint: sum_j( x_{i=j} ) <= 1
        start.emplace_back(non_zero_count);
        index.insert(index.end(), var_numbers_for_dom_var.begin(), var_numbers_for_dom_var.end());
        value.insert(value.end(), var_numbers_for_dom_var.size(), 1);
        rhs.emplace_back(1);

        non_zero_count += int(var_numbers_for_dom_var.size());

        _imp->derive_constraint[constr_count++] = [dom_sum](ProofLogger & logger, const State &) {
            return recover_am1_constraint(logger, dom_sum);
        };

        // AL1 constraints: sum_j( -x_{i=j} ) <= -1
        start.emplace_back(non_zero_count);
        index.insert(index.end(), var_numbers_for_dom_var.begin(), var_numbers_for_dom_var.end());
        value.insert(value.end(), var_numbers_for_dom_var.size(), -1);
        rhs.emplace_back(-1);

        non_zero_count += int(var_numbers_for_dom_var.size());

        _imp->derive_constraint[constr_count++] = [dom_sum](ProofLogger & logger, const State &) {
            return logger.emit_rup_proof_line_under_reason({}, dom_sum >= 1_i, ProofLevel::Top);
        };
    }

    // Now onto the bounds vars
    for (const auto & var : _imp->bound_vars) {
        _imp->var_number[var] = var_count;
        auto [lower, upper] = state.bounds(var);

        // Upper bound  (bound var <= upper)
        _imp->upper_bound_constraint_num[var] = constr_count;
        start.emplace_back(non_zero_count);
        index.emplace_back(var_count);
        value.emplace_back(1);
        // This will get modified later
        rhs.emplace_back(upper.raw_value);

        non_zero_count++;
        _imp->derive_constraint[constr_count++] = [var = var](ProofLogger & logger, const State & later_state) {
            // The constraint we actually derive for this is
            // [x<upper] => x < upper
            // For whatever the actual upper bound is when this is called.
            // Technically this could cause a problem
            auto later_upper = later_state.upper_bound(var);
            auto reason = [=]() { return Literals{var < later_upper + 1_i}; };
            return logger.emit_rup_proof_line_under_reason(reason,
                WeightedPseudoBooleanSum{} + 1_i * var <= later_upper, ProofLevel::Top);
        };

        // Lower bound (-bound var <= -lower)
        start.emplace_back(non_zero_count);
        index.emplace_back(var_count);
        value.emplace_back(-1);
        rhs.emplace_back(-lower.raw_value);
        non_zero_count++;

        _imp->derive_constraint[constr_count++] = [var = var](ProofLogger & logger, const State & later_state) {
            auto later_lower = later_state.lower_bound(var);
            auto reason = [=]() { return Literals{var >= later_lower}; };
            return logger.emit_rup_proof_line_under_reason(reason,
                WeightedPseudoBooleanSum{} + 1_i * var >= later_lower, ProofLevel::Top);
        };

        var_count++;
    }

    start.emplace_back(non_zero_count);

    // Swap cols and rows since we'll be solving the transpose
    _imp->model.lp_.num_row_ = var_count;
    _imp->model.lp_.num_col_ = constr_count;

    _imp->model.lp_.row_lower_ = vector<double>(_imp->model.lp_.num_row_, 0.0);
    _imp->model.lp_.row_upper_ = vector<double>(_imp->model.lp_.num_row_, 0.0);

    _imp->constraints_rhs = move(rhs);
    _imp->model.lp_.a_matrix_.start_ = start;
    _imp->model.lp_.a_matrix_.index_ = index;
    _imp->model.lp_.a_matrix_.value_ = value;
    _imp->model.lp_.setMatrixDimensions();

    //    optional<HighsBasis> optional_last_basis = nullopt;
    //    _imp->last_basis_handle = state.add_constraint_state(optional_last_basis);
}

auto LPJustifier::_add_pb_constraint_to_lp(const gcs::innards::WeightedPseudoBooleanLessEqual & pb_constraint) -> void
{
    auto normalised = variable_normalise(pb_constraint);
    long newNz = 0;
    for (const auto & term : normalised.lhs.terms) {
        long col;

        if (_imp->var_number.find(term.variable) != _imp->var_number.end()) {
            col = _imp->var_number[term.variable];
        }
        else {
            col = _imp->model.lp_.num_row_;
            _imp->var_number[term.variable] = _imp->model.lp_.num_row_++;
        }
        newNz++;
        _imp->model.lp_.a_matrix_.index_.emplace_back(col);
        _imp->model.lp_.a_matrix_.value_.emplace_back(term.coefficient.raw_value);
    }
    _imp->constraints_rhs.emplace_back(normalised.rhs.raw_value);
    _imp->model.lp_.a_matrix_.start_.emplace_back(_imp->model.lp_.a_matrix_.numNz() + newNz);
    _imp->model.lp_.num_col_++;
    _imp->model.lp_.setMatrixDimensions();
}

void LPJustifier::add_pb_constraint(const WeightedPseudoBooleanLessEqual & pb_constraint, ProofLine line)
{
    _add_pb_constraint_to_lp(pb_constraint);
    _imp->known_proof_line_for_constraint[_imp->model.lp_.num_col_ - 1] = line;
}

void LPJustifier::add_pb_constraint(const WeightedPseudoBooleanLessEqual & pb_constraint, DerivationFunction how_to_derive)
{
    _add_pb_constraint_to_lp(pb_constraint);
    _imp->derive_constraint[_imp->model.lp_.num_col_ - 1] = move(how_to_derive);
}

auto LPJustifier::compute_justification(const State & state, ProofLogger & logger, const WeightedPseudoBooleanLessEqual & inference,
    const bool compute_bounds) -> ExplicitJustificationFunction
{
    //  Restrict the constraint matrix based on the current state
    //  Need to do this outside the justification, because we rely on the current state
    auto restricted_model = _imp->model;

    // Make it Rowwise to make it easier to delete things.
    restricted_model.lp_.ensureRowwise();

    auto rhs_updated = _imp->constraints_rhs;

    vector<HighsInt> mask;
    vector<long> new_row_num(restricted_model.lp_.num_row_, 0);
    mask.assign(restricted_model.lp_.num_row_, 1);
    HighsIndexCollection to_delete{};

    auto restr_row_count = 0;
    for (auto var_iter = _imp->dom_vars.begin(); var_iter != _imp->dom_vars.end(); ++var_iter) {
        // Commenting this part out because it was breaking something and I'm not sure it makes a big difference time-wise
        //        if (state.has_single_value(*var_iter)) {
        //            // If there's only a single value actually do delete this.
        //            auto val = *state.optional_single_value(*var_iter);
        //            auto single_var_number = _imp->var_number[*var_iter == val];
        //
        //            // But modify the rhs since this literal became 1
        //            // Since we ensured the matrix was Rowwise we can just iterate through the nonZeros
        //            auto nz_from = _imp->model.lp_.a_matrix_.start_[single_var_number];
        //            auto nz_to = _imp->model.lp_.a_matrix_.start_[single_var_number] - 1;
        //            for (auto nz = nz_from; nz <= nz_to; ++nz) {
        //                auto constr = _imp->model.lp_.a_matrix_.index_[nz];
        //                rhs_updated[constr] -= _imp->model.lp_.a_matrix_.value_[nz];
        //            }
        //        }
        //        else {
        // Otherwise, preserve all the vals still in the domain
        state.for_each_value(*var_iter, [&](Integer val) {
            auto dont_delete = _imp->var_number[*var_iter == val];
            mask[dont_delete] = 0;
            new_row_num[dont_delete] = restr_row_count++;
        });
        //        }
    }

    for (const auto & var : _imp->bound_vars) {
        auto [lower, upper] = state.bounds(var);
        auto upper_constraint_num = _imp->upper_bound_constraint_num[var];
        auto lower_constraint_num = upper_constraint_num + 1;
        rhs_updated[upper_constraint_num] = (double)upper.raw_value;
        rhs_updated[lower_constraint_num] = -(double)lower.raw_value;
        new_row_num[_imp->var_number[var]] = restr_row_count++;
        mask[_imp->var_number[var]] = 0; // Don't delete the bound vars XD
    }

    restricted_model.lp_.ensureColwise();
    create(to_delete, mask.data(), restricted_model.lp_.num_row_);
    restricted_model.lp_.deleteRows(to_delete);

    restricted_model.lp_.col_cost_ = rhs_updated;
    restricted_model.lp_.col_lower_ = vector<double>(_imp->model.lp_.num_col_, 0.0);

    // Letting this be too large seems to cause numerical stability issues
    // even though the upper bound should theoretically be infinite.
    // I don't understand LP solvers :'(
    restricted_model.lp_.col_upper_ = vector<double>(_imp->model.lp_.num_col_, _imp->highs.getInfinity());

    HighsSolution solution_already;
    // Compute solution already, even if the justification isn't called
    WeightedPseudoBooleanLessEqual final_inference = inference;
    if (compute_bounds) {
        solution_already = _imp->pass_and_solve_model(inference, restricted_model, rhs_updated, new_row_num);
        // Update inference with the computed objective value
        final_inference = inference.lhs <= Integer{static_cast<long long>(_imp->highs.getInfo().objective_function_value)};
    }

    return [&state = state, &logger, inference = final_inference, &imp = _imp,
               restricted_model = move(restricted_model), rhs_updated, new_row_num,
               compute_bounds, solution_already = move(solution_already)](const Reason &) {
        HighsSolution solution;
        HighsModel restr_model = restricted_model;
        if (! compute_bounds)
            solution = imp->pass_and_solve_model(inference, restr_model, rhs_updated, new_row_num);
        else
            solution = solution_already;

        // Turn the solution into a pol step
        stringstream p_line;
        p_line << "p ";
        long count = 0;
        for (int col = 0; col < imp->highs.getLp().num_col_; col++) {
            auto coeff = solution.col_value[col];
            if (coeff != 0) {
                ProofLine line;

                if (imp->known_proof_line_for_constraint.find(col) != imp->known_proof_line_for_constraint.end()) {
                    // Ignore literal axioms
                    if (imp->known_proof_line_for_constraint.at(col) == -1)
                        continue;

                    // We already derived this, so just grab the proof line
                    p_line << imp->known_proof_line_for_constraint.at(col) << " ";
                }
                else {
                    // Otherwise, derive it, and cache the line for next time
                    line = imp->derive_constraint.at(col)(logger, state);

                    if (line == -1)
                        continue;
                    // Don't cache the bound var constraints
                    if (imp->bound_vars.empty() || col < imp->upper_bound_constraint_num.at(imp->bound_vars[0]) || col > imp->upper_bound_constraint_num.at(imp->bound_vars.back()) + 1)
                        imp->known_proof_line_for_constraint.emplace(col, line);

                    p_line << line << " ";
                }

                if (coeff > 1)
                    p_line << to_string(static_cast<long>(coeff)) << " * ";
                if (count >= 1) {
                    p_line << "+ ";
                }
                count++;
            }
        }

        bool bounding_var = false;

        if (inference.lhs.terms.size() == 1) {
            // Bounding a single variable
            overloaded{
                // So need to add this in order to swap the actual variable for the literal e.g. xvge3
                [&](IntegerVariableID v) {
                    bounding_var = true;
                    if (inference.lhs.terms[0].coefficient == -1_i) {
                        p_line << logger.emit_rup_proof_line_under_reason([&]() { return Literals{v < -inference.rhs}; }, WeightedPseudoBooleanSum{} + 1_i * v <= -inference.rhs - 1_i, ProofLevel::Temporary);
                        if (count >= 1) {
                            p_line << " + s";
                        }
                    }
                    else if (inference.lhs.terms[0].coefficient == 1_i) {
                        p_line << logger.emit_rup_proof_line_under_reason([&]() { return Literals{v >= inference.rhs + 1_i}; }, WeightedPseudoBooleanSum{} + -1_i * v <= -inference.rhs - 1_i, ProofLevel::Temporary);
                        if (count >= 1) {
                            p_line << " + s";
                        }
                    }
                },
                [](ProofLiteral) {}, [](ProofFlag) {}, [](ProofOnlySimpleIntegerVariableID) {}, [](ProofBitVariable) {}}
                .visit(inference.lhs.terms[0].variable);
        }

        if (count >= 2 || bounding_var) {
            // If there's only one constraint, no need to write a p line
            if (inference.lhs.terms.empty())
                logger.emit_proof_comment("Inferring contradiction.");

            logger.emit_proof_comment("Computed LP justification 2:");
            auto line = logger.emit_proof_line(p_line.str(), ProofLevel::Current);
            std::cout << "";
        }
    };
}

auto LPJustifier::Imp::pass_and_solve_model(const WeightedPseudoBooleanLessEqual & inference,
    HighsModel & restricted_model, vector<double> rhs_updated, vector<long> new_row_num) -> const HighsSolution
{
    HighsStatus return_status;
    // Are we inferring contradiction?  (0 <= k for k <= -1)
    bool inferring_contradiction = inference.lhs.terms.empty() && inference.rhs <= -1_i;

    return_status = this->highs.passModel(restricted_model);

    if (return_status != HighsStatus::kOk) {
        throw UnexpectedException{"Failed to create model for LP justification"};
    }

    // First modify the model depending on whether we're inferring contradiction
    if (inferring_contradiction) {
        //  Solving {min 0 : A^Ty = 0, b^Ty <= -1}
        auto new_idx = vector<HighsInt>{};
        auto new_val = vector<double>{};
        auto num_nz = 0;
        for (unsigned int col = 0; col < rhs_updated.size(); col++) {
            if (rhs_updated[col] != 0) {
                new_idx.emplace_back(col);
                new_val.emplace_back(rhs_updated[col]);
                num_nz++;
            }
        }

        // A^Ty = 0
        auto zero_col = vector<double>(this->highs.getNumCol(), 0);
        auto zero_row = vector<double>(this->highs.getNumRow(), 0);
        this->highs.changeColsCost(0, this->highs.getNumCol() - 1, zero_col.data());
        this->highs.changeRowsBounds(0, this->highs.getNumRow() - 1, zero_row.data(), zero_row.data());

        // Add an extra constraint for the rhs so that b^Ty <= -1
        this->highs.addRow(-this->highs.getInfinity(), -1, num_nz, new_idx.data(), new_val.data());
    }
    else {
        // Solving {min b^Ty : A^Ty = c} (where c is the coefficients of the inference)
        auto norm_inference = variable_normalise(inference);
        vector<double> row_bounds(this->highs.getNumRow(), 0);
        for (const auto & term : norm_inference.lhs.terms) {
            row_bounds[new_row_num[this->var_number.at(term.variable)]] = (double)term.coefficient.raw_value;
        }
        this->highs.changeRowsBounds(0, this->highs.getNumRow() - 1, row_bounds.data(), row_bounds.data());
    }

    if (return_status != HighsStatus::kOk) {
        throw UnexpectedException{"Failed to create model for LP justification "};
    }
    const HighsLp & lp = this->highs.getLp();

    // Now solve the model
    return_status = this->highs.run();

    // Check it worked
    const HighsModelStatus & model_status = this->highs.getModelStatus();
    const HighsInfo & info = this->highs.getInfo();
    const bool has_values = info.primal_solution_status;
    if ((return_status != HighsStatus::kOk && model_status != HighsModelStatus::kOptimal)) {
        throw UnexpectedException{"Failed to correctly solve model for LP justification"};
    }

    const HighsSolution & solution = this->highs.getSolution();

    return solution;
}

auto LPJustifier::compute_justification(const State & state, ProofLogger & logger, const Literals & inference,
    const bool compute_bounds) -> ExplicitJustificationFunction
{
    auto inf_sum = WeightedPseudoBooleanSum{};
    for (const auto & lit : inference)
        inf_sum += 1_i * lit;
    return compute_justification(state, logger, inf_sum >= 1_i, compute_bounds);
}

auto LPJustifier::compute_bound_and_justification(const State & state, ProofLogger & logger, const WeightedPseudoBooleanSum & to_bound)
    -> pair<Integer, ExplicitJustificationFunction>
{
    auto just = compute_justification(state, logger, to_bound <= 0_i, true);
    auto highs_obj = _imp->highs.getInfo().objective_function_value;
    auto bound = Integer(floor(highs_obj));

    return make_pair(bound, just);
}
namespace
{
    auto recover_am1_constraint(ProofLogger & logger, const WeightedPseudoBooleanSum & sum) -> ProofLine
    {
        /*
         * Derive sum <= 1 by deriving a contradiction from -sum >= 0
         * This takes |sum| rup steps in the subproof/
         *
         * @returns The ProofLine of the AM1.
         */
        map<string, Subproof> subproofs;
        subproofs["#1"] = [&](ProofLogger & sub_logger) {
            for (const auto & term : sum.terms)
                sub_logger.emit_rup_proof_line(WeightedPseudoBooleanSum{} + -1_i * term.variable >= 0_i, ProofLevel::Temporary);
            logger.emit_rup_proof_line(WeightedPseudoBooleanSum{} >= 1_i, ProofLevel::Temporary);
        };
        return logger.emit_red_proof_line(sum <= 1_i, {}, ProofLevel::Top, subproofs);
    }

    template <typename Var_>
    [[nodiscard]] auto make_term_positive(Integer coeff, VariableConditionFrom<Var_> cond)
        -> pair<Weighted<VariableConditionFrom<Var_>>, Integer>
    {
        /*
         * Ensure the term in a WeightedPseudoBoolean sum does not create a negative literal.
         *
         * @returns a pair consisting of the un-negated term and a number to add to the RHS.
         */
        switch (cond.op) {
            // So turn k * (var != value) >= b into -k * (var == val) >= b - k
        case VariableConditionOperator::NotEqual:
            return make_pair(-coeff * (cond.var == cond.value), -coeff);
        case VariableConditionOperator::Less:
            // And turn turn k * (var < value) >= b into -k * (var >= val) >= b - k
            return make_pair(-coeff * (cond.var >= cond.value), -coeff);
        case VariableConditionOperator::Equal:
        case VariableConditionOperator::GreaterEqual:
            // Otherwise, do nothing.
            return make_pair(coeff * (cond), 0_i);
        }
    }

    auto variable_normalise(const WeightedPseudoBooleanLessEqual & constraint) -> WeightedPseudoBooleanLessEqual
    {
        /*
         * Ensure a WeightedPseudoBooleanLessEqual has no negated literals by adjusting signs as necessary.
         *
         * @returns a variable normalised PB constraint.
         */
        WeightedPseudoBooleanSum normalised_lhs{};
        auto normalised_rhs = constraint.rhs;

        for (const auto & term : constraint.lhs.terms) {
            // Need to consider all possible term types (Aghh)
            overloaded{
                [&](const ProofLiteral & proof_lit) {
                    overloaded{
                        [&](const Literal & lit) {
                            overloaded{
                                [&](const TrueLiteral &) {
                                    // Treat this as coeff * 1
                                    normalised_rhs -= term.coefficient;
                                },
                                [&](const FalseLiteral &) {
                                    // Treat this as coeff * 0
                                },
                                [&](const IntegerVariableCondition & cond) {
                                    // Modify according to make_term_positive
                                    const auto & [pos_term, modify_rhs] = make_term_positive(term.coefficient, cond);
                                    normalised_lhs += pos_term;
                                    normalised_rhs += modify_rhs;
                                }}
                                .visit(lit);
                        },
                        [&](const ProofVariableCondition & cond) {
                            // Modify according to make_term_positive
                            const auto & [pos_term, modify_rhs] = make_term_positive(term.coefficient, cond);
                            normalised_lhs += pos_term;
                            normalised_rhs += modify_rhs;
                        }}
                        .visit(proof_lit);
                },
                [&](const ProofFlag & flag) {
                    if (! flag.positive) {
                        // k * <Negated flag> >= b becomes -k * <flag> >= b - k
                        normalised_lhs += -term.coefficient * ! flag;
                        normalised_rhs += -term.coefficient;
                    }
                    // Leave everything else as is
                    else {
                        normalised_lhs += term.coefficient * flag;
                    }
                },
                [&](const IntegerVariableID & iv) {
                    normalised_lhs += term.coefficient * iv;
                },
                [&](const ProofOnlySimpleIntegerVariableID & poiv) {
                    normalised_lhs += term.coefficient * poiv;
                },
                [&](const ProofBitVariable & pbv) {
                    normalised_lhs += term.coefficient * pbv;
                }}
                .visit(term.variable);
        }
        return (normalised_lhs <= normalised_rhs);
    }
}