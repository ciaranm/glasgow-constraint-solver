#include <gcs/innards/proofs/lp_justifier.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>

#include <Highs.h>
#include <algorithm>
#include <map>
#include <sstream>

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
using std::vector;

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::lp_innards;

namespace
{
    // For debugging purposes only
    auto get_matrix_string(HighsSparseMatrix matr) -> string
    {
        stringstream str;
        vector<vector<double>> full_matrix(matr.num_row_, vector<double>(matr.num_col_));
        if (matr.format_ == MatrixFormat::kRowwise) {
            for (int row = 0; row < matr.num_row_; ++row) {
                for (int j = matr.start_[row]; j < matr.start_[row + 1]; ++j) {
                    int col = matr.index_[j];
                    full_matrix[row][col] = matr.value_[j];
                }
            }
        }
        else {
            for (int col = 0; col < matr.num_col_; ++col) {
                for (int j = matr.start_[col]; j < matr.start_[col + 1]; ++j) {
                    int row = matr.index_[j];
                    full_matrix[row][col] = matr.value_[j];
                }
            }
        }

        for (const auto & row : full_matrix) {
            for (double elem : row) {
                str << elem << " ";
            }
            str << "\n";
        }

        return str.str();
    }

    auto recover_am1_constraint(ProofLogger & logger, const WeightedPseudoBooleanSum & sum) -> ProofLine
    {

        map<string, Subproof> subproofs;
        subproofs["#1"] = [&](ProofLogger & sub_logger) {
            for (const auto & term : sum.terms)
                sub_logger.emit_rup_proof_line(WeightedPseudoBooleanSum{} + -1_i * term.variable >= 0_i, ProofLevel::Temporary);
            logger.emit_rup_proof_line(WeightedPseudoBooleanSum{} >= 1_i, ProofLevel::Temporary);
        };
        return logger.emit_red_proof_line(sum <= 1_i, {}, ProofLevel::Temporary, subproofs);
    }

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
                },
                [&](const ProofBitVariable & pbv) {
                    normalised_lhs += term.coefficient * pbv;
                }}
                .visit(term.variable);
        }
        return (normalised_lhs <= normalised_rhs);
    }

}

struct LPJustifier::Imp
{
    Highs highs;                             // The HiGHs LP solver
    HighsModel model;                        // Base LP to solve
    ConstraintStateHandle last_basis_handle; // For hotstarts

    vector<IntegerVariableID> dom_vars;   // CP Variables seen as 0-1 [var==val] variables by the LP solver
    vector<IntegerVariableID> bound_vars; // CP Variables seen as finite domain variables [var] by the LP solver

    vector<double> constraints_rhs; // base right-hand-side of the <= constraints that the LP solver sees

    map<long, ProofLine> known_proof_line_for_constraint; // Store lines of constraints already derived
    map<long, DerivationFunction> derive_constraint;      // Store how to derive other constraints

    map<PseudoBooleanTerm, long> var_number;                 // Each PB term has a unique col/row number (col in the primal, row in the dual)
    map<IntegerVariableID, long> upper_bound_constraint_num; // For the bound vars, the number of the constraint for the upper bound

    long cache_after;
    explicit Imp(const LPJustificationOptions &)
    {
        // Maybe set some options here ?
    }
};

LPJustifier::LPJustifier(const LPJustificationOptions & o) :
    _imp(new Imp{o})
{
}

LPJustifier::~LPJustifier() = default;

void LPJustifier::initialise_with_vars(State & state, vector<IntegerVariableID> dom_vars, vector<IntegerVariableID> bound_vars)
{
    _imp->dom_vars = move(dom_vars);
    _imp->bound_vars = move(bound_vars);
    _imp->highs.setOptionValue("output_flag", false);

    _imp->model.lp_.a_matrix_.format_ = MatrixFormat::kColwise;
    _imp->model.lp_.sense_ = ObjSense::kMinimize;
    _imp->model.lp_.offset_ = 0;

    // The solution will be the coefficients in the pol step, so should be positive
    _imp->model.lp_.row_lower_ = vector<double>(_imp->model.lp_.num_col_, 0.0);
    _imp->model.lp_.row_upper_ = vector<double>(_imp->model.lp_.num_col_, _imp->highs.getInfinity());

    int col_count = 0;
    int non_zero_count = 0;
    int row_count = 0;

    vector<int> start;
    vector<int> index;
    vector<double> value;
    vector<double> rhs;

    for (const auto & var : _imp->dom_vars) {
        WeightedPseudoBooleanSum dom_sum{};
        vector<int> dom_index;
        auto first = col_count;
        auto last = col_count - 1;
        state.for_each_value(var, [&](Integer val) {
            // Literal axiom x <= 1
            start.emplace_back(non_zero_count);
            index.emplace_back(col_count);
            value.emplace_back(1);
            rhs.emplace_back(1);
            non_zero_count++;
            _imp->known_proof_line_for_constraint[row_count++] = -1;

            // Literal axiom -x <= 0
            start.emplace_back(non_zero_count);
            index.emplace_back(col_count);
            value.emplace_back(-1);
            rhs.emplace_back(0);
            non_zero_count++;
            _imp->known_proof_line_for_constraint[row_count++] = -1;

            dom_index.emplace_back(col_count);
            _imp->var_number[var == val] = col_count++;
            last = col_count;
            dom_sum += 1_i * (var == val);
        });

        // AM1 constraint
        start.emplace_back(non_zero_count);
        index.insert(index.end(), dom_index.begin(), dom_index.end());
        value.insert(value.end(), dom_index.size(), 1);
        rhs.emplace_back(1);

        non_zero_count += int(dom_index.size());

        _imp->derive_constraint[row_count++] = [var = var](ProofLogger & logger, const State & later_state) {
            WeightedPseudoBooleanSum dom_sum;
            later_state.for_each_value(var, [&](Integer val) {
                dom_sum += 1_i * (var == val);
            });
            return recover_am1_constraint(logger, dom_sum);
        };

        // AL1 constraints: dom vars >= 1
        start.emplace_back(non_zero_count);
        index.insert(index.end(), dom_index.begin(), dom_index.end());
        value.insert(value.end(), dom_index.size(), -1);
        rhs.emplace_back(-1);
        non_zero_count += int(dom_index.size());

        _imp->derive_constraint[row_count++] = [var = var](ProofLogger & logger, const State & later_state) {
            if (later_state.has_single_value(var)) {
                return ProofLine{-1};
            }
            WeightedPseudoBooleanSum dom_sum;
            later_state.for_each_value(var, [&](Integer val) {
                dom_sum += 1_i * (var == val);
            });
            return logger.emit_rup_proof_line_under_reason(generic_reason(later_state, {var}), dom_sum >= 1_i, ProofLevel::Temporary);
        };
    }

    for (const auto & var : _imp->bound_vars) {
        // bound var <= upper bound
        auto [lower, upper] = state.bounds(var);

        // Upper bound
        start.emplace_back(non_zero_count);
        index.emplace_back(col_count);
        value.emplace_back(1);
        rhs.emplace_back(upper.raw_value);
        _imp->upper_bound_constraint_num[var] = non_zero_count++;

        _imp->derive_constraint[row_count++] = [var = var](ProofLogger & logger, const State & later_state) {
            auto later_upper = later_state.upper_bound(var);
            auto reason = [=]() { return Literals{var >= -later_upper}; };
            return logger.emit_rup_proof_line_under_reason(reason,
                WeightedPseudoBooleanSum{} + 1_i * var <= later_upper, ProofLevel::Temporary);
        };

        // Lower bound
        start.emplace_back(non_zero_count);
        index.emplace_back(col_count);
        value.emplace_back(-1);
        rhs.emplace_back(-lower.raw_value);
        non_zero_count++;

        _imp->derive_constraint[row_count++] = [var = var](ProofLogger & logger, const State & later_state) {
            auto later_lower = later_state.lower_bound(var);
            auto reason = [=]() { return Literals{var >= later_lower}; };
            return logger.emit_rup_proof_line_under_reason(reason,
                WeightedPseudoBooleanSum{} + 1_i * var >= later_lower, ProofLevel::Temporary);
        };
        _imp->var_number[var] = col_count++;
    }

    start.emplace_back(non_zero_count);

    // Swap cols and rows since we'll be solving the transpose
    _imp->model.lp_.num_row_ = col_count;
    _imp->model.lp_.num_col_ = row_count;

    _imp->cache_after = row_count;

    _imp->model.lp_.row_lower_ = vector<double>(_imp->model.lp_.num_row_, 0.0);
    _imp->model.lp_.row_upper_ = vector<double>(_imp->model.lp_.num_row_, 0.0);

    _imp->constraints_rhs = move(rhs);
    _imp->model.lp_.sense_ = ObjSense::kMinimize;
    _imp->model.lp_.offset_ = 0;
    _imp->model.lp_.a_matrix_.start_ = start;
    _imp->model.lp_.a_matrix_.index_ = index;
    _imp->model.lp_.a_matrix_.value_ = value;
    _imp->model.lp_.setMatrixDimensions();

    optional<HighsBasis> optional_last_basis = nullopt;
    _imp->last_basis_handle = state.add_constraint_state(optional_last_basis);
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

auto LPJustifier::compute_justification(const State & state, ProofLogger & logger, const WeightedPseudoBooleanLessEqual & inference) -> ExplicitJustificationFunction
{
    // Restrict the constraint matrix based on the current state
    auto restricted_model = _imp->model;
    auto rhs_updated = _imp->constraints_rhs;

    auto & optional_last_basis = any_cast<optional<HighsBasis> &>(state.get_constraint_state(_imp->last_basis_handle));
    optional<HighsBasis> optional_current_basis = optional_last_basis ? make_optional(HighsBasis{}) : nullopt;

    vector<HighsInt> mask;
    vector<long> new_row_num(restricted_model.lp_.num_row_, 0);
    vector<long> old_row_num{};
    mask.assign(restricted_model.lp_.num_row_, 1);
    HighsIndexCollection to_delete{};

    auto restr_row_count = 0;
    for (auto var_iter = _imp->dom_vars.begin(); var_iter != _imp->dom_vars.end(); ++var_iter) {
        state.for_each_value(*var_iter, [&](Integer val) {
            auto dont_delete = _imp->var_number[*var_iter == val];
            mask[dont_delete] = 0;
            new_row_num[dont_delete] = restr_row_count++;
            old_row_num.emplace_back(dont_delete);
        });
    }

    if (optional_current_basis) {
        // Set the current basis based on the last basis, excluding deleted rows
        optional_current_basis->col_status = optional_last_basis->col_status;
        optional_current_basis->row_status = optional_last_basis->row_status;
        for (unsigned int row = 0; row < optional_current_basis->row_status.size(); ++row) {
            if (mask[row] == 1)
                optional_current_basis->row_status[row] = HighsBasisStatus::kNonbasic;
        }
    }

    create(to_delete, mask.data(), restricted_model.lp_.num_row_);
    restricted_model.lp_.deleteRows(to_delete);

    for (const auto & var : _imp->bound_vars) {
        auto [lower, upper] = state.bounds(var);
        auto upper_constraint_num = _imp->upper_bound_constraint_num[var];
        auto lower_constraint_num = upper_constraint_num + 1;
        rhs_updated[upper_constraint_num] = (double)upper.raw_value;
        rhs_updated[lower_constraint_num] = -(double)lower.raw_value;
        new_row_num[_imp->var_number[var]] = restr_row_count++;
        old_row_num.emplace_back(_imp->var_number[var]);
    }

    restricted_model.lp_.col_cost_ = rhs_updated;
    restricted_model.lp_.col_lower_ = vector<double>(_imp->model.lp_.num_col_, 0.0);
    restricted_model.lp_.col_upper_ = vector<double>(_imp->model.lp_.num_col_, _imp->highs.getInfinity());

    return [&state = state, &logger, inference = inference, &imp = _imp, &optional_last_basis, &optional_current_basis,
               restricted_model = restricted_model, rhs_updated = rhs_updated,
               new_row_num = new_row_num, old_row_num = old_row_num](const Reason & reason) {
        HighsStatus return_status;
        bool inferring_contradiction = inference.lhs.terms.empty() && inference.rhs <= -1_i;

        return_status = imp->highs.passModel(restricted_model);
        if (return_status != HighsStatus::kOk) {
            throw UnexpectedException{"Failed to create model for LP justification"};
        }

        // First modify the model depending on whether we're inferring contradiction
        if (inferring_contradiction) {
            // std::cout << "Inferring contradiction" << std::endl;
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
            auto zero_col = vector<double>(imp->highs.getNumCol(), 0);
            auto zero_row = vector<double>(imp->highs.getNumRow(), 0);
            imp->highs.changeColsCost(0, imp->highs.getNumCol() - 1, zero_col.data());
            imp->highs.changeRowsBounds(0, imp->highs.getNumRow() - 1, zero_row.data(), zero_row.data());

            // Add an extra constraint for the rhs so that b^Ty <= -1
            imp->highs.addRow(-imp->highs.getInfinity(), -1, num_nz, new_idx.data(), new_val.data());
        }
        else {
            //            std::cout << "Not inferring contradiction" << std::endl;
            // Solving {min b^Ty : A^Ty = c} (where c is the coefficients of the inference)
            auto norm_inference = variable_normalise(inference);
            vector<double> row_bounds(imp->highs.getNumRow(), 0);
            for (const auto & term : norm_inference.lhs.terms) {
                row_bounds[new_row_num[imp->var_number.at(term.variable)]] = (double)term.coefficient.raw_value;
            }
            imp->highs.changeRowsBounds(0, imp->highs.getNumRow() - 1, row_bounds.data(), row_bounds.data());
        }

        if (return_status != HighsStatus::kOk) {
            throw UnexpectedException{"Failed to create model for LP justification "};
        }
        const HighsLp & lp = imp->highs.getLp();

        if (optional_last_basis) {
            // Use the basis
            imp->highs.setBasis(*optional_current_basis);
        }

        // Now solve the model
        return_status = imp->highs.run();

        // Save the basis for next time
        optional_current_basis = imp->highs.getBasis();

        // Check it worked
        const HighsModelStatus & model_status = imp->highs.getModelStatus();
        const HighsInfo & info = imp->highs.getInfo();
        const bool has_values = info.primal_solution_status;
        if ((return_status != HighsStatus::kOk && model_status != HighsModelStatus::kOptimal)) {
            throw UnexpectedException{"Failed to correctly solve model for LP justification"};
        }

        const HighsSolution & solution = imp->highs.getSolution();

        optional_last_basis = imp->highs.getBasis(); // Store the basis for hot start next time

        // Turn the solution into a pol step
        stringstream p_line;
        p_line << "p ";
        long count = 0;
        for (int col = 0; col < lp.num_col_; col++) {
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
                    if (col > imp->cache_after)
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

        if (count >= 2) {
            // If there's only one constraint, no need to write a p line
            logger.emit_proof_comment("Computed LP justification 2:");
            auto line = logger.emit_proof_line(p_line.str(), ProofLevel::Current);
            std::cout << "";
        }
    };
}
