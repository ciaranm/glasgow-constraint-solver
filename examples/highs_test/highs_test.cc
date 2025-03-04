#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <iostream>
#include <string>

#include <Highs.h>
#include <boost/program_options.hpp>
#include <iomanip>
#include <utility>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

namespace po = boost::program_options;

using std::cout;
using std::endl;
using std::transform;

auto negate_matrix(vector<vector<double>> A)
{
    vector<vector<double>> neg{};
    for (const auto & row : A) {
        neg.emplace_back();
        for (const auto & val : row) {
            neg.back().emplace_back(-val);
        }
    }
    return neg;
}

auto transpose_matrix(vector<vector<double>> A)
{
    vector<vector<double>> transp(A[0].size(), vector<double>(A.size()));
    for (unsigned int i = 0; i < A.size(); i++) {
        for (unsigned int j = 0; j < A[0].size(); j++) {
            transp[j][i] = A[i][j];
        }
    }
    return transp;
}
int main()
{
    // Create and populate a HighsModel instance for the LP
    //
    // Min    f  =  x_0 +  x_1 + 3
    // s.t.                x_1 <= 7
    //        5 <=  x_0 + 2x_1 <= 15
    //        6 <= 3x_0 + 2x_1
    // 0 <= x_0 <= 4; 1 <= x_1
    //
    // Although the first constraint could be expressed as an upper
    // bound on x_1, it serves to illustrate a non-trivial packed
    // column-wise matrix.
    //

    vector<vector<double>> basic_matrix = {
        {1, 0, 1, 0, 1, 0},
        {0, 1, 0, 1, 0, 1},
        {1, 1, 0, 0, 0, 0},
        {0, 0, 1, 1, 0, 0},
        {0, 0, 0, 0, 1, 1}};

    vector<vector<double>> identity = {
        {1, 0, 0, 0, 0, 0},
        {0, 1, 0, 0, 0, 0},
        {0, 0, 1, 0, 0, 0},
        {0, 0, 0, 1, 0, 0},
        {0, 0, 0, 0, 1, 0},
        {0, 0, 0, 0, 0, 1}};

    basic_matrix.insert(basic_matrix.end(), identity.begin(), identity.end());

    vector<vector<double>> negated_matrix = negate_matrix(basic_matrix);
    vector<vector<double>> full_matrix(basic_matrix.begin(), basic_matrix.end());
    full_matrix.insert(full_matrix.end(), negated_matrix.begin(), negated_matrix.end());

    auto dual_matrix = transpose_matrix(full_matrix);

    vector<double> obj_row(basic_matrix.size(), 1.0);
    obj_row.insert(obj_row.end(), basic_matrix.size() - identity.size(), -1.0);
    obj_row.insert(obj_row.end(), identity.size(), 0.0);

    dual_matrix.emplace_back(obj_row); // Add one more row of all 1s

    // Create a Highs instance
    Highs highs;

    HighsModel model;
    model.lp_.num_col_ = int(dual_matrix[0].size());
    model.lp_.num_row_ = int(dual_matrix.size());
    model.lp_.sense_ = ObjSense::kMinimize;
    model.lp_.offset_ = 0;

    model.lp_.col_cost_ = vector<double>(model.lp_.num_col_, 0.0);
    model.lp_.col_upper_ = vector<double>(model.lp_.num_col_, highs.getInfinity());
    model.lp_.col_lower_ = vector<double>(model.lp_.num_col_, 0.0);

    vector<double> row_bound(model.lp_.num_row_, 0.0);
    row_bound.back() = -highs.getInfinity();

    model.lp_.row_lower_ = row_bound;

    cout << "row lower:";
    for (const auto & r : row_bound)
        cout << r << " ";
    cout << endl;

    row_bound.back() = -1.0;

    model.lp_.row_upper_ = row_bound;

    cout << "row upper:";
    for (const auto & r : row_bound)
        cout << r << " ";
    cout << endl;

    // Here the orientation of the matrix is column-wise
    model.lp_.a_matrix_.format_ = MatrixFormat::kRowwise;
    // a_start_ has num_col_1 entries, and the last entry is the number
    // of nonzeros in A, allowing the number of nonzeros in the last
    // column to be defined
    vector<int> starts;
    vector<int> indices;
    vector<double> values;
    int non_zeros = 0;

    for (const auto & row : dual_matrix) {
        starts.emplace_back(non_zeros);
        auto col_count = 0;
        for (const auto & val : row) {
            if (val != 0.0) {
                non_zeros++;
                indices.emplace_back(col_count);
                values.emplace_back(val);
            }
            col_count++;
        }
    }
    starts.emplace_back(non_zeros);
    for (const auto & s : starts)
        cout << s << " ";
    cout << endl;
    for (const auto & s : indices)
        cout << s << " ";
    cout << endl;
    for (const auto & s : values)
        cout << s << " ";
    cout << endl;
    model.lp_.a_matrix_.start_ = starts;
    model.lp_.a_matrix_.index_ = indices;
    model.lp_.a_matrix_.value_ = values;

    int numRows = starts.size() - 1;

    // Find the number of columns (max value in indices + 1)
    int numCols = 0;
    for (int idx : indices) {
        if (idx > numCols) {
            numCols = idx;
        }
    }
    numCols += 1;

    // Print the sparse matrix in full format
    for (int i = 0; i < numRows; ++i) {
        int rowStart = starts[i];
        int rowEnd = starts[i + 1];

        // Create a row of zeroes
        std::vector<int> row(numCols, 0);

        // Fill in the non-zero values for the current row
        for (int j = rowStart; j < rowEnd; ++j) {
            row[indices[j]] = values[j];
        }

        // Print the row
        for (int val : row) {
            std::cout << std::setw(4) << val; // Format output for alignment
        }
        std::cout << std::endl;
    }

    HighsModel newModel = model; // copy ?

    HighsStatus return_status;
    //
    // Pass the model to HiGHS
    return_status = highs.passModel(newModel);
    assert(return_status == HighsStatus::kOk);
    // If a user passes a model with entries in
    // model.lp_.a_matrix_.value_ less than (the option)
    // small_matrix_value in magnitude, they will be ignored. A logging
    // message will indicate this, and passModel will return
    // HighsStatus::kWarning
    //
    // Get a const reference to the LP data in HiGHS
    const HighsLp & lp = highs.getLp();
    //
    // Solve the model
    return_status = highs.run();
    assert(return_status == HighsStatus::kOk);
    //
    // Get the model status
    const HighsModelStatus & model_status = highs.getModelStatus();
    assert(model_status == HighsModelStatus::kOptimal);
    cout << "Model status: " << highs.modelStatusToString(model_status) << endl;
    //
    // Get the solution information
    const HighsInfo & info = highs.getInfo();
    //    cout << "Simplex iteration count: " << info.simplex_iteration_count << endl;
    //    cout << "Objective function value: " << info.objective_function_value << endl;
    //    cout << "Primal  solution status: "
    //         << highs.solutionStatusToString(info.primal_solution_status) << endl;
    //    cout << "Dual    solution status: "
    //         << highs.solutionStatusToString(info.dual_solution_status) << endl;
    //    cout << "Basis: " << highs.basisValidityToString(info.basis_validity) << endl;
    const bool has_values = info.primal_solution_status;
    const bool has_duals = info.dual_solution_status;
    const bool has_basis = info.basis_validity;
    //    //
    // Get the solution values and basis
    const HighsSolution & solution = highs.getSolution();
    const HighsBasis & basis = highs.getBasis();
    //
    // Report the primal and solution values and basis
    for (int col = 0; col < lp.num_col_; col++) {
        cout << "Column " << col;
        if (has_values) cout << "; value = " << solution.col_value[col];
        if (has_duals) cout << "; dual = " << solution.col_dual[col];
        if (has_basis)
            cout << "; status: " << highs.basisStatusToString(basis.col_status[col]);
        cout << endl;
    }
    for (int row = 0; row < lp.num_row_; row++) {
        cout << "Row    " << row;
        if (has_values) cout << "; value = " << solution.row_value[row];
        if (has_duals) cout << "; dual = " << solution.row_dual[row];
        if (has_basis)
            cout << "; status: " << highs.basisStatusToString(basis.row_status[row]);
        cout << endl;
    }
    //
    //    // Now indicate that all the variables must take integer values
    //    model.lp_.integrality_.resize(lp.num_col_);
    //    for (int col = 0; col < lp.num_col_; col++)
    //        model.lp_.integrality_[col] = HighsVarType::kInteger;
    //
    //    highs.passModel(model);
    //    // Solve the model
    //    return_status = highs.run();
    //    assert(return_status == HighsStatus::kOk);
    //    // Report the primal solution values
    //    for (int col = 0; col < lp.num_col_; col++) {
    //        cout << "Column " << col;
    //        if (info.primal_solution_status)
    //            cout << "; value = " << solution.col_value[col];
    //        cout << endl;
    //    }
    //    for (int row = 0; row < lp.num_row_; row++) {
    //        cout << "Row    " << row;
    //        if (info.primal_solution_status)
    //            cout << "; value = " << solution.row_value[row];
    //        cout << endl;
    //    }

    return EXIT_SUCCESS;
}
