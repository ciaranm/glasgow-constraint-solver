#include <Highs.h>
#include <iomanip>
#include <iostream>
#include <utility>

using std::cout;
using std::endl;
using std::move;
using std::tuple;

auto print_matrix(HighsSparseMatrix matr) -> void
{
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
            cout << std::setw(2) << elem << " ";
        }
        cout << "\n";
    }
}

auto main(int argc, char * argv[]) -> int
{

    HighsModel model;
    Highs highs;

    model.lp_.num_row_ = 8;
    model.lp_.num_col_ = 36;
    model.lp_.a_matrix_.format_ = MatrixFormat::kColwise;
    model.lp_.sense_ = ObjSense::kMinimize;

    model.lp_.a_matrix_.start_ = {0, 1, 2, 2, 2, 2, 2, 3, 4, 4, 4, 5, 6, 7, 8, 10, 12, 12, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 24, 25, 26, 28, 30, 33, 36, 39, 42};
    model.lp_.a_matrix_.index_ = {0, 0, 0, 0, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 4, 4, 3, 4, 3, 4, 5, 5, 6, 6, 7, 7, 0, 5, 0, 5, 1, 3, 6, 1, 3, 6, 2, 4, 7, 2, 4, 7};
    model.lp_.a_matrix_.value_ = {1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, -1, 1, -1, 1, -1, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1, 1, -1, -1, -1, 1, 1, 1, -1};
    model.lp_.setMatrixDimensions();

    model.lp_.row_lower_ = {0, 0, 0, 1, 0, 0, 0, 0};
    model.lp_.row_upper_ = {0, 0, 0, 1, 0, 0, 0, 0};
    model.lp_.col_cost_ = {1, 0, 1, 0, 1, 0, 1, -1, 1, 0, 1, 0, 1, 0, 1, -1, 1, 0, 1, 0, 1, 0, 1, -1, 1, -1, 2, -0, 2, -0, 0, 0, 0, 0, 0, 0};
    model.lp_.col_lower_ = vector<double>(model.lp_.num_col_, 0);
    model.lp_.col_upper_ = vector<double>(model.lp_.num_col_, 50);

    highs.passModel(model);
    print_matrix(model.lp_.a_matrix_);
    HighsStatus return_status;

    // Pass the model to HiGHS
    return_status = highs.passModel(model);
    assert(return_status == HighsStatus::kOk);

    // Get a const reference to the LP data in HiGHS
    const HighsLp & lp = highs.getLp();

    // Solve the model
    return_status = highs.run();
    assert(return_status == HighsStatus::kOk);

    const HighsInfo & info = highs.getInfo();
    cout << "Simplex iteration count: " << info.simplex_iteration_count << endl;
    cout << "Objective function value: " << info.objective_function_value << endl;
    cout << "Primal  solution status: " << highs.solutionStatusToString(info.primal_solution_status) << endl;
    cout << "Dual    solution status: " << highs.solutionStatusToString(info.dual_solution_status) << endl;
    cout << "Basis: " << highs.basisValidityToString(info.basis_validity) << endl;

    auto solution = highs.getSolution();

    for (unsigned i = 0; i < solution.col_value.size(); i++) {
        cout << std::setw(3) << i;
    }
    cout << endl;
    for (const auto & val : solution.col_value) {
        cout << std::setw(3) << val;
    }
    cout << endl;
}
