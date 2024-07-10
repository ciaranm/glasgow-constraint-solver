

#ifndef GCS_API_HH
#define GCS_API_HH
#include <gcs/gcs.hh>
#include <pybind11/pybind11.h>
#include <string>
#include <unordered_map>
using namespace gcs;

using std::string;
using std::vector;

class Python
{
public:
    /**
     * gcs::Problem methods, simplified for pybind11.
     * Using long long int instead of gcs::Integer and std::string instead of gcs::VariableID.
     */
    auto create_integer_variable(const vector<long long int> & domain, const string & name) -> string;
    auto create_integer_constant(const long long int & value) -> string;
    auto minimise(const string &) -> void;
    auto maximise(const string &) -> void;

    /**
     * Allow for negation and translation of variables, wrapping around gcs::ViewOfIntegerVariableID
     */
    auto negate(const string & var_id) -> string;
    auto add_constant(const string & var_id, long long int constant) -> string;

    /**
     * Main solve method: no solution callbacks provided for simplicity - just enforce default
     * behaviour of looking for all solutions, then allow querying of solution values.
     */
    auto solve(bool all_solutions = true) -> std::unordered_map<string, unsigned long long int>; // Convert Stats struct to python dict via map
    auto get_solution_value(const string &) -> std::optional<long long int>;
    auto get_proof_filename() -> string;

    /**
     * Methods to post constraints: functional interface so we don't have to export all the constraint classes
     * to python.
     */

    // Arithmetic
    auto post_abs(const string & var_id_1, const string & var_id_2) -> void;
    auto post_arithmetic(const string & var_id_1, const string & var_id_2, const string & result_id, const string & op) -> void;

    // Comparisons
    auto post_equals(const string & var_id_1, const string & var_id_2) -> void;
    auto post_less_than(const string & var_id_1, const string & var_id_2) -> void;
    auto post_less_than_equal(const string & var_id_1, const string & var_id_2) -> void;
    auto post_greater_than(const string & var_id_1, const string & var_id_2) -> void;
    auto post_greater_than_equal(const string & var_id_1, const string & var_id_2) -> void;
    auto post_not_equals(const string & var_id_1, const string & var_id_2) -> void;
    // Half reified comparisons
    auto post_less_than_if(const string & var_id_1, const string & var_id_2, const string & reif) -> void;
    auto post_less_than_equal_if(const string & var_id_1, const string & var_id_2, const string & reif) -> void;
    auto post_greater_than_if(const string & var_id_1, const string & var_id_2, const string & reif) -> void;
    auto post_greater_than_equal_if(const string & var_id_1, const string & var_id_2, const string & reif) -> void;
    auto post_equals_if(const string & var_id_1, const string & var_id_2, const string & reif_id) -> void;
    // Fully reified comparisons
    auto post_less_than_iff(const string & var_id_1, const string & var_id_2, const string & reif) -> void;
    auto post_less_than_equal_iff(const string & var_id_1, const string & var_id_2, const string & reif) -> void;
    auto post_greater_than_iff(const string & var_id_1, const string & var_id_2, const string & reif) -> void;
    auto post_greater_than_equal_iff(const string & var_id_1, const string & var_id_2, const string & reif) -> void;
    auto post_count(const vector<string> & var_ids, const string & var_id, const string & count_id) -> void;
    auto post_equals_iff(const string & var_id_1, const string & var_id_2, const string & reif_id) -> void;

    // Linear
    auto post_linear_equality(const vector<string> & var_ids, const vector<long long int> & coeffs, long long int value) -> void;
    auto post_linear_equality_iff(const vector<string> & var_ids, const vector<long long int> & coeffs, long long int value, const string & reif) -> void;
    auto post_linear_less_equal(const vector<string> & var_ids, const vector<long long int> & coeffs, long long int value) -> void;
    auto post_linear_less_equal_iff(const vector<string> & var_ids, const vector<long long int> & coeffs, long long int value, const string & reif) -> void;
    auto post_linear_greater_equal(const vector<string> & var_ids, const vector<long long int> & coeffs, long long int value) -> void;
    auto post_linear_greater_equal_iff(const vector<string> & var_ids, const vector<long long int> & coeffs, long long int value, const string & reif) -> void;
    auto post_linear_not_equal(const vector<string> & var_ids, const vector<long long int> & coeffs, long long int value) -> void;

    // Logical
    auto post_and(const vector<string> & var_ids) -> void;
    auto post_and_if(const vector<string> & var_ids, const string & reif_id) -> void;
    auto post_and_iff(const vector<string> & var_ids, const string & reif_id) -> void;
    auto post_or(const vector<string> & var_ids) -> void;
    auto post_or_if(const vector<string> & var_ids, const string & reif_id) -> void;
    auto post_or_iff(const vector<string> & var_ids, const string & reif_id) -> void;

    auto post_implies(const string & var_id_1, const string & var_id_2) -> void;
    auto post_implies_if(const string & var_id_1, const string & var_id_2, const string & reif_id) -> void;
    auto post_implies_iff(const string & var_id_1, const string & var_id_2, const string & reif_id) -> void;

    // Globals
    auto post_alldifferent(const vector<string> & var_ids) -> void;
    auto post_circuit(const vector<string> & var_ids) -> void;
    auto post_min(const vector<string> & var_ids, const string & var_id) -> void;
    auto post_max(const vector<string> & var_ids, const string & var_id) -> void;
    auto post_nvalue(const string & var_id, const vector<string> & var_ids) -> void;
    auto post_table(const vector<string> & var_id, const vector<vector<long long int>> & table) -> void;
    auto post_negative_table(const vector<string> & var_id, const vector<vector<long long int>> & table) -> void;
    auto post_inverse(const vector<string> & var_ids_1, const vector<string> & var_ids_2) -> void;
    auto post_element(const string & var_id, const string & index_id, const vector<string> & var_ids) -> void;
    auto post_xor(const vector<string> & var_ids) -> void;
    auto post_in(const string & var_id, const vector<long long int> & domain) -> void;
    auto post_in_vars(const string & var_id, const vector<string> & var_ids) -> void;

private:
    const string proof_filename = "gcs_proof";
    Problem p{};
    // Python will use string ids to keep track of variables
    std::unordered_map<string, IntegerVariableID> vars{};
    // raw_value in gcs::Integer is a long long int
    std::unordered_map<IntegerVariableID, long long int> solution_values{};
    unsigned long long id_count{};

    /**
     * Private helper methods to deal with the var map.
     */
    auto map_new_id(IntegerVariableID var_id) -> string
    {
        auto str_id = std::to_string(id_count++);
        vars.insert({str_id, var_id});
        return str_id;
    }

    IntegerVariableID get_var(const string & var_id)
    {
        try {
            auto var = vars.at(var_id);
            return var;
        }
        catch (const std::out_of_range & e) {
            throw pybind11::key_error("Variable ID '" + var_id + "' not known to the Glasgow Constraint Solver.");
        }
    }

    IntegerVariableCondition get_var_as_cond(const string & var_id)
    {
        try {
            auto var = vars.at(var_id);
            return var == 1_i;
        }
        catch (const std::out_of_range & e) {
            throw pybind11::key_error("Variable ID '" + var_id + "' not known to the Glasgow Constraint Solver.");
        }
    }

    vector<IntegerVariableID> get_vars(const vector<string> & var_ids)
    {
        vector<IntegerVariableID> selected_vars{};
        for (const string & id : var_ids) {
            selected_vars.push_back(get_var(id));
        }
        return selected_vars;
    }

    WeightedSum make_linear(const vector<string> & var_ids, const vector<long long int> & coeffs)
    {
        if (var_ids.size() != coeffs.size()) {
            throw pybind11::value_error("Invalid arguments for Glasgow Constraint Solver post_linear_equality: must have same number of coefficients and variables.");
        }

        WeightedSum summands{};
        for (unsigned int i = 0; i < coeffs.size(); i++) {
            summands += Integer{coeffs[i]} * vars.at(var_ids[i]);
        }
        return summands;
    }
};

#endif