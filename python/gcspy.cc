#include <python/gcspy.hh>

#include <gcs/constraints/in.hh>
#include <iostream>
#include <optional>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

namespace py = pybind11;
using namespace gcs;

using std::cout;
using std::endl;
using std::string;
using std::to_string;

auto Python::create_integer_variable(const vector<long long int> & domain, const string & name) -> string
{
    vector<Integer> domain_i(domain.begin(), domain.end());
    auto var_id = p.create_integer_variable(domain_i, name);
    return map_new_id(var_id);
}

auto Python::create_integer_constant(const long long int & value) -> string
{
    auto constant_id = ConstantIntegerVariableID{Integer(value)};
    return map_new_id(constant_id);
}

auto Python::minimise(const string & var_id) -> void
{
    p.minimise(get_var(var_id));
}

auto Python::maximise(const string & var_id) -> void
{
    p.maximise(get_var(var_id));
}

auto Python::negate(const string & var_id) -> string
{
    auto var = get_var(var_id);
    return map_new_id(-var);
}

auto Python::add_constant(const string & var_id, long long int constant) -> string
{
    auto var = get_var(var_id);
    return map_new_id(var + Integer{constant});
}

auto Python::solve(bool all_solutions) -> std::unordered_map<string, unsigned long long int>
{
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                for (auto const & var : vars) {
                    solution_values[var.second] = s(var.second).raw_value;
                }
                return all_solutions; // Keep searching for solutions
            },
        });
    std::unordered_map<string, unsigned long long int> stats_map{};
    stats_map["recursions"] = stats.recursions;
    stats_map["failures"] = stats.failures;
    stats_map["propagations"] = stats.propagations;
    stats_map["effectful_propagations"] = stats.effectful_propagations;
    stats_map["contradicting_propagations"] = stats.contradicting_propagations;
    stats_map["solutions"] = stats.solutions;
    stats_map["max_depth"] = stats.max_depth;
    stats_map["n_propagators"] = stats.n_propagators;
    stats_map["solve_time"] = stats.solve_time.count();

    return stats_map;
}

auto Python::get_solution_value(const string & var_id) -> std::optional<long long int>
{
    try {
        auto sol_val = solution_values.at(get_var(var_id));
        return sol_val;
    }
    catch (const std::out_of_range & e) {
        return std::nullopt;
    }
}

auto Python::get_proof_filename() -> string
{
    return proof_filename;
}

auto Python::post_abs(const string & var_id_1, const string & var_id_2) -> void
{
    p.post(Abs(get_var(var_id_1), get_var(var_id_2)));
}

auto Python::post_arithmetic(const string & var_id_1, const string & var_id_2,
    const string & result_id, const string & op) -> void
{
    auto var1 = get_var(var_id_1);
    auto var2 = get_var(var_id_2);
    auto result = get_var(result_id);
    if (op == "sum") {
        try {
            p.post(Plus(var1, var2, result));
        }
        catch (const std::runtime_error & e) {
            cout << e.what() << endl;
        }
    }
    else if (op == "mul") {
        p.post(Times(var1, var2, result));
    }
    else if (op == "div") {
        p.post(Div(var1, var2, result));
    }
    else if (op == "mod") {
        p.post(Mod(var1, var2, result));
    }
    else if (op == "pow") {
        p.post(Power(var1, var2, result));
    }
    else {
        throw pybind11::value_error("Invalid arithmetic operator for Glasgow Constraint Solver: '" + op + "'");
    }
}

auto Python::post_alldifferent(const vector<std::string> & var_ids) -> void
{
    p.post(AllDifferent{get_vars(var_ids)});
}

auto Python::post_circuit(const vector<std::string> & var_ids) -> void
{
    p.post(Circuit{get_vars(var_ids)});
}

auto Python::post_less_than(const string & var_id_1, const string & var_id_2) -> void
{
    p.post(LessThan{get_var(var_id_1), get_var(var_id_2)});
}

auto Python::post_less_than_equal(const string & var_id_1, const string & var_id_2) -> void
{
    p.post(LessThanEqual{get_var(var_id_1), get_var(var_id_2)});
}

auto Python::post_greater_than(const string & var_id_1, const string & var_id_2) -> void
{
    p.post(GreaterThan{get_var(var_id_1), get_var(var_id_2)});
}

auto Python::post_greater_than_equal(const string & var_id_1, const string & var_id_2) -> void
{
    p.post(GreaterThanEqual{get_var(var_id_1), get_var(var_id_2)});
}

auto Python::post_less_than_if(const string & var_id_1, const string & var_id_2, const string & reif) -> void
{
    p.post(LessThanIf{get_var(var_id_1), get_var(var_id_2), get_var_as_cond(reif)});
}

auto Python::post_less_than_equal_if(const string & var_id_1, const string & var_id_2, const string & reif) -> void
{
    p.post(innards::CompareLessThanReif{get_var(var_id_1), get_var(var_id_2), get_var_as_cond(reif), false, true});
}

auto Python::post_greater_than_if(const string & var_id_1, const string & var_id_2, const string & reif) -> void
{
    p.post(innards::CompareLessThanReif{get_var(var_id_2), get_var(var_id_1), get_var_as_cond(reif), false, false});
}

auto Python::post_greater_than_equal_if(const string & var_id_1, const string & var_id_2, const string & reif) -> void
{
    p.post(innards::CompareLessThanReif{get_var(var_id_2), get_var(var_id_1), get_var_as_cond(reif), false, true});
}

auto Python::post_less_than_iff(const string & var_id_1, const string & var_id_2, const string & reif) -> void
{
    p.post(LessThanIff(get_var(var_id_1), get_var(var_id_2), get_var_as_cond(reif)));
}

auto Python::post_less_than_equal_iff(const string & var_id_1, const string & var_id_2, const string & reif) -> void
{
    p.post(LessThanEqualIff(get_var(var_id_1), get_var(var_id_2), get_var_as_cond(reif)));
}

auto Python::post_greater_than_iff(const string & var_id_1, const string & var_id_2, const string & reif) -> void
{
    p.post(GreaterThanIff(get_var(var_id_1), get_var(var_id_2), get_var_as_cond(reif)));
}

auto Python::post_greater_than_equal_iff(const string & var_id_1, const string & var_id_2, const string & reif) -> void
{
    p.post(GreaterThanEqualIff(get_var(var_id_1), get_var(var_id_2), get_var_as_cond(reif)));
}

auto Python::post_count(const vector<string> & var_ids, const string & var_id, const string & count_id)
    -> void
{
    p.post(Count(get_vars(var_ids), get_var(var_id), get_var(count_id)));
}

auto Python::post_element(const string & var_id, const string & index_id,
    const vector<string> & var_ids) -> void
{
    p.post(Element(get_var(var_id), get_var(index_id), get_vars(var_ids)));
}

auto Python::post_equals(const string & var_id_1, const string & var_id_2) -> void
{
    p.post(Equals(get_var(var_id_1), get_var(var_id_2)));
}

auto Python::post_equals_if(const string & var_id_1, const string & var_id_2, const string & reif_id) -> void
{
    p.post(EqualsIf(get_var(var_id_1), get_var(var_id_2), get_var(reif_id) != 0_i));
}

auto Python::post_equals_iff(const string & var_id_1, const string & var_id_2, const string & reif_id) -> void
{
    p.post(EqualsIff(get_var(var_id_1), get_var(var_id_2), get_var(reif_id) != 0_i));
}

auto Python::post_not_equals(const string & var_id_1, const string & var_id_2) -> void
{
    p.post(NotEquals(get_var(var_id_1), get_var(var_id_2)));
}

auto Python::post_in(const string & var_id, const vector<long long int> & domain) -> void
{
    vector<Integer> domain_i{};
    for (auto d : domain) {
        domain_i.emplace_back(d);
    }
    p.post(In(get_var(var_id), domain_i));
}

auto Python::post_in_vars(const string & var_id, const vector<string> & var_ids) -> void
{
    p.post(In(get_var(var_id), get_vars(var_ids)));
}

auto Python::post_linear_equality(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value) -> void
{
    p.post(LinearEquality{(make_linear(var_ids, coeffs)), Integer{value}});
}

auto Python::post_linear_equality_iff(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value, const string & reif) -> void
{
    p.post(LinearEqualityIff{(make_linear(var_ids, coeffs)), Integer{value}, get_var(reif) != 0_i});
}

auto Python::post_linear_less_equal(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value) -> void
{
    p.post(LinearLessEqual{(make_linear(var_ids, coeffs)), Integer{value}});
}

auto Python::post_linear_less_equal_iff(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value, const string & reif) -> void
{
    p.post(LinearLessEqualIff{(make_linear(var_ids, coeffs)), Integer{value}, get_var(reif) != 0_i});
}

auto Python::post_linear_greater_equal(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value) -> void
{
    p.post(LinearGreaterThanEqual{(make_linear(var_ids, coeffs)), Integer{value}});
}

auto Python::post_linear_greater_equal_iff(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value, const string & reif) -> void
{
    p.post(LinearLessEqualIff{(make_linear(var_ids, coeffs)), Integer{value}, get_var(reif) != 0_i});
}

auto Python::post_linear_not_equal(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value) -> void
{
    p.post(LinearNotEquals{(make_linear(var_ids, coeffs)), Integer{value}});
}

auto Python::post_and(const vector<string> & var_ids) -> void
{
    p.post(And{get_vars(var_ids)});
}

auto Python::post_and_if(const vector<string> & var_ids, const string & reif_id) -> void
{
    // Note: x => AND([vars]) is equivalent to x <=> AND([vars, x])
    auto new_vars = get_vars(var_ids);
    auto reif_var = get_var(reif_id);
    new_vars.push_back(reif_var);
    p.post(And{new_vars, reif_var});
}

auto Python::post_and_iff(const vector<string> & var_ids, const string & reif_id) -> void
{
    p.post(And{get_vars(var_ids), get_var(reif_id)});
}

auto Python::post_or(const vector<string> & var_ids) -> void
{
    p.post(Or{get_vars(var_ids)});
}

auto Python::post_or_if(const vector<string> & var_ids, const string & reif_id) -> void
{
    // Note: x => OR([vars]) is equivalent to OR([vars, 1 - x])
    auto new_vars = get_vars(var_ids);
    auto reif_var = -get_var(reif_id) + 1_i;
    new_vars.push_back(reif_var);
    p.post(Or{new_vars});
}

auto Python::post_or_iff(const vector<string> & var_ids, const string & reif_id) -> void
{
    p.post(Or{get_vars(var_ids), get_var(reif_id)});
}

auto Python::post_implies(const string & var_id_1, const string & var_id_2) -> void
{
    // Note: x => y is equivalent to OR([y, 1-x])
    auto var_1 = get_var(var_id_1);
    auto var_2 = get_var(var_id_2);
    p.post(Or{{var_2, -var_1 + 1_i}});
}

auto Python::post_implies_if(const string & var_id_1, const string & var_id_2, const string & reif_id) -> void
{
    // Note x => (a => b) is equivalent to OR([b, 1-a, 1-x])
    auto var_1 = get_var(var_id_1);
    auto var_2 = get_var(var_id_2);
    auto reif_var = get_var(reif_id);
    p.post(Or{{var_2, -var_1 + 1_i, -reif_var + 1_i}});
}

auto Python::post_implies_iff(const string & var_id_1, const string & var_id_2, const string & reif_id) -> void
{
    // x <=> (a => b) is equivalent to x => (a => b) and 1-x => (And([a, 1-b])
    post_implies_if(var_id_1, var_id_2, reif_id);
    p.post(And{{get_var(var_id_1), -get_var(var_id_2) + 1_i}, -get_var(reif_id) + 1_i});
}

auto Python::post_min(const vector<string> & var_ids, const string & var_id) -> void
{
    p.post(ArrayMin(get_vars(var_ids), get_var(var_id)));
}

auto Python::post_max(const vector<string> & var_ids, const string & var_id) -> void
{
    p.post(ArrayMax(get_vars(var_ids), get_var(var_id)));
}

auto Python::post_nvalue(const string & var_id, const vector<string> & var_ids) -> void
{
    p.post(NValue(get_var(var_id), get_vars(var_ids)));
}

auto Python::post_table(const vector<string> & var_id, const vector<vector<long long int>> & table) -> void
{
    SimpleTuples table_i;
    for (const auto & v : table) {
        vector<Integer> row{};
        row.reserve(v.size());
        for (auto vv : v) {
            row.emplace_back(vv);
        }
        table_i.push_back(row);
    }

    p.post(Table(get_vars(var_id), move(table_i)));
}

auto Python::post_negative_table(const vector<string> & var_id, const vector<vector<long long int>> & table) -> void
{
    SimpleTuples table_i;
    for (const auto & v : table) {
        vector<Integer> row{};
        row.reserve(v.size());
        for (auto vv : v) {
            row.emplace_back(vv);
        }
        table_i.push_back(row);
    }

    p.post(NegativeTable(get_vars(var_id), move(table_i)));
}

auto Python::post_inverse(const vector<string> & var_ids_1, const vector<string> & var_ids_2) -> void
{
    p.post(Inverse{get_vars(var_ids_1), get_vars(var_ids_2)});
}

auto Python::post_xor(const vector<std::string> & var_ids) -> void
{
    p.post(ParityOdd{get_vars(var_ids)});
}

/**
 * Python bindings: match the API exactly, using automatic STL conversion provided by Pybind11.
 */
PYBIND11_MODULE(gcspy, m)
{
    m.doc() = "Python bindings for the Glasgow Constraint Solver";
    py::class_<Python>(m, "GCS")
        .def(py::init<>())
        .def("create_integer_variable", &Python::create_integer_variable)
        .def("create_integer_constant", &Python::create_integer_constant)
        .def("maximise", &Python::maximise)
        .def("minimise", &Python::minimise)
        .def("negate", &Python::negate)
        .def("add_constant", &Python::add_constant)
        .def("solve", &Python::solve, py::arg("all_solutions") = true)

        .def("get_solution_value", &Python::get_solution_value)
        .def("get_proof_filename", &Python::get_proof_filename)

        // Constraints
        .def("post_abs", &Python::post_abs)
        .def("post_alldifferent", &Python::post_alldifferent)
        .def("post_arithmetic", &Python::post_arithmetic)
        .def("post_circuit", &Python::post_circuit)

        .def("post_less_than", &Python::post_less_than)
        .def("post_less_than_equal", &Python::post_less_than_equal)
        .def("post_greater_than", &Python::post_greater_than)
        .def("post_greater_than_equal", &Python::post_greater_than_equal)
        .def("post_less_than_if", &Python::post_less_than_if)
        .def("post_less_than_equal_if", &Python::post_less_than_equal_if)
        .def("post_greater_than_if", &Python::post_greater_than_if)
        .def("post_greater_than_equal_if", &Python::post_greater_than_equal_if)
        .def("post_less_than_iff", &Python::post_less_than_iff)
        .def("post_less_than_equal_iff", &Python::post_less_than_equal_iff)
        .def("post_greater_than_iff", &Python::post_greater_than_iff)
        .def("post_greater_than_equal_iff", &Python::post_greater_than_equal_iff)
        .def("post_equals", &Python::post_equals)
        .def("post_equals_if", &Python::post_equals_if)
        .def("post_equals_iff", &Python::post_equals_iff)

        .def("post_count", &Python::post_count)
        .def("post_element", &Python::post_element)

        .def("post_not_equals", &Python::post_not_equals)
        .def("post_in", &Python::post_in)
        .def("post_in_vars", &Python::post_in_vars)
        .def("post_linear_equality", &Python::post_linear_equality)
        .def("post_linear_equality_iff", &Python::post_linear_equality_iff)
        .def("post_linear_less_equal", &Python::post_linear_less_equal)
        .def("post_linear_greater_equal", &Python::post_linear_greater_equal)
        .def("post_linear_greater_equal_iff", &Python::post_linear_greater_equal_iff)
        .def("post_linear_not_equal", &Python::post_linear_not_equal)

        .def("post_and", &Python::post_and)
        .def("post_and_if", &Python::post_and_if)
        .def("post_and_iff", &Python::post_and_iff)
        .def("post_or", &Python::post_or)
        .def("post_or_if", &Python::post_or_if)
        .def("post_or_iff", &Python::post_or_iff)

        .def("post_implies", &Python::post_implies)
        .def("post_implies_if", &Python::post_implies_if)
        .def("post_implies_iff", &Python::post_implies_iff)

        .def("post_min", &Python::post_min)
        .def("post_max", &Python::post_max)
        .def("post_nvalue", &Python::post_nvalue)
        .def("post_table", &Python::post_table)
        .def("post_negative_table", &Python::post_negative_table)
        .def("post_inverse", &Python::post_inverse)
        .def("post_xor", &Python::post_xor);
}