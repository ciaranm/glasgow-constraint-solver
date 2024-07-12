#include <chrono>
#include <condition_variable>
#include <gcs/constraints/in.hh>
#include <iostream>
#include <mutex>
#include <optional>
#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <python/gcspy.hh>
#include <signal.h>
#include <thread>

namespace py = pybind11;
using namespace gcs;

using std::atomic;
using std::cerr;
using std::condition_variable;
using std::cout;
using std::cv_status;
using std::endl;
using std::exception;
using std::function;
using std::mutex;
using std::nullopt;
using std::optional;
using std::string;
using std::thread;
using std::to_string;
using std::unique_lock;
using std::chrono::milliseconds;
using std::chrono::seconds;
using std::chrono::system_clock;

static atomic<bool> abort_flag{false}, was_terminated{false};

auto sig_int_or_term_handler(int) -> void
{
    abort_flag.store(true);
    was_terminated.store(true);
}

auto Python::create_integer_variable(const long long lower, const long long upper, const string & name) -> string
{
    auto var_id = p.create_integer_variable(Integer{lower}, Integer{upper}, name);
    auto str_id = map_new_id(var_id);
#ifdef WRITE_API_CALLS
    cout << "auto v" << str_id << " = p.create_integer_variable(" << lower << "_i, " << upper << "_i);" << endl;
#endif
    return str_id;
}

auto Python::create_integer_constant(const long long int & value) -> string
{
    auto constant_id = ConstantIntegerVariableID{Integer(value)};
    auto str_id = map_new_id(constant_id);
#ifdef WRITE_API_CALLS
    cout << "auto v" << str_id << " = ConstantIntegerVariableID{Integer(" << value << ")};" << endl;
#endif
    return str_id;
}

auto Python::minimise(const string & var_id) -> void
{
#ifdef WRITE_API_CALLS
    cout << "minimise" << endl;
#endif
    p.minimise(get_var(var_id));
}

auto Python::maximise(const string & var_id) -> void
{
#ifdef WRITE_API_CALLS
    cout << "maximise" << endl;
#endif
    p.maximise(get_var(var_id));
}

auto Python::negate(const string & var_id) -> string
{
#ifdef WRITE_API_CALLS
    cout << "negate" << endl;
#endif
    auto var = get_var(var_id);
    return map_new_id(-var);
}

auto Python::add_constant(const string & var_id, long long int constant) -> string
{
#ifdef WRITE_API_CALLS
    cout << "add_constant" << endl;
#endif
    auto var = get_var(var_id);
    return map_new_id(var + Integer{constant});
}

auto Python::solve(bool all_solutions,
    optional<unsigned long long> timeout,
    optional<unsigned long long> solution_limit,
    const optional<function<void(std::unordered_map<string, long long int>)>> & callback,
    bool prove,
    const optional<string> & proof_name,
    const optional<string> & proof_location)
    -> std::unordered_map<string, unsigned long long int>
{
#ifdef WRITE_API_CALLS
    cout << "solve" << endl;
#endif
    signal(SIGINT, &sig_int_or_term_handler);
    signal(SIGTERM, &sig_int_or_term_handler);

    thread timeout_thread;
    mutex timeout_mutex;
    condition_variable timeout_cv;
    bool actually_timed_out = false;
    bool completed = false;

    if (timeout) {
        milliseconds limit{timeout.value() * 1000};
        timeout_thread = thread([limit = limit, &timeout_mutex, &timeout_cv, &actually_timed_out] {
            auto abort_time = system_clock::now() + limit;
            {
                /* Sleep until either we've reached the time limit,
                 * or we've finished all the work. */
                unique_lock<mutex> guard(timeout_mutex);
                while (! abort_flag.load()) {
                    if (cv_status::timeout == timeout_cv.wait_until(guard, abort_time)) {
                        /* We've woken up, and it's due to a timeout. */
                        actually_timed_out = true;
                        break;
                    }
                }
            }
            abort_flag.store(true);
        });
    }

    if (prove) {
        if (! proof_name)
            throw pybind11::value_error("Glasgow Constraint Solver: prove is true but no proof_name provided");
        if (! proof_location)
            throw pybind11::value_error("Glasgow Constraint Solver: prove is true but no proof_location provided");
    }

    try {
        auto stats = solve_with(
            p,
            SolveCallbacks{
                .solution = [&](const CurrentState & s) -> bool {
                    solution_values.emplace_back();
                    id_solution_values.emplace_back();
                    for (auto const & var : vars) {
                        solution_values.back()[var.second] = s(var.second).raw_value;
                        id_solution_values.back()[var.first] = s(var.second).raw_value;
                    }
                    if (callback) {
                        (*callback)(id_solution_values.back());
                    }
                    if (solution_limit) {
                        if (--*solution_limit == 0) {
                            return false;
                        }
                    }
                    return all_solutions; // Keep searching for solutions if all solutions
                },
                .completed = [&] { completed = true; }},
            prove ? make_optional<ProofOptions>(*proof_location + "/" + *proof_name + ".opb", *proof_location + "/" + *proof_name + ".pbp") : nullopt,
            &abort_flag);

        if (timeout_thread.joinable()) {
            {
                unique_lock<mutex> guard(timeout_mutex);
                abort_flag.store(true);
                timeout_cv.notify_all();
            }
            timeout_thread.join();
        }

        std::unordered_map<string, unsigned long long int> stats_map{};
        stats_map["recursions"] = stats.recursions;
        stats_map["failures"] = stats.failures;
        stats_map["propagations"] = stats.propagations;
        stats_map["effectful_propagations"] = stats.effectful_propagations;
        stats_map["contradicting_propagations"] = stats.contradicting_propagations;
        stats_map["solutions"] = stats.solutions;
        stats_map["max_depth"] = stats.max_depth;
        stats_map["n_propagators"] = stats.n_propagators;
        stats_map["solve_time"] = stats.solve_time.count() / 1'000'000.0;
        stats_map["completed"] = completed;

        return stats_map;
    }
    catch (const exception & e) {
        fmt::println(cerr, "gcs: error: {}", e.what());

        if (timeout_thread.joinable()) {
            {
                unique_lock<mutex> guard(timeout_mutex);
                abort_flag.store(true);
                timeout_cv.notify_all();
            }
            timeout_thread.join();
        }
        return std::unordered_map<string, unsigned long long int>{};
    }
}

auto Python::get_solution_value(const string & var_id, const unsigned long long solution_number = 0) -> std::optional<long long int>
{
#ifdef WRITE_API_CALLS
    cout << "get_solution_value" << endl;
#endif
    try {
        auto sol_val = solution_values[solution_number].at(get_var(var_id));
        return sol_val;
    }
    catch (const std::out_of_range & e) {
        return std::nullopt;
    }
}

auto Python::get_proof_filename() -> string
{
#ifdef WRITE_API_CALLS
    cout << "get_proof_filename" << endl;
#endif
    return proof_filename;
}

auto Python::post_abs(const string & var_id_1, const string & var_id_2) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_abs" << endl;
#endif
    p.post(Abs(get_var(var_id_1), get_var(var_id_2)));
}

auto Python::post_arithmetic(const string & var_id_1, const string & var_id_2,
    const string & result_id, const string & op)
    -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_arithmetic" << endl;
#endif
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
#ifdef WRITE_API_CALLS
    cout << "p.post(AllDifferent{{";
    for (size_t i = 0; i < var_ids.size() - 1; ++i)
        cout << "v" << var_ids[i] << ", ";
    cout << "v" << var_ids.back() << "}gi});" << endl;
#endif
    p.post(AllDifferent{get_vars(var_ids)});
}

auto Python::post_circuit(const vector<std::string> & var_ids) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_circuit" << endl;
#endif
    p.post(Circuit{get_vars(var_ids)});
}

auto Python::post_less_than(const string & var_id_1, const string & var_id_2) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_less_than" << endl;
#endif
    p.post(LessThan{get_var(var_id_1), get_var(var_id_2)});
}

auto Python::post_less_than_equal(const string & var_id_1, const string & var_id_2) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_less_than_equal" << endl;
#endif
    p.post(LessThanEqual{get_var(var_id_1), get_var(var_id_2)});
}

auto Python::post_greater_than(const string & var_id_1, const string & var_id_2) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_greater_than" << endl;
#endif
    p.post(GreaterThan{get_var(var_id_1), get_var(var_id_2)});
}

auto Python::post_greater_than_equal(const string & var_id_1, const string & var_id_2) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_greater_than_equal" << endl;
#endif
    p.post(GreaterThanEqual{get_var(var_id_1), get_var(var_id_2)});
}

auto Python::post_less_than_reif(const string & var_id_1, const string & var_id_2, const string & reif, bool fully_reify) -> void
{
    if (fully_reify) {
#ifdef WRITE_API_CALLS
        cout << "p.post(LessThanIff{v" << var_id_1 << ", "
             << "v" << var_id_2 << ", v" << reif << " != 0_i"
             << "});" << endl;
#endif
        p.post(LessThanIff{get_var(var_id_1), get_var(var_id_2), get_var_as_cond(reif)});
    }
    else {
#ifdef WRITE_API_CALLS
        cout << "p.post(LessThanIf{v" << var_id_1 << ", "
             << "v" << var_id_2 << ", v" << reif << " != 0_i"
             << "});" << endl;
#endif
        p.post(LessThanIf{get_var(var_id_1), get_var(var_id_2), get_var_as_cond(reif)});
    }
}

auto Python::post_less_than_equal_reif(const string & var_id_1, const string & var_id_2, const string & reif, bool fully_reif) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_less_than_equal_reif" << endl;
#endif
    if (fully_reif)
        p.post(LessThanEqualIff{get_var(var_id_1), get_var(var_id_2), get_var_as_cond(reif)});
    else
        p.post(innards::CompareLessThanReif{get_var(var_id_1), get_var(var_id_2), get_var_as_cond(reif), false, true});
}

auto Python::post_greater_than_reif(const string & var_id_1, const string & var_id_2, const string & reif, bool fully_reify) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_greater_than_reif" << endl;
#endif
    if (fully_reify)
        p.post(GreaterThanIff(get_var(var_id_1), get_var(var_id_2), get_var_as_cond(reif)));
    else
        p.post(innards::CompareLessThanReif{get_var(var_id_2), get_var(var_id_1), get_var_as_cond(reif), false, false});
}

auto Python::post_greater_than_equal_reif(const string & var_id_1, const string & var_id_2, const string & reif, bool fully_reify) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_greater_than_equal_reif" << endl;
#endif
    if (fully_reify)
        p.post(GreaterThanEqualIff(get_var(var_id_1), get_var(var_id_2), get_var_as_cond(reif)));
    else
        p.post(innards::CompareLessThanReif{get_var(var_id_2), get_var(var_id_1), get_var_as_cond(reif), false, true});
}

auto Python::post_count(const vector<string> & var_ids, const string & var_id, const string & count_id)
    -> void
{
    p.post(Count(get_vars(var_ids), get_var(var_id), get_var(count_id)));
}

auto Python::post_element(const string & var_id, const string & index_id,
    const vector<string> & var_ids)
    -> void
{
    p.post(Element(get_var(var_id), get_var(index_id), get_vars(var_ids)));
}

auto Python::post_equals(const string & var_id_1, const string & var_id_2) -> void
{
#ifdef WRITE_API_CALLS
    cout << "p.post(Equals(v" << var_id_1 << ", v" << var_id_2 << ");" << endl;
#endif
    p.post(Equals(get_var(var_id_1), get_var(var_id_2)));
}

auto Python::post_equals_reif(const string & var_id_1, const string & var_id_2, const string & reif_id, bool fully_reif) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_equals_reif" << endl;
#endif
    if (fully_reif)
        p.post(EqualsIff(get_var(var_id_1), get_var(var_id_2), get_var(reif_id) != 0_i));
    else
        p.post(EqualsIf(get_var(var_id_1), get_var(var_id_2), get_var(reif_id) != 0_i));
}

auto Python::post_not_equals(const string & var_id_1, const string & var_id_2) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_not_equals" << endl;
#endif
    p.post(NotEquals(get_var(var_id_1), get_var(var_id_2)));
}

auto Python::post_in(const string & var_id, const vector<long long int> & domain) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_in" << endl;
#endif
    vector<Integer> domain_i{};
    for (auto d : domain) {
        domain_i.emplace_back(d);
    }
    p.post(In(get_var(var_id), domain_i));
}

auto Python::post_in_vars(const string & var_id, const vector<string> & var_ids) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_in_vars" << endl;
#endif
    p.post(In(get_var(var_id), get_vars(var_ids)));
}

auto Python::post_linear_equality(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value)
    -> void
{
#ifdef WRITE_API_CALLS
    cout << "p.post(LinearEquality{WeightedSum{}";
    for (size_t i = 0; i < var_ids.size(); ++i)
        cout << " + " << coeffs[i] << "_i * "
             << "v" << var_ids[i];
    cout << ", " << value << "_i"
         << "});" << endl;
#endif
    p.post(LinearEquality{(make_linear(var_ids, coeffs)), Integer{value}});
}

auto Python::post_linear_equality_iff(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value, const string & reif)
    -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_linear_equality_iff" << endl;
#endif
    p.post(LinearEqualityIff{(make_linear(var_ids, coeffs)), Integer{value}, get_var(reif) != 0_i});
}

auto Python::post_linear_less_equal(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value)
    -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_linear_less_equal" << endl;
#endif
    p.post(LinearLessEqual{(make_linear(var_ids, coeffs)), Integer{value}});
}

auto Python::post_linear_less_equal_iff(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value, const string & reif)
    -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_linear_less_equal_iff" << endl;
#endif
    p.post(LinearLessEqualIff{(make_linear(var_ids, coeffs)), Integer{value}, get_var(reif) != 0_i});
}

auto Python::post_linear_greater_equal(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value)
    -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_linear_greater_equal" << endl;
#endif
    p.post(LinearGreaterThanEqual{(make_linear(var_ids, coeffs)), Integer{value}});
}

auto Python::post_linear_greater_equal_iff(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value, const string & reif)
    -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_linear_greater_equal_iff" << endl;
#endif
    p.post(LinearLessEqualIff{(make_linear(var_ids, coeffs)), Integer{value}, get_var(reif) != 0_i});
}

auto Python::post_linear_not_equal(const vector<string> & var_ids, const vector<long long int> & coeffs,
    long long int value)
    -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_linear_not_equal" << endl;
#endif
    p.post(LinearNotEquals{(make_linear(var_ids, coeffs)), Integer{value}});
}

auto Python::post_and(const vector<string> & var_ids) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_and" << endl;
#endif
    p.post(And{get_vars(var_ids)});
}

auto Python::post_and_reif(const vector<string> & var_ids, const string & reif_id, bool fully_reify) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_and_reif" << endl;
#endif
    if (fully_reify)
        p.post(And{get_vars(var_ids), get_var(reif_id)});
    else {
        // Note: x => AND([vars]) is equivalent to x <=> AND([vars, x])
        auto new_vars = get_vars(var_ids);
        auto reif_var = get_var(reif_id);
        new_vars.push_back(reif_var);
        p.post(And{new_vars, reif_var});
    }
}

auto Python::post_or(const vector<string> & var_ids) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_or" << endl;
#endif
    p.post(Or{get_vars(var_ids)});
}

auto Python::post_or_reif(const vector<string> & var_ids, const string & reif_id, bool fully_reify) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_or_reif" << endl;
#endif
    if (fully_reify)
        p.post(Or{get_vars(var_ids), get_var(reif_id)});
    else {
        // Note: x => OR([vars]) is equivalent to OR([vars, 1 - x])
        auto new_vars = get_vars(var_ids);
        auto reif_var = -get_var(reif_id) + 1_i;
        new_vars.push_back(reif_var);
        p.post(Or{new_vars});
    }
}

auto Python::post_implies(const string & var_id_1, const string & var_id_2) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_implies" << endl;
#endif
    // Note: x => y is equivalent to OR([y, 1-x])
    auto var_1 = get_var(var_id_1);
    auto var_2 = get_var(var_id_2);
    p.post(Or{{var_2, -var_1 + 1_i}});
}

auto Python::post_implies_reif(const string & var_id_1, const string & var_id_2, const string & reif_id, bool fully_reify) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_implies_reif" << endl;
#endif
    // Note x => (a => b) is equivalent to OR([b, 1-a, 1-x])
    auto var_1 = get_var(var_id_1);
    auto var_2 = get_var(var_id_2);
    auto reif_var = get_var(reif_id);
    p.post(Or{{var_2, -var_1 + 1_i, -reif_var + 1_i}});
    if (fully_reify)
        p.post(And{{get_var(var_id_1), -get_var(var_id_2) + 1_i}, -get_var(reif_id) + 1_i});
}

auto Python::post_min(const vector<string> & var_ids, const string & var_id) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_min" << endl;
#endif
    p.post(ArrayMin(get_vars(var_ids), get_var(var_id)));
}

auto Python::post_max(const vector<string> & var_ids, const string & var_id) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_max" << endl;
#endif
    p.post(ArrayMax(get_vars(var_ids), get_var(var_id)));
}

auto Python::post_nvalue(const string & var_id, const vector<string> & var_ids) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_nvalue" << endl;
#endif
    p.post(NValue(get_var(var_id), get_vars(var_ids)));
}

auto Python::post_table(const vector<string> & var_id, const vector<vector<long long int>> & table) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_table" << endl;
#endif
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
#ifdef WRITE_API_CALLS
    cout << "post_negative_table" << endl;
#endif
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
#ifdef WRITE_API_CALLS
    cout << "post_inverse" << endl;
#endif
    p.post(Inverse{get_vars(var_ids_1), get_vars(var_ids_2)});
}

auto Python::post_xor(const vector<std::string> & var_ids) -> void
{
#ifdef WRITE_API_CALLS
    cout << "post_xor" << endl;
#endif
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
        .def("solve", &Python::solve,
            py::arg("all_solutions") = true,
            py::arg("timeout") = nullopt,
            py::arg("solution_limit") = nullopt,
            py::arg("callback") = nullopt,
            py::arg("prove") = false,
            py::arg("proof_name") = nullopt,
            py::arg("proof_location") = nullopt)
        .def("get_solution_value", &Python::get_solution_value, py::arg("var_id"), py::arg("solution_number") = 0)
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

        .def("post_less_than_reif", &Python::post_less_than_reif)
        .def("post_less_than_equal_reif", &Python::post_less_than_equal_reif)
        .def("post_greater_than_reif", &Python::post_greater_than_reif)
        .def("post_greater_than_equal_reif", &Python::post_greater_than_equal_reif)

        .def("post_equals", &Python::post_equals)
        .def("post_equals_reif", &Python::post_equals_reif)

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
        .def("post_and_reif", &Python::post_and_reif)
        .def("post_or", &Python::post_or)
        .def("post_or_reif", &Python::post_or_reif)

        .def("post_implies", &Python::post_implies)
        .def("post_implies_reif", &Python::post_implies_reif)

        .def("post_count", &Python::post_count)
        .def("post_element", &Python::post_element)
        .def("post_min", &Python::post_min)
        .def("post_max", &Python::post_max)
        .def("post_nvalue", &Python::post_nvalue)
        .def("post_table", &Python::post_table)
        .def("post_negative_table", &Python::post_negative_table)
        .def("post_inverse", &Python::post_inverse)
        .def("post_xor", &Python::post_xor);
}