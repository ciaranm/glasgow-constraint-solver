#include <gcs/gcs.hh>

#include <nlohmann/json.hpp>

#include <boost/program_options.hpp>

#include <fmt/chrono.h>
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#include <fmt/std.h>

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <csignal>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <iostream>
#include <list>
#include <mutex>
#include <optional>
#include <string>
#include <thread>
#include <unordered_map>
#include <vector>

using namespace gcs;

using std::atomic;
using std::cerr;
using std::condition_variable;
using std::cout;
using std::cv_status;
using std::exception;
using std::flush;
using std::ifstream;
using std::list;
using std::mutex;
using std::nullopt;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::string;
using std::thread;
using std::unique_lock;
using std::unordered_map;
using std::vector;
using std::chrono::milliseconds;
using std::chrono::seconds;
using std::chrono::system_clock;

using fmt::print;
using fmt::println;

namespace po = boost::program_options;

class FlatZincInterfaceError : public exception
{
private:
    std::string _wat;

public:
    explicit FlatZincInterfaceError(const std::string & w) :
        _wat(w)
    {
    }

    virtual auto what() const noexcept -> const char * override
    {
        return _wat.c_str();
    }
};

namespace
{
    static atomic<bool> abort_flag{false}, was_terminated{false};

    auto sig_int_or_term_handler(int) -> void
    {
        abort_flag.store(true);
        was_terminated.store(true);
    }

    struct ExtractedData
    {
        unordered_map<string, pair<IntegerVariableID, bool>> integer_variables;
        unordered_map<string, vector<Integer>> constant_arrays;
        unordered_map<string, vector<IntegerVariableID>> variable_arrays;
        list<vector<Integer>> unnamed_constant_arrays;
        vector<IntegerVariableID> branch_variables, all_variables;
    };

    auto arg_as_array_of_integer(ExtractedData & data, const auto & args, int idx) -> vector<Integer> *
    {
        auto a = args.at(idx);
        if (a.is_string()) {
            string name = a;
            auto iter = data.constant_arrays.find(name);
            if (iter == data.constant_arrays.end())
                throw FlatZincInterfaceError{fmt::format("Can't find constant array named {}", name)};
            return &iter->second;
        }
        else {
            vector<Integer> result;
            for (const auto & val : a)
                result.push_back(Integer{static_cast<long long>(val)});
            data.unnamed_constant_arrays.push_back(move(result));
            return &data.unnamed_constant_arrays.back();
        }
    }

    auto arg_as_array_of_var(ExtractedData & data, const auto & args, int idx) -> vector<IntegerVariableID>
    {
        auto a = args.at(idx);
        if (a.is_string()) {
            string name = a;
            auto iter = data.variable_arrays.find(name);
            if (iter == data.variable_arrays.end())
                throw FlatZincInterfaceError{fmt::format("Can't find variable array named {}", name)};
            return iter->second;
        }
        else if (a.is_array()) {
            vector<IntegerVariableID> result;
            for (const string v : a)
                result.push_back(data.integer_variables.at(v).first);
            return result;
        }
        else {
            throw UnimplementedException{fmt::format(
                "don't know how to parse array of variables at index {}", idx)};
        }
    }

    auto arg_as_var(ExtractedData & data, const auto & args, int idx) -> IntegerVariableID
    {
        auto a = args.at(idx);
        if (a.is_string()) {
            string name = a;
            auto iter = data.integer_variables.find(name);
            if (iter == data.integer_variables.end())
                throw FlatZincInterfaceError{fmt::format("Can't find variable named {}", name)};
            return iter->second.first;
        }
        else if (a.is_number()) {
            auto val = Integer{static_cast<long long>(a)};
            return ConstantIntegerVariableID{val};
        }
        else if (a.is_boolean()) {
            auto val = Integer{static_cast<bool>(a) ? 1_i : 0_i};
            return ConstantIntegerVariableID{val};
        }
        else
            throw FlatZincInterfaceError{fmt::format("Didn't get a string or number for arg_as_var? arg is \"{}\"", a.dump())};
    }
}

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()                                                                  //
        ("help", "Display help information")                                                       //
        ("all-solutions,a", "Print all solutions, or solve an optimisation problem to optimality") //
        ("n-solutions,n", po::value<unsigned long long>(), "Stop after this many solutions")       //
        ("statistics,s", "Print statistics")                                                       //
        ("timeout,t", po::value<unsigned long long>(), "Timeout in ms");                           //

    po::options_description all_options{"All options"};
    all_options.add_options() //
        ("file", po::value<string>(), "FlatZinc file used as input");

    all_options.add(display_options);

    po::positional_options_description positional_options;
    positional_options
        .add("file", 1);

    po::variables_map options_vars;

    try {
        po::store(po::command_line_parser(argc, argv)
                      .options(all_options)
                      .positional(positional_options)
                      .run(),
            options_vars);
        po::notify(options_vars);
    }
    catch (const po::error & e) {
        println(cerr, "Error: {}", e.what());
        println(cerr, "Try {} --help", argv[0]);
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        println("Usage: {} [options] flatzinc-file.fzn", argv[0]);
        println("");
        display_options.print(cout);
        return EXIT_SUCCESS;
    }

    bool all_solutions = options_vars.contains("all-solutions");

    optional<unsigned long long> solution_limit;
    if (options_vars.contains("n-solutions"))
        solution_limit = options_vars["n-solutions"].as<unsigned long long>();

    signal(SIGINT, &sig_int_or_term_handler);
    signal(SIGTERM, &sig_int_or_term_handler);

    thread timeout_thread;
    mutex timeout_mutex;
    condition_variable timeout_cv;
    bool actually_timed_out = false;

    if (options_vars.contains("timeout")) {
        milliseconds limit{options_vars["timeout"].as<unsigned long long>()};

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

    try {
        auto fznname = options_vars["file"].as<string>();
        ifstream infile{fznname};
        if (! infile)
            throw FlatZincInterfaceError{fmt::format("Error reading from {}", fznname)};

        auto fzn = nlohmann::json::parse(infile);
        if (fzn["version"] != "1.0")
            throw FlatZincInterfaceError{fmt::format("Unknown flatzinc version {} in {}", string{fzn["version"]}, fznname)};

        Problem problem;
        ExtractedData data;

        for (auto v = fzn["variables"].begin(), v_end = fzn["variables"].end(); v != v_end; ++v) {
            auto name = v.key();
            auto vardata = v.value();
            string var_type = vardata["type"];
            if (var_type == "bool") {
                auto var = problem.create_integer_variable(0_i, 1_i, name);
                data.integer_variables.emplace(name, pair{var, true});
                if ((! vardata.contains("defined")) || (! vardata["defined"].get<bool>()))
                    data.branch_variables.push_back(var);
                data.all_variables.push_back(var);
            }
            else if (var_type == "int") {
                if (! vardata.contains("domain")) {
                    auto var = problem.create_integer_variable(Integer::min_value(), Integer::max_value(), name);
                    data.integer_variables.emplace(name, pair{var, false});
                    if ((! vardata.contains("defined")) || (! vardata["defined"].get<bool>()))
                        data.branch_variables.push_back(var);
                    data.all_variables.push_back(var);
                }
                else {
                    auto size = vardata["domain"].size();
                    auto var = problem.create_integer_variable(                   //
                        Integer{vardata["domain"][0][0].get<long long>()},        //
                        Integer{vardata["domain"][size - 1][1].get<long long>()}, //
                        name);
                    data.integer_variables.emplace(name, pair{var, false});
                    if ((! vardata.contains("defined")) || (! vardata["defined"].get<bool>()))
                        data.branch_variables.push_back(var);
                    data.all_variables.push_back(var);
                    for (unsigned i = 0; i < size - 1; ++i) {
                        problem.post(Or{{! (var >= Integer{vardata["domain"][i][1].get<long long>()} + 1_i),
                                            var >= Integer{vardata["domain"][i + 1][0].get<long long>()}},
                            innards::TrueLiteral{}});
                    }
                }
            }
            else
                throw FlatZincInterfaceError{fmt::format("Unknown flatzinc variable type {} for variable {} in {}", var_type, name, fznname)};
        }

        for (auto a = fzn["arrays"].begin(), a_end = fzn["arrays"].end(); a != a_end; ++a) {
            auto name = a.key();
            auto arraydata = a.value();

            vector<Integer> values;
            vector<IntegerVariableID> variables;
            bool seen_variable = false;
            for (const auto & v : arraydata["a"]) {
                if (v.is_string()) {
                    seen_variable = true;
                    variables.push_back(data.integer_variables.at(string{v}).first);
                }
                else {
                    auto val = Integer{v.get<long long>()};
                    values.push_back(val);
                    variables.push_back(ConstantIntegerVariableID{val});
                }
            }

            if (! seen_variable)
                data.constant_arrays.emplace(name, move(values));
            data.variable_arrays.emplace(name, move(variables));
        }

        for (const auto & constraint : fzn["constraints"]) {
            string id = constraint["id"];
            auto args = constraint["args"];
            if (id == "array_int_element") {
                const auto & idx = arg_as_var(data, args, 0);
                auto array = arg_as_array_of_integer(data, args, 1);
                const auto & var = arg_as_var(data, args, 2);

                problem.post(ElementConstantArray{var, idx - 1_i, array});
            }
            else if (id == "array_int_maximum" || id == "array_int_minimum") {
                const auto & var = arg_as_var(data, args, 0);
                const auto & vars = arg_as_array_of_var(data, args, 1);
                if (id.ends_with("maximum"))
                    problem.post(ArrayMax{vars, var});
                else
                    problem.post(ArrayMin{vars, var});
            }
            else if (id == "array_var_int_element") {
                const auto & idx = arg_as_var(data, args, 0);
                auto array = arg_as_array_of_var(data, args, 1);
                const auto & var = arg_as_var(data, args, 2);

                problem.post(Element{var, idx - 1_i, array});
            }
            else if (id == "int_abs") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                problem.post(Abs{var1, var2});
            }
            else if (id == "int_div") {
                throw UnimplementedException{};
            }
            else if (id == "int_eq" || id == "bool2int" || id == "bool_eq") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                problem.post(Equals{var1, var2});
            }
            else if (id == "int_eq_reif") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & reif = arg_as_var(data, args, 2);
                problem.post(EqualsIff{var1, var2, reif == 1_i});
            }
            else if (id == "int_le") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                problem.post(LessThanEqual{var1, var2});
            }
            else if (id == "int_lt") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                problem.post(LessThan{var1, var2});
            }
            else if (id == "int_le_reif") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & reif = arg_as_var(data, args, 2);
                problem.post(LessThanEqualIff{var1, var2, reif == 1_i});
            }
            else if (id == "int_lt_reif") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & reif = arg_as_var(data, args, 2);
                problem.post(LessThanIff{var1, var2, reif == 1_i});
            }
            else if (id == "int_lin_eq" || id == "int_lin_le" || id == "int_lin_ne") {
                auto coeffs = arg_as_array_of_integer(data, args, 0);
                const auto & vars = arg_as_array_of_var(data, args, 1);
                Integer total{static_cast<long long>(args.at(2))};
                if (coeffs->size() != vars.size())
                    throw FlatZincInterfaceError{fmt::format("Array length mismatch in {} in {}", id, fznname)};

                SumOf<Weighted<IntegerVariableID>> terms;
                for (size_t c = 0; c < coeffs->size(); ++c)
                    terms += (*coeffs)[c] * vars[c];

                if (id.ends_with("_eq"))
                    problem.post(LinearEquality{terms, total});
                else if (id.ends_with("_ne"))
                    problem.post(LinearNotEquals{terms, total});
                else
                    problem.post(terms <= total);
            }
            else if (id == "int_lin_eq_reif" || id == "int_lin_le_reif" || id == "int_lin_ne_reif") {
                auto coeffs = arg_as_array_of_integer(data, args, 0);
                const auto & vars = arg_as_array_of_var(data, args, 1);
                Integer total{static_cast<long long>(args.at(2))};
                if (coeffs->size() != vars.size())
                    throw FlatZincInterfaceError{fmt::format("Array length mismatch in {} in {}", id, fznname)};
                const auto & reif = arg_as_var(data, args, 3);

                SumOf<Weighted<IntegerVariableID>> terms;
                for (size_t c = 0; c < coeffs->size(); ++c)
                    terms += (*coeffs)[c] * vars[c];

                if (id.ends_with("_eq_reif"))
                    problem.post(LinearEqualityIff{terms, total, reif == 1_i});
                else if (id.ends_with("_ne_reif"))
                    problem.post(LinearEqualityIff{terms, total, reif != 1_i});
                else
                    problem.post(LinearLessEqualIff{terms, total, reif == 1_i});
            }
            else if (id == "int_max") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & var3 = arg_as_var(data, args, 2);
                problem.post(Max{var1, var2, var3});
            }
            else if (id == "int_min") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & var3 = arg_as_var(data, args, 2);
                problem.post(Min{var1, var2, var3});
            }
            else if (id == "int_mod") {
                throw UnimplementedException{};
            }
            else if (id == "int_ne" || id == "bool_not") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                problem.post(NotEquals{var1, var2});
            }
            else if (id == "int_ne_reif") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & reif = arg_as_var(data, args, 2);
                problem.post(EqualsIff{var1, var2, reif != 1_i});
            }
            else if (id == "int_plus") {
                throw UnimplementedException{};
            }
            else if (id == "int_pow") {
                throw UnimplementedException{};
            }
            else if (id == "int_times") {
                throw UnimplementedException{};
            }
            else if (id == "set_in") {
                throw UnimplementedException{};
            }
            else if (id == "array_bool_and") {
                throw UnimplementedException{};
            }
            else if (id == "array_bool_element") {
                throw UnimplementedException{};
            }
            else if (id == "array_bool_xor") {
                throw UnimplementedException{};
            }
            else if (id == "array_var_bool_element") {
                throw UnimplementedException{};
            }
            else if (id == "bool_and") {
                throw UnimplementedException{};
            }
            else if (id == "bool_clause") {
                const auto & pos = arg_as_array_of_var(data, args, 0);
                const auto & neg = arg_as_array_of_var(data, args, 1);
                innards::Literals lits;
                for (auto & v : pos)
                    lits.push_back(v == 1_i);
                for (auto & v : neg)
                    lits.push_back(v == 0_i);
                problem.post(Or{lits, innards::TrueLiteral{}});
            }
            else if (id == "bool_clause_reif") {
                const auto & pos = arg_as_array_of_var(data, args, 0);
                const auto & neg = arg_as_array_of_var(data, args, 1);
                const auto & reif = arg_as_var(data, args, 2);
                innards::Literals lits;
                for (auto & v : pos)
                    lits.push_back(v == 1_i);
                for (auto & v : neg)
                    lits.push_back(v == 0_i);
                problem.post(Or{lits, reif == 1_i});
            }
            else if (id == "bool_eq_reif") {
                throw UnimplementedException{};
            }
            else if (id == "bool_le") {
                throw UnimplementedException{};
            }
            else if (id == "bool_le_reif") {
                throw UnimplementedException{};
            }
            else if (id == "bool_lin_eq") {
                throw UnimplementedException{};
            }
            else if (id == "bool_lin_le") {
                throw UnimplementedException{};
            }
            else if (id == "bool_lt") {
                throw UnimplementedException{};
            }
            else if (id == "bool_lt_reif") {
                throw UnimplementedException{};
            }
            else if (id == "bool_or") {
                throw UnimplementedException{};
            }
            else if (id == "bool_xor") {
                throw UnimplementedException{};
            }
            else if (id == "glasgow_alldifferent") {
                const auto & vars = arg_as_array_of_var(data, args, 0);
                problem.post(AllDifferent{vars});
            }
            else if (id == "glasgow_count_eq") {
                const auto & vars = arg_as_array_of_var(data, args, 0);
                const auto & varmatch = arg_as_var(data, args, 1);
                const auto & varcount = arg_as_var(data, args, 2);
                problem.post(Count{vars, varmatch, varcount});
            }
            else
                throw FlatZincInterfaceError{fmt::format("Unknown flatzinc constraint {} in {}", id, fznname)};
        }

        auto solve_method = fzn["solve"]["method"];
        if (solve_method == "satisfy") {
        }
        else if (solve_method == "minimize") {
            problem.minimise(data.integer_variables.at(fzn["solve"]["objective"]).first);
        }
        else if (solve_method == "maximize") {
            problem.maximise(data.integer_variables.at(fzn["solve"]["objective"]).first);
        }
        else
            throw FlatZincInterfaceError{fmt::format("Unknown solve method {} in {}", string{solve_method}, fznname)};

        BranchCallback branch = branch_on_dom_then_deg(data.branch_variables);
        GuessCallback guess = guess_smallest_value_first();
        if (fzn["solve"].contains("ann")) {
            auto parse_int_search = [&data](const auto & ann) {
                BranchCallback branch;
                GuessCallback guess;

                auto args = ann["args"];
                data.branch_variables = arg_as_array_of_var(data, args, 0);
                string var_heuristic = args[1];
                string val_heuristic = args[2];
                string method = args[3];

                if (var_heuristic == "first_fail") {
                    branch = branch_on_dom(data.branch_variables);
                }
                else if (var_heuristic == "input_order") {
                    branch = branch_in_order(data.branch_variables);
                }
                else if (var_heuristic == "dom_w_deg") {
                    // not technically "w" but it'll do for now
                    branch = branch_on_dom_then_deg(data.branch_variables);
                }
                else {
                    println(cerr, "Warning: treating unknown int_search variable heuristic {} as dom_w_deg instead", var_heuristic);
                }

                if (val_heuristic == "indomain" || val_heuristic == "indomain_min") {
                    guess = guess_smallest_value_first();
                }
                else if (val_heuristic == "indomain_max") {
                    guess = guess_largest_value_first();
                }
                else if (val_heuristic == "indomain_median") {
                    guess = guess_median_value();
                }
                else {
                    println(cerr, "Warning: treating unknown int_search value heuristic {} as indomain_min instead", val_heuristic);
                }

                if (method != "complete") {
                    println(cerr, "Warning: treating unknown int_search method {} as complete instead", method);
                }

                return pair{branch, guess};
            };

            auto anns = fzn["solve"]["ann"];
            for (const auto & ann : anns) {
                if (ann["id"] == "int_search") {
                    tie(branch, guess) = parse_int_search(ann);
                }
                else if (ann["id"] == "seq_search") {
                    if (ann["args"].size() > 1)
                        println(cerr, "Warning: only using first item of seq_search for value ordering");
                    for (const auto & sub_ann : ann["args"][0]) {
                        tie(branch, guess) = parse_int_search(sub_ann);
                    }
                }
            }
        }

        if (options_vars.contains("statistics")) {
            println(cout, "%%%mzn-stat: intVariables={}", data.integer_variables.size());
            println(cout, "%%%mzn-stat: branchableVariables={}", data.branch_variables.size());
            println(cout, "%%%mzn-stat-end");
            cout << flush;
        }

        bool completed = false;
        auto stats = solve_with(problem,
            SolveCallbacks{
                .solution = [&](const CurrentState & s) -> bool {
                    for (const string name : fzn["output"]) {
                        if (data.integer_variables.contains(name)) {
                            auto vardata = data.integer_variables.at(name);
                            if (! s.has_single_value(data.integer_variables.at(name).first))
                                throw UnimplementedException{fmt::format("Variable {} does not have a unique value", name)};
                            if (vardata.second)
                                println(cout, "{} = {};", name, s(vardata.first) == 1_i ? "true" : "false");
                            else
                                println(cout, "{} = {};", name, s(vardata.first));
                        }
                        else if (data.variable_arrays.contains(name)) {
                            vector<string> vals;
                            for (auto & v : data.variable_arrays.at(name)) {
                                if (! s.has_single_value(v))
                                    throw UnimplementedException{fmt::format("Variable inside array {} does not have a unique value", name)};
                                vals.push_back(fmt::format("{}", s(v)));
                                println(cout, "{} = [{}];", name, fmt::join(vals, ", "));
                            }
                        }
                        else
                            throw FlatZincInterfaceError{fmt::format("Unknown output item {} in {}", name, fznname)};
                    }
                    println(cout, "----------");
                    cout << flush;
                    if (solution_limit) {
                        if (--*solution_limit == 0)
                            return false;
                    }
                    else if (! all_solutions)
                        return false;

                    return true;
                },
                .branch = branch_sequence(vector{branch, branch_on_dom_then_deg(data.branch_variables),
                    branch_on_dom_then_deg(data.all_variables)}),
                .guess = guess,
                .completed = [&] { completed = true; }},
            nullopt, &abort_flag);

        if (timeout_thread.joinable()) {
            {
                unique_lock<mutex> guard(timeout_mutex);
                abort_flag.store(true);
                timeout_cv.notify_all();
            }
            timeout_thread.join();
        }

        if (completed) {
            println(cout, "==========");
            cout << flush;
        }

        if (options_vars.contains("statistics")) {
            println(cout, "%%%mzn-stat: failures={}", stats.failures);
            println(cout, "%%%mzn-stat: nodes={}", stats.recursions);
            println(cout, "%%%mzn-stat: propagations={}", stats.propagations);
            println(cout, "%%%mzn-stat: effectfulPropagations={}", stats.effectful_propagations);
            println(cout, "%%%mzn-stat: peakDepth={}", stats.max_depth);
            println(cout, "%%%mzn-stat: solveTime={:.3f}", duration_cast<milliseconds>(stats.solve_time).count() / 1000.0);
            println(cout, "%%%mzn-stat-end");
            cout << flush;
        }
    }
    catch (const exception & e) {
        println(cerr, "{}: error: {}", argv[0], e.what());

        if (timeout_thread.joinable()) {
            {
                unique_lock<mutex> guard(timeout_mutex);
                abort_flag.store(true);
                timeout_cv.notify_all();
            }
            timeout_thread.join();
        }
        return EXIT_FAILURE;
    }

    if (timeout_thread.joinable()) {
        {
            unique_lock<mutex> guard(timeout_mutex);
            abort_flag.store(true);
            timeout_cv.notify_all();
        }
        timeout_thread.join();
    }

    return EXIT_SUCCESS;
}
