#include <gcs/gcs.hh>
#include <gcs/innards/interval_set.hh>

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

using gcs::innards::IntervalSet;
using gcs::innards::Literals;
using gcs::innards::TrueLiteral;

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
        unordered_map<string, pair<vector<IntegerVariableID>, bool>> variable_arrays;
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

    auto arg_as_set_of_integer(ExtractedData &, const auto & args, int idx) -> IntervalSet<Integer>
    {
        auto a = args.at(idx)["set"];
        IntervalSet<Integer> result;
        for (const auto & range : a)
            result.insert_at_end(Integer{static_cast<long long>(range[0])}, Integer{static_cast<long long>(range[1])});
        return result;
    }

    auto arg_as_array_of_var(ExtractedData & data, const auto & args, int idx) -> vector<IntegerVariableID>
    {
        auto a = args.at(idx);
        if (a.is_string()) {
            string name = a;
            auto iter = data.variable_arrays.find(name);
            if (iter == data.variable_arrays.end())
                throw FlatZincInterfaceError{fmt::format("Can't find variable array named {}", name)};
            return iter->second.first;
        }
        else if (a.is_array()) {
            vector<IntegerVariableID> result;
            for (const auto & v : a)
                if (v.is_string())
                    result.push_back(data.integer_variables.at(v).first);
                else
                    throw FlatZincInterfaceError{fmt::format("Don't know how to parse entry {} in array of variables", v.dump())};
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
        ("timeout,t", po::value<unsigned long long>(), "Timeout in ms")                            //
        ("prove", po::value<string>(), "Write proofs to this file (.opb and .pbp)");               //
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
                            TrueLiteral{}});
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
            bool seen_variable = false, seen_a_bool = false;
            for (const auto & v : arraydata["a"]) {
                if (v.is_string()) {
                    seen_variable = true;
                    variables.push_back(data.integer_variables.at(string{v}).first);
                    seen_a_bool = seen_a_bool || data.integer_variables.at(string{v}).second;
                }
                else {
                    auto val = Integer{v.get<long long>()};
                    values.push_back(val);
                    variables.push_back(ConstantIntegerVariableID{val});
                }
            }

            if (! seen_variable)
                data.constant_arrays.emplace(name, move(values));
            data.variable_arrays.emplace(name, pair{move(variables), seen_a_bool});
        }

        for (const auto & constraint : fzn["constraints"]) {
            string id = constraint["id"];
            auto args = constraint["args"];
            if (id == "array_int_element" || id == "array_bool_element") {
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
            else if (id == "array_var_int_element" || id == "array_var_bool_element") {
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
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & var3 = arg_as_var(data, args, 2);
                problem.post(Div{var1, var2, var3});
            }
            else if (id == "int_eq" || id == "bool2int" || id == "bool_eq") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                problem.post(Equals{var1, var2});
            }
            else if (id == "int_eq_reif" || id == "bool_eq_reif") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & reif = arg_as_var(data, args, 2);
                problem.post(EqualsIff{var1, var2, reif == 1_i});
            }
            else if (id == "int_le" || id == "bool_le") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                problem.post(LessThanEqual{var1, var2});
            }
            else if (id == "int_lt" || id == "bool_lt") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                problem.post(LessThan{var1, var2});
            }
            else if (id == "int_le_reif" || id == "bool_le_reif") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & reif = arg_as_var(data, args, 2);
                problem.post(LessThanEqualIff{var1, var2, reif == 1_i});
            }
            else if (id == "int_lt_reif" || id == "bool_lt_reif") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & reif = arg_as_var(data, args, 2);
                problem.post(LessThanIff{var1, var2, reif == 1_i});
            }
            else if (id == "int_lin_eq" || id == "int_lin_le" || id == "int_lin_ne" || id == "bool_lin_eq" || id == "bool_lin_le") {
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
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & var3 = arg_as_var(data, args, 2);
                problem.post(Mod{var1, var2, var3});
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
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & var3 = arg_as_var(data, args, 2);
                problem.post(Plus{var1, var2, var3});
            }
            else if (id == "int_pow") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & var3 = arg_as_var(data, args, 2);
                problem.post(Power{var1, var2, var3});
            }
            else if (id == "int_times") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & var3 = arg_as_var(data, args, 2);
                problem.post(Times{var1, var2, var3});
            }
            else if (id == "set_in") {
                const auto & var = arg_as_var(data, args, 0);
                const auto & set = arg_as_set_of_integer(data, args, 1);

                // var is inside the range as a whole
                problem.post(WeightedSum{} + 1_i * var >= set.intervals[0].first);
                problem.post(WeightedSum{} + 1_i * var <= set.intervals[set.intervals.size() - 1].second);

                // var isn't inside any of the gaps between ranges
                for (unsigned i = 0; i < set.intervals.size() - 1; ++i)
                    problem.post(Or{{! (var >= set.intervals[i].second + 1_i), var >= set.intervals[i + 1].first},
                        TrueLiteral{}});
            }
            else if (id == "array_bool_and") {
                const auto & vars = arg_as_array_of_var(data, args, 0);
                const auto & reif = arg_as_var(data, args, 1);
                Literals lits;
                for (auto & v : vars)
                    lits.push_back(v == 1_i);
                problem.post(And{lits, reif == 1_i});
            }
            else if (id == "array_bool_xor") {
                const auto & vars = arg_as_array_of_var(data, args, 0);
                problem.post(ParityOdd{vars});
            }
            else if (id == "bool_and") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & reif = arg_as_var(data, args, 2);
                problem.post(And{Literals{{var1 == 1_i, var2 == 1_i}}, reif == 1_i});
            }
            else if (id == "bool_clause") {
                const auto & pos = arg_as_array_of_var(data, args, 0);
                const auto & neg = arg_as_array_of_var(data, args, 1);
                Literals lits;
                for (auto & v : pos)
                    lits.push_back(v == 1_i);
                for (auto & v : neg)
                    lits.push_back(v == 0_i);
                problem.post(Or{lits, TrueLiteral{}});
            }
            else if (id == "bool_clause_reif") {
                const auto & pos = arg_as_array_of_var(data, args, 0);
                const auto & neg = arg_as_array_of_var(data, args, 1);
                const auto & reif = arg_as_var(data, args, 2);
                Literals lits;
                for (auto & v : pos)
                    lits.push_back(v == 1_i);
                for (auto & v : neg)
                    lits.push_back(v == 0_i);
                problem.post(Or{lits, reif == 1_i});
            }
            else if (id == "bool_or") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                const auto & reif = arg_as_var(data, args, 2);
                problem.post(Or{Literals{{var1 == 1_i, var2 == 1_i}}, reif == 1_i});
            }
            else if (id == "bool_xor") {
                const auto & var1 = arg_as_var(data, args, 0);
                const auto & var2 = arg_as_var(data, args, 1);
                if (args.size() == 3) {
                    const auto & reif = arg_as_var(data, args, 2);
                    problem.post(EqualsIff{var1, var2, reif != 1_i});
                }
                else
                    problem.post(NotEquals{var1, var2});
            }
            else if (id == "set_in_reif") {
                const auto & var = arg_as_var(data, args, 0);
                const auto & set = arg_as_set_of_integer(data, args, 1);
                const auto & reif = arg_as_var(data, args, 2);

                // reif -> var is inside the range as a whole
                problem.post(Or{{reif != 1_i, var >= set.intervals[0].first}, TrueLiteral{}});
                problem.post(Or{{reif != 1_i, var < set.intervals[set.intervals.size() - 1].second + 1_i}, TrueLiteral{}});

                // reif -> var isn't inside any of the gaps between ranges
                for (unsigned i = 0; i < set.intervals.size() - 1; ++i)
                    problem.post(Or{{reif != 1_i,
                                        ! (var >= set.intervals[i].second + 1_i),
                                        var >= set.intervals[i + 1].first},
                        TrueLiteral{}});

                // ! reif -> var isn't inside this range
                for (unsigned i = 0; i < set.intervals.size(); ++i)
                    problem.post(Or{{reif == 1_i,
                                        var < set.intervals[i].first,
                                        var >= set.intervals[i].second + 1_i},
                        TrueLiteral{}});
            }
            else if (id == "glasgow_alldifferent") {
                const auto & vars = arg_as_array_of_var(data, args, 0);
                problem.post(AllDifferent{vars});
            }
            else if (id == "glasgow_circuit") {
                const auto & vars = arg_as_array_of_var(data, args, 0);
                vector<IntegerVariableID> vars_shifted;
                for (const auto & v : vars)
                    vars_shifted.push_back(v - 1_i);
                problem.post(Circuit{vars});
            }
            else if (id == "glasgow_count_eq") {
                const auto & vars = arg_as_array_of_var(data, args, 0);
                const auto & varmatch = arg_as_var(data, args, 1);
                const auto & varcount = arg_as_var(data, args, 2);
                problem.post(Count{vars, varmatch, varcount});
            }
            else if (id == "glasgow_inverse") {
                const auto & vars1 = arg_as_array_of_var(data, args, 0);
                const auto & vars2 = arg_as_array_of_var(data, args, 1);
                problem.post(Inverse{vars1, vars2, 1_i, 1_i});
            }
            else if (id == "glasgow_regular") {
                const auto & vars = arg_as_array_of_var(data, args, 0);
                const auto & num_states = static_cast<long long>(args.at(1));
                const auto & num_symbols = static_cast<long long>(args.at(2));
                vector<Integer> symbols{};
                for (int i = 0; i <= num_symbols - 1; i++) {
                    symbols.emplace_back(i);
                }
                const auto & raw_transitions = arg_as_array_of_integer(data, args, 3);
                const auto & start_state = static_cast<long long>(args.at(4));

                vector<vector<long>> transitions;
                for (int i = 0; i < num_states; i++) {
                    transitions.emplace_back();
                    for (int j = 0; j < num_symbols; j++) {
                        // Swap 0 and start state to ensure start state is always 0 for gcs::regular
                        auto t_value = raw_transitions->at(i * num_symbols + j).raw_value;
                        if (t_value == start_state) {
                            transitions[i].emplace_back(0);
                        }
                        else if (t_value == 1) {
                            transitions[i].emplace_back(start_state - 1);
                        }
                        else
                            transitions[i].emplace_back(t_value - 1);
                    }
                }

                const auto & final_states = arg_as_set_of_integer(data, args, 5);
                vector<long> final_states_raw{};
                for (long i = 1; i < num_states + 1; i++) {
                    if (final_states.contains(Integer{i})) {
                        final_states_raw.emplace_back(i - 1);
                    }
                }

                problem.post(Regular{vars, symbols, num_states, transitions, final_states_raw});
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

        vector<BranchCallback> branchers;
        GuessCallback guessers;
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
                    branch = branch_on_dom_then_deg(data.branch_variables);
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
                    guess = guess_smallest_value_first();
                }

                if (method != "complete") {
                    println(cerr, "Warning: treating unknown int_search method {} as complete instead", method);
                }

                return pair{branch, guess};
            };

            auto anns = fzn["solve"]["ann"];
            for (const auto & ann : anns) {
                if (ann["id"] == "int_search" || ann["id"] == "bool_search") {
                    auto [branch, guess] = parse_int_search(ann);
                    branchers.push_back(branch);
                    guessers = guess;
                }
                else if (ann["id"] == "seq_search") {
                    bool first = true;
                    for (const auto & sub_ann : ann["args"][0]) {
                        auto [branch, guess] = parse_int_search(sub_ann);
                        branchers.push_back(branch);
                        if (first) {
                            guessers = guess;
                            first = false;
                        }
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

        branchers.push_back(branch_on_dom_then_deg(data.branch_variables));
        branchers.push_back(branch_on_dom_then_deg(data.all_variables));

        optional<ProofOptions> proof_options;
        if (options_vars.contains("prove")) {
            string basename = options_vars["prove"].as<string>();
            proof_options.emplace(basename + ".opb", basename + ".pbp");
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
                            for (auto & v : data.variable_arrays.at(name).first) {
                                if (! s.has_single_value(v))
                                    throw UnimplementedException{fmt::format("Variable inside array {} does not have a unique value", name)};
                                if (data.variable_arrays.at(name).second)
                                    vals.push_back(fmt::format("{}", s(v) == 1_i ? "true" : "false"));
                                else
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
                .branch = branch_sequence(branchers),
                .guess = guessers,
                .completed = [&] { completed = true; }},
            proof_options, &abort_flag);

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
