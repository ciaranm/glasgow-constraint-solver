#include "flatzinc_json_parser.hh"
#include <gcs/gcs.hh>

#include <boost/program_options.hpp>

#include <fmt/chrono.h>
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <csignal>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <iostream>
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
using std::jthread;
using std::mutex;
using std::nullopt;
using std::optional;
using std::string;
using std::unique_lock;
using std::unordered_map;
using std::vector;
using std::chrono::milliseconds;
using std::chrono::seconds;
using std::chrono::system_clock;

using fmt::print;
using fmt::println;

namespace po = boost::program_options;
namespace j = gcs::flatzincjson;

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

    jthread timeout_thread;
    mutex timeout_mutex;
    condition_variable timeout_cv;
    bool actually_timed_out = false;

    if (options_vars.contains("timeout")) {
        milliseconds limit{options_vars["timeout"].as<unsigned long long>()};

        timeout_thread = jthread([limit = limit, &timeout_mutex, &timeout_cv, &actually_timed_out] {
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

        j::FlatZincJson fzn = nlohmann::json::parse(infile);
        if (fzn.version != "1.0")
            throw FlatZincInterfaceError{fmt::format("Unknown flatzinc version {} in {}", fzn.version, fznname)};

        Problem problem;

        unordered_map<string, IntegerVariableID> integer_variables;
        for (const auto & [name, vardata] : fzn.variables) {
            string var_type = vardata["type"];
            if (var_type != "int")
                throw FlatZincInterfaceError{fmt::format("Unknown flatzinc variable type {} for variable {} in {}", var_type, name, fznname)};

            if (vardata["domain"].size() != 1)
                throw FlatZincInterfaceError{fmt::format("Can't parse domain for variable {} in {}", name, fznname)};
            integer_variables.emplace(name, //
                    problem.create_integer_variable( //
                        Integer{vardata["domain"][0][0].get<long long>()}, //
                        Integer{vardata["domain"][0][1].get<long long>()}, //
                        name));
        }

        unordered_map<string, vector<Integer>> arrays;
        for (const auto & [name, arraydata] : fzn.arrays) {
            vector<Integer> values;
            for (const auto & v : arraydata["a"])
                values.push_back(Integer{v.get<long long>()});
            arrays.emplace(name, move(values));
        }

        for (const auto & [annotations, args, id] : fzn.constraints) {
            if (id == "int_lin_eq") {
                const auto & coeffs = arrays.at(get<string>(args.at(0)));
                const auto & vars = get<vector<j::FlatZincJso>>(args.at(1));
                Integer total{static_cast<long long>(get<double>(args.at(2)))};
                if (coeffs.size() != vars.size())
                    throw FlatZincInterfaceError{fmt::format("Array length mismatch in {} in {}", id, fznname)};

                SumOf<Weighted<IntegerVariableID>> terms;
                for (size_t c = 0; c < coeffs.size(); ++c)
                    terms += coeffs[c] * integer_variables.at(get<string>(vars[c]));
                problem.post(terms == total);
            }
            else
                throw FlatZincInterfaceError{fmt::format("Unknown flatzinc constraint {} in {}", id, fznname)};
        }

        switch (fzn.solve.method) {
        case j::Method::SATISFY: break;
        case j::Method::MINIMIZE:
            problem.minimise(integer_variables.at(get<string>(*fzn.solve.objective)));
            break;
        case j::Method::MAXIMIZE:
            problem.maximise(integer_variables.at(get<string>(*fzn.solve.objective)));
            break;
        }

        bool completed = false;
        auto stats = solve_with(problem,
            SolveCallbacks{
                .solution = [&](const CurrentState & s) -> bool {
                    for (const auto & name : fzn.output)
                        println(cout, "{} = {};", name, s(integer_variables.at(name)));
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
            println(cout, "%%%mzn-stat: peakDepth={}", stats.max_depth);
            println(cout, "%%%mzn-stat: solveTime={:.3f}", duration_cast<milliseconds>(stats.solve_time).count() * 1000.0);
            cout << flush;
        }
    }
    catch (const exception & e) {
        println(cerr, "{}: error: {}", argv[0], e.what());
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
