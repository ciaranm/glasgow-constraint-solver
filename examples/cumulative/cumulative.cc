#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
#include <ranges>
#include <string>
#include <utility>
#include <vector>

#include <cxxopts.hpp>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#endif

using namespace gcs;

using std::cerr;
using std::cref;
using std::make_optional;
using std::move;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::string;
using std::uniform_int_distribution;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

namespace
{
    // --variant selects the OPB encoding of the Cumulative, spelled exactly as
    // the GCS_CUMULATIVE_ENCODING environment variable spells it so that a
    // measurement taken here transfers to a test lane without translation.
    auto encoding_from_string(const string & spec) -> optional<CumulativeEncoding>
    {
        if (spec == "time-indexed")
            return CumulativeEncoding::TimeIndexed;
        if (spec == "both")
            return CumulativeEncoding::Both;
        if (spec == "both-recovering")
            return CumulativeEncoding::BothRecovering;
        if (spec == "start-checkpoint")
            return CumulativeEncoding::StartCheckpoint;
        return nullopt;
    }

    auto encoding_names() -> string
    {
        return "time-indexed, both, both-recovering, start-checkpoint";
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Cumulative Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program options")                               //
            ("help", "Display help information")                             //
            ("prove", "Create a proof")                                      //
            ("proof-files-basename", "Basename for the .opb and .pbp files", //
                cxxopts::value<string>()->default_value("cumulative"))       //
            ("stats", "Print solve statistics")                              //
            ;

        options.add_options("Model")                                                              //
            ("variant",                                                                           //
                "Which OPB encoding to give the Cumulative. Supported: " + encoding_names() +     //
                    ". Left alone by default, so the solver's own default applies. The encoding " //
                    "changes the proof and nothing else: the same solutions are found, by the "   //
                    "same search, whichever is chosen",                                           //
                cxxopts::value<string>())                                                         //
            ;

        options.add_options("Instance")                                                                            //
            ("tasks",                                                                                              //
                "Generate this many random tasks instead of the built-in five. The lengths and "                   //
                "heights come from --seed; the capacity from --capacity",                                          //
                cxxopts::value<long long>())                                                                       //
            ("capacity", "Resource capacity for a generated instance",                                             //
                cxxopts::value<long long>()->default_value("3"))                                                   //
            ("max-length",                                                                                         //
                "Generated lengths are drawn from 1 .. this. The default of four keeps a generated "               //
                "instance small enough to solve; the case the start-checkpoint encoding exists for is "            //
                "the opposite one, a few tasks of very long duration, where the time-indexed block is "            //
                "linear in the duration and the start-checkpoint one does not mention it",                         //
                cxxopts::value<long long>()->default_value("4"))                                                   //
            ("max-start",                                                                                          //
                "Start times are drawn from 0 .. this. Zero, the default, uses the whole horizon, which "          //
                "is what makes a long duration expensive to *solve* as well as to encode. Setting it "             //
                "small separates the two: a task of duration 10000 whose start has nine possible values "          //
                "still has a 10000-long window, and so a per-time block linear in the duration, but an "           //
                "instance anyone can solve",                                                                       //
                cxxopts::value<long long>()->default_value("0"))                                                   //
            ("horizon",                                                                                            //
                "Override the planning horizon. The optimum does not depend on it once it is large "               //
                "enough to hold one, but the time-indexed encoding is linear in it and the "                       //
                "start-checkpoint one does not mention it, so sweeping it against --tasks is how the "             //
                "two are compared. Zero, the default, uses ten for the built-in instance and the sum "             //
                "of the lengths for a generated one",                                                              //
                cxxopts::value<long long>()->default_value("0"))                                                   //
            ("seed", "Seed for the generated lengths and heights", cxxopts::value<unsigned>()->default_value("0")) //
            ;

        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        println(cerr, "Error: {}", e.what());
        println(cerr, "Try {} --help", argv[0]);
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        println("Usage: {} [options]", argv[0]);
        println("");
        println("Tasks share a single cumulative resource.");
        println("Minimise the makespan: the time at which the last task finishes.");
        println("");
        print("{}", options.help());
        return EXIT_SUCCESS;
    }

    optional<CumulativeEncoding> encoding;
    if (options_vars.contains("variant")) {
        auto variant_name = options_vars["variant"].as<string>();
        encoding = encoding_from_string(variant_name);
        if (! encoding) {
            println(cerr, "Error: unknown --variant value '{}'. Supported: {}.", variant_name, encoding_names());
            return EXIT_FAILURE;
        }
    }

    // Tasks on a resource of capacity 3. Lengths and heights are fixed; each
    // task's start time is the decision variable. The schedule must keep the
    // cumulated demand at every time point at or below the capacity.
    //
    // The built-in five, unless --tasks asks for a generated instance: the
    // encoding comparison wants n and the horizon moved independently, which
    // one fixed instance cannot do.
    vector<Integer> lengths = {3_i, 2_i, 2_i, 1_i, 4_i};
    vector<Integer> heights = {2_i, 1_i, 2_i, 3_i, 1_i};
    Integer capacity = 3_i;
    Integer horizon = 10_i;

    if (options_vars.contains("tasks")) {
        auto n = options_vars["tasks"].as<long long>();
        if (n < 1) {
            println(cerr, "Error: --tasks must be at least 1, not {}.", n);
            return EXIT_FAILURE;
        }
        capacity = Integer{options_vars["capacity"].as<long long>()};
        if (capacity < 1_i) {
            println(cerr, "Error: --capacity must be at least 1, not {}.", capacity);
            return EXIT_FAILURE;
        }

        auto max_length = options_vars["max-length"].as<long long>();
        if (max_length < 1) {
            println(cerr, "Error: --max-length must be at least 1, not {}.", max_length);
            return EXIT_FAILURE;
        }

        mt19937 rand(options_vars["seed"].as<unsigned>());
        lengths.clear();
        heights.clear();
        // Heights up to the capacity, so a task can be forced to run alone,
        // and lengths from one to --max-length: enough of a mix that the
        // profile has peaks to check.
        for (long long i = 0; i < n; ++i) {
            lengths.push_back(Integer{uniform_int_distribution<long long>{1, max_length}(rand)});
            heights.push_back(Integer{uniform_int_distribution<long long>{1, capacity.raw_value}(rand)});
        }

        // Every task end to end always fits, so a generated instance is always
        // feasible and --horizon only ever has to be raised from here.
        horizon = 0_i;
        for (const auto & l : lengths)
            horizon += l;
    }

    if (auto horizon_override = options_vars["horizon"].as<long long>(); horizon_override != 0) {
        if (horizon_override < 1) {
            println(cerr, "Error: --horizon must be positive, not {}.", horizon_override);
            return EXIT_FAILURE;
        }
        horizon = Integer{horizon_override};
    }

    // The start domain, which --max-start separates from the horizon. They are
    // the same thing by default, and a long duration then makes the instance
    // expensive to solve as well as to encode --- which is the confound to
    // avoid when the question is about the *encoding*: what makes the per-time
    // block big is the task's possible-active window, which runs from the
    // earliest start to the latest start plus the length, so a long task has a
    // long window however few starts it can take.
    auto max_start = horizon;
    if (auto max_start_override = options_vars["max-start"].as<long long>(); max_start_override != 0) {
        if (max_start_override < 0) {
            println(cerr, "Error: --max-start must not be negative, not {}.", max_start_override);
            return EXIT_FAILURE;
        }
        max_start = Integer{max_start_override};
    }

    Problem p;
    auto starts = p.create_integer_variable_vector(lengths.size(), 0_i, max_start, "s");

    auto cumulative = Cumulative{starts, lengths, heights, capacity};
    if (encoding)
        cumulative.with_encoding(*encoding);
    p.post(move(cumulative));

    auto makespan = p.create_integer_variable(0_i, horizon + Integer{static_cast<long long>(lengths.size())}, "makespan");
    for (auto i = 0u; i < lengths.size(); ++i)
        p.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * makespan + -1_i * starts[i], lengths[i]});

    p.minimise(makespan);

    auto stats = solve_with(p, //
        SolveCallbacks{        //
            .solution = [&](const CurrentState & s) -> bool {
                println("schedule: starts {} makespan {}", starts | std::ranges::views::transform(cref(s)), s(makespan));
                return true;
            }},
        options_vars.contains("prove") ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>()) : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
