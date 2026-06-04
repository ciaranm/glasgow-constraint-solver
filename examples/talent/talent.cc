#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/inverse.hh>
#include <gcs/constraints/logical.hh>
#include <gcs/constraints/min_max.hh>

#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cxxopts.hpp>

#include <iostream>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#endif

using namespace gcs;
using std::cerr;
using std::cout;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
using std::println;
#else
using fmt::format;
using fmt::print;
using fmt::println;
#endif

int main(int argc, char * argv[])
{
    cxxopts::Options options("Talent Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options()                                                //
            ("help", "Display help information")                             //
            ("prove", "Create a proof")                                      //
            ("proof-files-basename", "Basename for the .opb and .pbp files", //
                cxxopts::value<string>()->default_value("talent"))           //
            ("stats", "Print solve statistics")                              //
            ;

        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        println(cerr, "Error: {}", e.what());
        println(cerr, "Try {} --help", argv[0]);
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        println("Usage: {} [options] [size]", argv[0]);
        println("");
        cout << options.help() << std::endl;
        return EXIT_SUCCESS;
    }

    int numActors = 5;
    int numScenes = 9;

    vector<int> actorPay = {1, 1, 1, 1, 1};
    vector<int> sceneDuration = {2, 4, 1, 3, 3, 2, 5, 7, 6};
    vector<vector<int>> actorInScene = {
        {1, 1, 0, 1, 0, 1, 1, 0, 1},
        {1, 1, 0, 1, 1, 1, 0, 1, 0},
        {1, 1, 0, 0, 0, 0, 1, 1, 0},
        {1, 0, 0, 0, 1, 1, 0, 0, 1},
        {0, 0, 1, 0, 1, 1, 1, 1, 0}};

    vector<vector<int>> actorsScenes{};

    Problem p;

    auto scene = p.create_integer_variable_vector(numScenes, 0_i, Integer(numScenes - 1), "scene");

    auto slot = p.create_integer_variable_vector(numScenes, 0_i, Integer(numScenes - 1), "slot");

    auto firstSlot = p.create_integer_variable_vector(numActors, 0_i, Integer(numScenes - 1), "firstSlot");
    auto lastSlot = p.create_integer_variable_vector(numActors, 0_i, Integer(numScenes - 1), "lastSlot");
    auto actorWait = p.create_integer_variable_vector(numActors, 0_i, Integer(100), "actorWait");
    WeightedSum idle_expr{};

    for (int a = 0; a < numActors; ++a) {
        actorsScenes.emplace_back();
        for (int s = 0; s < numScenes; ++s) {
            if (actorInScene[a][s]) {
                actorsScenes.back().emplace_back(s);
            }
        }
        auto actorsSlots = p.create_integer_variable_vector(actorsScenes.size(), 0_i, Integer(numScenes - 1), format("actorsSlots_{}_", a));
        for (unsigned int s = 0; s < actorsScenes.size(); s++) {
            p.post_named(Equals{actorsSlots[s], slot[actorsScenes[a][s]]}, format("actor[{}]inScene[{}]", a, actorsScenes[a][s]));
        }
        p.post_named(ArrayMin{actorsSlots, firstSlot[a]}, format("firstSlot_{}_", a));
        p.post_named(ArrayMax{actorsSlots, lastSlot[a]}, format("lastSlot_{}_", a));

        auto wait_expr = WeightedSum{};
        for (int s = 0; s < numScenes; ++s) {
            auto afterFirst = p.create_integer_variable(0_i, 1_i);
            p.post_named(LessThanEqualIff{firstSlot[a], slot[s], afterFirst == 1_i}, format("afterFirst_{}_{}_", a, s));
            auto beforeLast = p.create_integer_variable(0_i, 1_i);
            p.post_named(LessThanEqualIff{slot[s], lastSlot[a], beforeLast == 1_i}, format("beforeLast_{}_{}_", a, s));
            auto onSet = p.create_integer_variable(0_i, 1_i);
            p.post_named(And{{afterFirst, beforeLast}, onSet}, format("onSet_{}_{}_", a, s));

            if (actorInScene[a][s] == 0) {
                wait_expr += Integer(sceneDuration[s]) * onSet;
            }
        }
        wait_expr += -1_i * actorWait[a];
        p.post_named(wait_expr == 0_i, format("wait_{}_", a));
        idle_expr += Integer(actorPay[a]) * actorWait[a];
    }

    p.post_named(Inverse{scene, slot}, "inverse");

    IntegerVariableID idleCost = p.create_integer_variable(0_i, Integer(100), "idleCost");
    idle_expr += -1_i * idleCost;
    p.post_named(idle_expr == 0_i, "idle");
    p.minimise(idleCost);

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "Idle Cost: " << s(idleCost) << "\n";
                return true;
            },
            .branch = branch_with(variable_order::dom_then_deg(scene), value_order::smallest_first())},
        options_vars.contains("prove")
            ? make_optional(ProofOptions{options_vars["proof-files-basename"].as<string>()})
            : nullopt);

    if (options_vars.contains("stats"))
        cout << stats;
    return 0;
}
