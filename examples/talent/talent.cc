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

using namespace gcs;
using std::cerr;
using std::cout;
using std::make_optional;
using std::nullopt;
using std::vector;

using fmt::print;
using fmt::println;


int main(int argc, char * argv[])
{
    cxxopts::Options options("Talent Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options()
            ("help", "Display help information")
            ("prove", "Create a proof");

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
        auto actorsSlots = p.create_integer_variable_vector(actorsScenes.size(), 0_i, Integer(numScenes - 1), "actorsSlots");
        for (unsigned int s = 0; s < actorsScenes.size(); s++) {
            p.post(Equals{actorsSlots[s], slot[actorsScenes[a][s]]});
        }
        p.post(ArrayMin{actorsSlots, firstSlot[a]});
        p.post(ArrayMax{actorsSlots, lastSlot[a]});

        auto wait_expr = WeightedSum{};
        for (int s = 0; s < numScenes; ++s) {
            auto afterFirst = p.create_integer_variable(0_i, 1_i);
            p.post(LessThanEqualIff{firstSlot[a], slot[s], afterFirst == 1_i});
            auto beforeLast = p.create_integer_variable(0_i, 1_i);
            p.post(LessThanEqualIff{slot[s], lastSlot[a], beforeLast == 1_i});
            auto onSet = p.create_integer_variable(0_i, 1_i);
            p.post(And{{afterFirst, beforeLast}, onSet});

            if (actorInScene[a][s] == 0) {
                wait_expr += Integer(sceneDuration[s]) * onSet;
            }
        }
        wait_expr += -1_i * actorWait[a];
        p.post(wait_expr == 0_i);
        idle_expr += Integer(actorPay[a]) * actorWait[a];
    }

    p.post(Inverse{scene, slot});

    IntegerVariableID idleCost = p.create_integer_variable(0_i, Integer(100), "idleCost");
    idle_expr += -1_i * idleCost;
    p.post(idle_expr == 0_i);
    p.minimise(idleCost);

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "Idle Cost: " << s(idleCost) << "\n";
                return true;
            },
            .branch = branch_with(variable_order::dom_then_deg(scene), value_order::smallest_first())},
        options_vars.contains("prove") ? make_optional(ProofOptions{"talent"}) : nullopt);

    cout << stats;
    return 0;
}
