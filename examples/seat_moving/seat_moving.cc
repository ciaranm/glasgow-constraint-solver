#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/constraints/logical.hh>

#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <cstdlib>
#include <exception>
#include <iostream>
#include <map>
#include <numeric>
#include <optional>
#include <random>
#include <string>
#include <utility>
#include <vector>

#include <cxxopts.hpp>

#include <examples/benchmark_cli.hh>
#include <examples/dzn.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::map;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::vector;
using std::ranges::shuffle;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
using std::println;
#else
using fmt::format;
using fmt::print;
using fmt::println;
#endif

// Seat moving, a native port of the MiniZinc Challenge 2018 model
// `2018/seat-moving/seat-moving.mzn` (submitted by Toshimitsu Fujiwara).
//
// P people occupy P of S seats. Every person has a start seat and a goal seat,
// and we must schedule a sequence of at most MAX_STEP seating arrangements
// carrying the first into the last. Between two consecutive arrangements a
// person may only change seat if either
//
//   * the seat they move into was empty in the previous arrangement, or
//   * they can carry their luggage (`Can_swap`) and they are swapping directly
//     with whoever previously sat where they are going.
//
// Several people may move in the same step, so long as each move obeys that
// rule and no two people end up in the same seat. We minimise
// `step * P * MAX_STEP + cost`, i.e. lexicographically the number of steps
// actually used and then the total number of person-moves; MAX_STEP is fixed
// by the model as `(2 * S) div (S - P + 1) + 1`, which keeps the horizon short
// when there are many spare seats.
//
// The modelling follows the MiniZinc source directly:
//
//   * `seat[i, s]` is who sits in seat s at step i (0 for an empty seat), and
//     `person[i, p]` is where person p sits at step i. The first and last rows
//     of `seat` are the given Start and Goal, so they are posted as constants,
//     exactly as MiniZinc's flattener resolves them.
//   * The two views are tied together by `seat[i, person[i, p]] = p`, an
//     Element with a *variable* index and a constant result.
//   * `alldifferent_except_0` over each row of `seat`, and the model's
//     redundant `alldifferent` over each row of `person`.
//   * `cost` counts the person-steps that move. We reify `person[i, p] =
//     person[i + 1, p]` once as `same[i][p]` and reuse that single Boolean both
//     for the cost sum and as the guard of the moving constraint; MiniZinc's
//     flattener happens to reify that same condition twice.
//   * "Don't move once everything is in place": `step < i -> seat[i, s] =
//     Goal[s]`, half-reified through a `done[i]` Boolean.
//   * The moving constraint needs `person[i + 1, seat[i, person[i + 1, p]]]`,
//     a doubly nested element whose inner value may be 0 (an empty seat), which
//     is outside `person`'s index set. Rather than MiniZinc's clamp-and-guard
//     rewriting, we index a copy of the `person` row that has been prefixed
//     with the constant 0: an empty seat then yields 0, which can never equal a
//     seat number, so the swap disjunct is false exactly when it should be.
//
// The search deliberately mirrors the model's `seq_search` annotation, because
// the interesting thing about this instance is how deep its find-first search
// goes: first_fail/indomain_min over `person` in row-major order, then the same
// over `seat`, then indomain_split on `step` and on `cost`, then indomain_min
// on `objective`, and finally a dom-then-deg fallback for anything left.
//
// `--all-different gac|vc|not-equals` selects the encoding of the redundant
// alldifferent, as in ortho_latin; `gac`, the default, is what reproduces the
// reference proof shape.

namespace
{
    struct Instance
    {
        string name;
        int seats = 0;                  // S
        int people = 0;                 // P
        vector<int> start;              // Start[1..S], 0 for an empty seat
        vector<int> goal;               // Goal[1..S]
        vector<unsigned char> can_swap; // Can_swap[1..P]
    };

    // MAX_STEP = (2 * S) div (S - P + 1) + 1, as in the .mzn.
    [[nodiscard]] auto max_step(const Instance & instance) -> int
    {
        return (2 * instance.seats) / (instance.seats - instance.people + 1) + 1;
    }

    // Reject anything the model silently assumes: Start and Goal must be
    // seatings, i.e. each person appears exactly once and every other entry is
    // an empty seat.
    [[nodiscard]] auto validate(const Instance & instance) -> optional<string>
    {
        if (instance.people < 1 || instance.seats < instance.people)
            return format("need 1 <= P <= S, got S = {} and P = {}", instance.seats, instance.people);
        if (static_cast<int>(instance.can_swap.size()) != instance.people)
            return format("Can_swap has {} entries, expected P = {}", instance.can_swap.size(), instance.people);

        for (const auto & [what, array] : {pair{"Start", &instance.start}, pair{"Goal", &instance.goal}}) {
            if (static_cast<int>(array->size()) != instance.seats)
                return format("{} has {} entries, expected S = {}", what, array->size(), instance.seats);
            vector<int> seen(instance.people + 1, 0);
            for (auto & v : *array) {
                if (v < 0 || v > instance.people)
                    return format("{} contains {}, which is not a person in 0..{}", what, v, instance.people);
                ++seen[v];
            }
            for (int p = 1; p <= instance.people; ++p)
                if (1 != seen[p])
                    return format("{} seats person {} {} times, expected exactly once", what, p, seen[p]);
        }

        return nullopt;
    }

    // The five MiniZinc Challenge 2018 instances, verbatim from
    // 2018/seat-moving/*.dzn. Embedding them keeps the Challenge data
    // reproducible from this repository alone. `sm-10-12-00` is the one used as
    // a proof benchmark: MAX_STEP is 9 there, which is what makes its
    // find-first search deep.
    [[nodiscard]] auto built_in_instances() -> map<string, Instance>
    {
        map<string, Instance> instances;

        // A small instance for the default run and for the proof-logging test:
        // three people, five seats, MAX_STEP = 4.
        instances.emplace("small", Instance{"small", 5, 3, {1, 0, 2, 0, 3}, {3, 2, 0, 1, 0}, {1, 0, 1}});

        instances.emplace("sm-10-12-00",
            Instance{"sm-10-12-00", 12, 10,            //
                {8, 4, 0, 6, 0, 2, 1, 3, 5, 7, 9, 10}, //
                {0, 4, 6, 8, 0, 7, 3, 5, 9, 10, 1, 2}, //
                {0, 1, 1, 0, 1, 0, 1, 0, 1, 0}});

        instances.emplace("sm-10-20-05",
            Instance{"sm-10-20-05", 20, 10,                                    //
                {0, 10, 0, 2, 0, 0, 7, 9, 0, 0, 0, 4, 3, 5, 1, 6, 8, 0, 0, 0}, //
                {0, 7, 4, 0, 6, 10, 0, 0, 5, 0, 0, 0, 2, 1, 0, 8, 0, 9, 0, 3}, //
                {1, 0, 0, 0, 1, 1, 0, 1, 1, 0}});

        instances.emplace("sm-15-12-00",
            Instance{"sm-15-12-00", 18, 15,                                   //
                {8, 0, 15, 11, 14, 1, 13, 9, 0, 7, 4, 10, 2, 0, 12, 5, 6, 3}, //
                {11, 13, 0, 8, 2, 1, 6, 0, 3, 10, 15, 5, 4, 14, 0, 7, 9, 12}, //
                {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1}});

        instances.emplace("sm-15-20-00",
            Instance{"sm-15-20-00", 30, 15,                                                                       //
                {0, 0, 0, 0, 11, 12, 0, 3, 0, 0, 0, 15, 0, 1, 0, 13, 0, 2, 0, 6, 0, 14, 7, 0, 4, 8, 0, 9, 10, 5}, //
                {1, 0, 0, 0, 5, 0, 0, 0, 8, 12, 0, 0, 9, 13, 0, 14, 0, 10, 15, 0, 0, 4, 6, 7, 0, 3, 0, 0, 11, 2}, //
                {1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0}});

        instances.emplace("sm-20-20-00",
            Instance{"sm-20-20-00", 40, 20, //
                {0, 0, 12, 0, 0, 2, 16, 7, 0, 18, 0, 0, 0, 17, 0, 4, 6, 11, 10, 0, 0, 0, 0, 19, 0, 15, 0, 3, 0, 0, 13, 0, 14, 0, 8, 9, 5, 1, 0,
                    20}, //
                {0, 19, 18, 5, 2, 0, 7, 0, 1, 3, 0, 0, 0, 0, 17, 13, 4, 9, 0, 0, 14, 0, 0, 0, 8, 6, 15, 16, 12, 10, 0, 0, 0, 20, 0, 0, 0, 0, 0,
                    11}, //
                {0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0}});

        return instances;
    }

    // Read a MiniZinc Challenge 2018 seat-moving data file, which assigns S, P,
    // Start, Goal and Can_swap. Everything the file says about sizes is checked
    // by validate(), not here, so a short Start is a complaint about the
    // instance rather than about the file.
    [[nodiscard]] auto read_dzn(const string & path) -> optional<Instance>
    {
        try {
            auto data = dzn::read(path);

            Instance instance{path, 0, 0, {}, {}, {}};
            instance.seats = static_cast<int>(data.integer("S"));
            instance.people = static_cast<int>(data.integer("P"));

            for (const auto & [name, into] : {pair{"Start", &instance.start}, pair{"Goal", &instance.goal}})
                for (auto seat : data.integers(name))
                    into->push_back(static_cast<int>(seat));

            for (auto swaps : data.bools("Can_swap"))
                instance.can_swap.push_back(swaps ? 1 : 0);

            return instance;
        }
        catch (const std::exception & e) {
            println(cerr, "Error reading the instance: {}", e.what());
            return nullopt;
        }
    }

    // A random instance: seat the people in a random subset of the seats, twice
    // over, and toss a coin for each person's Can_swap flag. Every instance
    // generated this way is a legal seating problem, though not necessarily
    // solvable within MAX_STEP.
    [[nodiscard]] auto random_instance(int seats, int people, unsigned seed) -> Instance
    {
        mt19937 rng(seed);

        auto seating = [&]() {
            vector<int> who(seats, 0);
            std::iota(who.begin(), who.begin() + people, 1);
            shuffle(who, rng);
            return who;
        };

        Instance instance{format("random-{}-{}-{}", seats, people, seed), seats, people, seating(), seating(), {}};
        for (int p = 0; p < people; ++p)
            instance.can_swap.push_back(static_cast<unsigned char>(rng() % 2));
        return instance;
    }

    auto solve_instance(const Instance & instance, const string & all_different_mode, bool optimise, bool print_solution,
        const optional<string> & proof_basename, double timeout) -> Stats
    {
        const auto n_seats = instance.seats, n_people = instance.people, n_steps = max_step(instance);

        Problem p;

        // Post the model's redundant alldifferent over one row of person with the
        // chosen encoding, spelled as in ortho_latin: 'vc' and 'not-equals' do the
        // same (non-GAC) pruning as each other, and 'gac' prunes more. The
        // alldifferent_except_0 over seat is unaffected --- gcs has only the one
        // AllDifferentExcept --- so this switch changes propagation strength
        // without changing the OPB encoding at all, which is what makes it a
        // usable control pair.
        auto post_all_different = [&](const vector<IntegerVariableID> & vars) {
            if (all_different_mode == "gac")
                p.post(AllDifferent{vars});
            else if (all_different_mode == "vc")
                p.post(AllDifferent{vars} //
                        .with_consistency(consistency::VC{}));
            else
                for (unsigned i = 0; i < vars.size(); ++i)
                    for (unsigned j = i + 1; j < vars.size(); ++j)
                        p.post(NotEquals{vars[i], vars[j]});
        };

        // seat[i][s]: who is in seat s at step i, or 0 for an empty seat. The
        // first and last steps are given, so they are constants rather than
        // variables --- which is also what MiniZinc's flattener does to them.
        vector<vector<IntegerVariableID>> seat;
        for (int i = 0; i < n_steps; ++i) {
            if (0 == i || n_steps - 1 == i) {
                const auto & fixed = (0 == i) ? instance.start : instance.goal;
                vector<IntegerVariableID> row;
                for (int s = 0; s < n_seats; ++s)
                    row.push_back(constant_variable(Integer(fixed[s])));
                seat.push_back(std::move(row));
            }
            else
                seat.push_back(p.create_integer_variable_vector(n_seats, 0_i, Integer(n_people), format("seat[{}]", i + 1)));
        }

        // person[i][q]: which seat person q + 1 is in at step i.
        vector<vector<IntegerVariableID>> person;
        for (int i = 0; i < n_steps; ++i)
            person.push_back(p.create_integer_variable_vector(n_people, 1_i, Integer(n_seats), format("person[{}]", i + 1)));

        // Tie the two views together, and forbid double-seating. The
        // alldifferent over person is the .mzn's redundant_constraint.
        for (int i = 0; i < n_steps; ++i) {
            for (int q = 0; q < n_people; ++q)
                p.post(Element{constant_variable(Integer(q + 1)), pair{person[i][q], 1_i}, seat[i]});
            p.post(AllDifferentExceptZero{seat[i]});
            post_all_different(person[i]);
        }

        // same[i][q] holds exactly when person q + 1 does not move between step
        // i + 1 and step i + 2, so cost, the number of person-moves, is
        // (n_steps - 1) * n_people minus their sum.
        vector<vector<IntegerVariableID>> same;
        WeightedSum cost_sum;
        for (int i = 0; i + 1 < n_steps; ++i) {
            same.push_back(p.create_integer_variable_vector(n_people, 0_i, 1_i, format("same[{}]", i + 1)));
            for (int q = 0; q < n_people; ++q) {
                p.post(EqualsIff{person[i][q], person[i + 1][q], same[i][q] == 1_i});
                cost_sum += 1_i * same[i][q];
            }
        }

        auto cost = p.create_integer_variable(0_i, Integer((n_steps - 1) * n_people), "cost");
        cost_sum += 1_i * cost;
        p.post(cost_sum == Integer((n_steps - 1) * n_people));

        // objective = step * P * MAX_STEP + cost, i.e. steps used first and
        // moves as a tie-break. The declared upper bound is the .mzn's,
        // `ub(step) * ub(cost) + ub(cost)` for the *declared* cost bound.
        const auto step_weight = n_people * n_steps;
        auto step = p.create_integer_variable(0_i, Integer(n_steps), "step");
        auto objective = p.create_integer_variable(0_i, Integer(n_steps * step_weight + step_weight), "objective");
        p.post(WeightedSum{} + Integer(step_weight) * step + 1_i * cost + -1_i * objective == 0_i);

        // Don't move after all seats are fixed: step < i implies row i is Goal.
        // Row n_steps is Goal by construction, and row 1 is Start, for which
        // the implication is just a bound on step.
        for (int i = 1; i < n_steps; ++i) {
            if (1 == i) {
                if (instance.start != instance.goal)
                    p.post(GreaterThanEqual{step, constant_variable(1_i)});
                continue;
            }

            auto done = p.create_integer_variable(0_i, 1_i, format("done[{}]", i));
            p.post(LessThanEqualIff{step, constant_variable(Integer(i - 1)), done == 1_i});
            for (int s = 0; s < n_seats; ++s)
                p.post(EqualsIf{seat[i - 1][s], constant_variable(Integer(instance.goal[s])), done == 1_i});
        }

        // The moving constraint: a person who moves must either be moving into a
        // seat that was empty, or swapping directly with whoever was in it.
        for (int i = 0; i + 1 < n_steps; ++i) {
            // The next step's person row, prefixed with a constant 0 so that it
            // can be indexed by an occupant of 0, meaning "the seat was empty".
            // Person positions are seats, numbered from 1, so a lookup that
            // lands on the 0 entry can never satisfy the swap equality.
            vector<IntegerVariableID> next_seat_of;
            next_seat_of.push_back(constant_variable(0_i));
            for (int q = 0; q < n_people; ++q)
                next_seat_of.push_back(person[i + 1][q]);

            for (int q = 0; q < n_people; ++q) {
                // Who was sitting, at step i + 1, where person q + 1 will sit at
                // step i + 2.
                auto occupant = p.create_integer_variable(0_i, Integer(n_people), format("occupant[{}][{}]", i + 1, q + 1));
                p.post(Element{occupant, pair{person[i + 1][q], 1_i}, seat[i]});

                auto vacated = p.create_integer_variable(0_i, 1_i, format("vacated[{}][{}]", i + 1, q + 1));
                p.post(EqualsIff{occupant, constant_variable(0_i), vacated == 1_i});

                if (instance.can_swap[q]) {
                    // Where that occupant goes next: a swap is exactly the case
                    // where they go to the seat person q + 1 is leaving.
                    auto partner_seat = p.create_integer_variable(0_i, Integer(n_seats), format("partnerSeat[{}][{}]", i + 1, q + 1));
                    p.post(Element{partner_seat, pair{occupant, 0_i}, next_seat_of});

                    auto swapped = p.create_integer_variable(0_i, 1_i, format("swapped[{}][{}]", i + 1, q + 1));
                    p.post(EqualsIff{person[i][q], partner_seat, swapped == 1_i});

                    p.post(Or{vector<IntegerVariableID>{same[i][q], swapped, vacated}});
                }
                else
                    p.post(Or{vector<IntegerVariableID>{same[i][q], vacated}});
            }
        }

        // The objective is declared even when we are only after the first
        // solution, matching `fzn-glasgow -n 1` on the flattened model: the
        // objective bound only ever constrains search *after* a solution, so
        // this does not change the find-first tree, but it does mean the proof
        // concludes with the same bounds claim the reference run makes.
        p.minimise(objective);

        // Reproduce the .mzn's seq_search annotation. The order within each
        // int_search matters: first_fail breaks ties on position in the array,
        // and array1d() flattens row-major.
        vector<IntegerVariableID> person_flat, seat_flat;
        for (int i = 0; i < n_steps; ++i)
            for (int q = 0; q < n_people; ++q)
                person_flat.push_back(person[i][q]);
        for (int i = 0; i < n_steps; ++i)
            for (int s = 0; s < n_seats; ++s)
                seat_flat.push_back(seat[i][s]);

        vector<BranchHeuristic> searches{branch_with(variable_order::dom(person_flat), value_order::smallest_in()),
            branch_with(variable_order::dom(seat_flat), value_order::smallest_in()),
            branch_with(variable_order::dom(vector<IntegerVariableID>{step}), value_order::split_smallest_first()),
            branch_with(variable_order::dom(vector<IntegerVariableID>{cost}), value_order::split_smallest_first()),
            branch_with(variable_order::dom(vector<IntegerVariableID>{objective}), value_order::smallest_in()),
            // fzn-glasgow appends a dom-then-deg fallback after whatever the
            // search annotation asked for, to catch anything it does not name.
            branch_with(variable_order::dom_then_deg(p), value_order::smallest_first())};

        auto branch = searches.front();
        for (size_t s = 1; s < searches.size(); ++s)
            branch = branch_sequence(branch, searches[s]);

        return bench::solve_with_timeout(timeout, p, //
            SolveCallbacks{                          //
                .solution = [&](const CurrentState & s) -> bool {
                    if (print_solution) {
                        for (int i = 0; i < n_steps; ++i) {
                            print("step {:2}:", i + 1);
                            for (int seat_index = 0; seat_index < n_seats; ++seat_index)
                                print(" {:2}", s(seat[i][seat_index]).raw_value);
                            println("");
                        }
                        println("step = {}, cost = {}, objective = {}", s(step).raw_value, s(cost).raw_value, s(objective).raw_value);
                        println("");
                    }
                    return optimise;
                },
                .branch = branch},
            proof_basename ? make_optional(ProofOptions{*proof_basename}) : nullopt);
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Seat Moving Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")                                                                     //
            ("help", "Display help information")                                                                   //
            ("prove", "Create a proof")                                                                            //
            ("proof-files-basename", "Basename for the .opb and .pbp files",                                       //
                cxxopts::value<string>()->default_value("seat_moving"))                                            //
            ("instance", "Built-in instance to solve", cxxopts::value<string>()->default_value("small"))           //
            ("dzn", "Solve a MiniZinc Challenge 2018 seat-moving .dzn instance instead", cxxopts::value<string>()) //
            ("seats", "Generate a random instance with this many seats instead", cxxopts::value<int>())            //
            ("people", "How many people to seat in a random instance", cxxopts::value<int>())                      //
            ("seed", "Seed for a random instance", cxxopts::value<int>()->default_value("0"))                      //
            ("all-different",
                "All-different encoding to use for the redundant alldifferent over person: "           //
                "'gac' (the default), 'vc', or 'not-equals' (the not-equals clique)",                  //
                cxxopts::value<string>()->default_value("gac"))                                        //
            ("optimise", "Minimise the objective, rather than stopping at the first solution")         //
            ("quiet", "Do not print solutions")                                                        //
            ("timeout", "Abort after this many seconds", cxxopts::value<double>()->default_value("0")) //
            ("stats", "Print solve statistics");

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
        cout << options.help() << endl;
        println("Built-in instances:");
        for (const auto & [name, instance] : built_in_instances())
            println("    {:12} S = {}, P = {}, MAX_STEP = {}", name, instance.seats, instance.people, max_step(instance));
        return EXIT_SUCCESS;
    }

    const string all_different_mode = options_vars["all-different"].as<string>();
    if (all_different_mode != "gac" && all_different_mode != "vc" && all_different_mode != "not-equals") {
        println(cerr, "Error: --all-different must be 'gac', 'vc', or 'not-equals'.");
        return EXIT_FAILURE;
    }

    optional<Instance> instance;
    if (options_vars.contains("dzn")) {
        instance = read_dzn(options_vars["dzn"].as<string>());
        if (! instance)
            return EXIT_FAILURE;
    }
    else if (options_vars.contains("seats") || options_vars.contains("people")) {
        if (! (options_vars.contains("seats") && options_vars.contains("people"))) {
            println(cerr, "Error: --seats and --people must be given together");
            return EXIT_FAILURE;
        }
        instance =
            random_instance(options_vars["seats"].as<int>(), options_vars["people"].as<int>(), static_cast<unsigned>(options_vars["seed"].as<int>()));
    }
    else {
        auto instances = built_in_instances();
        auto name = options_vars["instance"].as<string>();
        auto found = instances.find(name);
        if (found == instances.end()) {
            print(cerr, "Unknown instance '{}'. Available:", name);
            for (const auto & [key, _] : instances)
                print(cerr, " {}", key);
            println(cerr, "");
            return EXIT_FAILURE;
        }
        instance = found->second;
    }

    if (auto problem_with_instance = validate(*instance)) {
        println(cerr, "Error: bad instance {}: {}", instance->name, *problem_with_instance);
        return EXIT_FAILURE;
    }

    auto stats = solve_instance(*instance, //
        all_different_mode,                //
        options_vars.contains("optimise"), //
        ! options_vars.contains("quiet"),  //
        options_vars.contains("prove")     //
            ? make_optional(options_vars["proof-files-basename"].as<string>())
            : nullopt,
        options_vars["timeout"].as<double>());

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
