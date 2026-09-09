// Driver for benchmarking the order-encoding-deletion proof-logging change
// (GCS_DELETE_ORDER_ENCODING=literals). It builds a scalable "windowed packing"
// problem whose proof is EQ-FREE and whose search introduces many integer order
// literals (ge atoms) over LARGE-domain variables that are reasoned over
// LOCALLY-NARROW ranges -- exactly the regime the deletion optimisation targets.
//
// Two ingredients keep the proof eq-free and the ge chains long:
//   * Variables have a large domain [0, D] (D = --domain, up to a few thousand),
//     so the order encoding chain is long.
//   * Branching is a bound SPLIT (value_order::split_smallest_first ->
//     `var <= v`, a ge literal), NOT a value assignment (`var == v`, an eq
//     atom). See gcs/search_heuristics.hh. An eq-minting `smallest` value order
//     is offered ONLY for building eq-heavy CONTROL instances.
//   * Refutation (--unsat) finds NO solution, so NO solution-blocking clause
//     (solx) is ever emitted, so there are NO eq atoms at all -- the cleanest
//     case. First-solution SAT (default) emits at most one solx (a handful of eq
//     atoms). Optimisation (--optimise) emits one solx per improving solution.
//
// Each variable is confined to a narrow window [r_i, r_i + width] inside the big
// domain via two single-variable linear bound constraints (LinearGreaterThanEqual
// / LinearLessThanEqual -- both propagate on bounds, i.e. ge, never eq). The
// windows are spread across [0, D] so different variables exercise different
// stretches of the (long) order chain, and coupling constraints make the packing
// contended so genuine SEARCH (thousands of recursions), not propagation alone,
// is needed.
//
// Coupling is selectable:
//   --problem linear     : a bank of budget (<=) and demand (>=) inequalities
//                          over random overlapping subsets (mismatched coeffs).
//   --problem pairwise   : every pairwise sum x_i + x_j >= ceil(lo*D) plus a
//                          grand-total budget. UNSAT-needing-search by
//                          construction: no single constraint is infeasible, so
//                          bounds propagation cannot refute and the whole tree
//                          must be searched. This is the mode that exercises the
//                          deletion win on this build.
//   --problem cumulative : a Cumulative resource over the tasks (starts = the
//                          large-domain vars), plus release/deadline windows.
//
// Canonical win invocation (the reproducible order-encoding-deletion signal):
//
//   order_deletion_bench --problem pairwise --size 8 --domain D --window D \
//       --tightness 90 --unsat
//
// For the MAXIMUM win, also set GCS_DELETE_ORDER_ENCODING_MIN_CHAIN=0: the default
// chain-length gate (16) holds each variable's first thresholds resident, trading a
// slice of the synthetic win for strictly-no-harm on short-chain models.
//
// with D swept over e.g. 250 / 500 / 1000 / 2000 for the domain curve. `--window
// D` disables the per-variable windows (otherwise the instance root-refutes) and
// `--tightness 90` sits just inside UNSAT so the tree must be searched rather than
// bounds-refuted. Only `pairwise` searches deeply on this build: `linear` and
// `cumulative` with their defaults root-refute in a few recursions (~0.01 s
// verify, no signal), so they serve only as cheap controls, not win cases.
//
// A proof-only change: recursions / propagations / solutions MUST be identical
// with the mode off vs on. This driver prints them via --stats so the harness
// can assert that.
//
// Standard flags: --prove --stats --proof-files-basename.

#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <optional>
#include <random>
#include <string>
#include <vector>

#include <cxxopts.hpp>

#include <version>
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#endif

using namespace gcs;

using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::size_t;
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

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("order_deletion_bench", "Eq-free, long-ge-chain, search-heavy driver for the order-encoding-deletion proof change");
    options.add_options()                                                                                                                 //
        ("problem", "Coupling: linear | pairwise | cumulative", cxxopts::value<string>()->default_value("linear"))                        //
        ("size", "Number of variables / tasks", cxxopts::value<int>()->default_value("16"))                                               //
        ("domain", "Domain is 0..D (large -> long ge chains)", cxxopts::value<int>()->default_value("1000"))                              //
        ("window", "Narrow-window width per variable (0 = full domain)", cxxopts::value<int>()->default_value("0"))                       //
        ("sums", "linear: number of coupling inequalities (0 = 2*size)", cxxopts::value<int>()->default_value("0"))                       //
        ("sumlen", "linear: variables per inequality (0 = size)", cxxopts::value<int>()->default_value("0"))                              //
        ("big", "linear: big coefficients per sum (0 = all unit coeffs -> cheap propagation)", cxxopts::value<int>()->default_value("0")) //
        ("demand-frac", "linear: fraction (percent) of inequalities that are >= demands", cxxopts::value<int>()->default_value("35"))     //
        ("tightness", "Budget/capacity tightness, percent of worst case", cxxopts::value<int>()->default_value("55"))                     //
        ("cap-tasks", "cumulative: resource capacity", cxxopts::value<int>()->default_value("2"))                                         //
        ("unsat", "Force infeasibility (refute with NO solutions -> fully eq-free)")                                                      //
        ("optimise", "Minimise an objective instead of first-solution SAT")                                                               //
        ("var-order", "Variable order: in_order | dom | dom_then_deg", cxxopts::value<string>()->default_value("dom_then_deg"))           //
        ("value-order", "Value order: split_smallest | split_largest | smallest(EQ control)",
            cxxopts::value<string>()->default_value("split_smallest"))                                                                    //
        ("seed", "RNG seed", cxxopts::value<unsigned>()->default_value("1"))                                                              //
        ("prove", "Create a proof")                                                                                                       //
        ("proof-files-basename", "Basename for the .opb and .pbp files", cxxopts::value<string>()->default_value("order_deletion_bench")) //
        ("stats", "Print solve statistics")                                                                                               //
        ("help", "Display help information");                                                                                             //

    cxxopts::ParseResult o;
    try {
        o = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        println(stderr, "Error: {}", e.what());
        return EXIT_FAILURE;
    }
    if (o.contains("help")) {
        print("{}", options.help());
        return EXIT_SUCCESS;
    }

    const string problem = o["problem"].as<string>();
    const int n = o["size"].as<int>();
    const int D = o["domain"].as<int>();
    int window = o["window"].as<int>();
    int sums = o["sums"].as<int>();
    int sumlen = o["sumlen"].as<int>();
    const int big_coeffs = o["big"].as<int>();
    const int demand_frac = o["demand-frac"].as<int>();
    const int tightness = o["tightness"].as<int>();
    const int cap_tasks = o["cap-tasks"].as<int>();
    const bool unsat = o.contains("unsat");
    const bool optimise = o.contains("optimise");
    const string var_order = o["var-order"].as<string>();
    const string value_order = o["value-order"].as<string>();
    const unsigned seed = o["seed"].as<unsigned>();

    if (sums <= 0)
        sums = 2 * n;
    if (sumlen <= 0)
        sumlen = n;
    if (sumlen > n)
        sumlen = n;

    mt19937 rng(seed);

    Problem p;
    auto x = p.create_integer_variable_vector(static_cast<size_t>(n), 0_i, Integer{D}, "x");

    // Narrow windows spread across the big domain: variable i is confined to
    // [r_i, r_i + width]. With window == 0 we default the width so the union of
    // windows tiles the domain with modest overlap (contended but not trivial).
    if (window <= 0)
        window = std::max(2, (2 * D) / std::max(1, n));
    vector<int> release(n);
    {
        const int span = std::max(1, D - window);
        for (int i = 0; i < n; ++i) {
            // Deterministic spread plus a small jitter, so windows overlap.
            int base = (n > 1) ? (i * span) / (n - 1) : 0;
            int jitter = uniform_int_distribution<int>(0, std::max(0, window / 2))(rng);
            int r = std::min(span, base + jitter);
            release[i] = r;
            p.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * x[i], Integer{r}});
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[i], Integer{r + window}});
        }
    }

    IntegerVariableID objective = x[0];

    if (problem == "linear") {
        // A bank of budget (<=) and demand (>=) inequalities over random
        // overlapping subsets, with a few big coefficients per sum (mismatched
        // spread). Budgets cap weighted sums; demands floor them. Overlap on
        // shared variables makes satisfying all of them contended; --unsat
        // pushes budgets down / demands up until the whole tree must be
        // refuted.
        uniform_int_distribution<int> pick(0, n - 1);
        for (int c = 0; c < sums; ++c) {
            vector<bool> used(n, false);
            WeightedSum sum;
            long long worst = 0;
            int placed = 0, big = 0;
            while (placed < sumlen) {
                int j = pick(rng);
                if (used[j])
                    continue;
                used[j] = true;
                Integer coeff = (big < big_coeffs) ? Integer{7 + big * 5} : 1_i;
                if (big < big_coeffs)
                    ++big;
                sum += coeff * x[j];
                worst += coeff.raw_value * D;
                ++placed;
            }
            const bool is_demand = (uniform_int_distribution<int>(0, 99)(rng) < demand_frac);
            if (is_demand) {
                // Demand floor: a bit tighter under --unsat so budgets and
                // demands over shared variables collide.
                long long floor = unsat ? (worst * (tightness + 20)) / 100 : (worst * (tightness - 15)) / 100;
                if (floor < 0)
                    floor = 0;
                p.post(LinearGreaterThanEqual{sum, Integer{floor}});
            }
            else {
                long long budget = (worst * tightness) / 100;
                p.post(LinearLessThanEqual{sum, Integer{budget}});
            }
        }
        objective = x[0];
    }
    else if (problem == "pairwise") {
        // The canonical eq-free UNSAT-needing-search structure, scaled: every
        // pairwise sum x_i + x_j >= ceil(lo*D), and the grand total <= hi*D.
        // Summing the C(n,2) pairwise constraints forces total >= n*lo*D/2, so
        // the instance is UNSAT whenever hi < n*lo/2, yet no single constraint
        // is infeasible -- bounds propagation cannot refute it, the solver must
        // branch. Unit coefficients keep per-propagation proofs cheap. lo/hi are
        // derived from --tightness so the structure stays UNSAT across sizes:
        // lo = 1.4, hi = n*lo/2 * (tightness/100) < n*lo/2.
        const double lo = 1.4;
        const long long pair_rhs = static_cast<long long>(lo * D + 0.9999);
        const long long total_rhs = static_cast<long long>((static_cast<double>(n) * lo / 2.0) * D * (tightness / 100.0));
        for (int i = 0; i < n; ++i)
            for (int j = i + 1; j < n; ++j)
                p.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * x[i] + 1_i * x[j], Integer{pair_rhs}});
        WeightedSum tot;
        for (int i = 0; i < n; ++i)
            tot += 1_i * x[i];
        p.post(LinearLessThanEqual{tot, Integer{total_rhs}});
        objective = x[0];
    }
    else if (problem == "cumulative") {
        // Tasks share a resource of capacity cap_tasks over the horizon D.
        // starts = the large-domain vars x; lengths/heights chosen so the
        // packing is tight (total load near capacity*horizon). Windows above
        // act as release/deadline pins. --unsat shrinks the effective horizon
        // (via a global deadline) so the tasks cannot all be packed.
        vector<Integer> lengths(n, 0_i), heights(n, 0_i);
        uniform_int_distribution<int> len_pick(std::max(1, D / (4 * std::max(1, n))), std::max(2, D / (2 * std::max(1, n))));
        for (int i = 0; i < n; ++i) {
            lengths[i] = Integer{len_pick(rng)};
            heights[i] = 1_i;
        }
        p.post(Cumulative{x, lengths, heights, Integer{cap_tasks}});

        // A global deadline couples all tasks: every task must finish by
        // `deadline`. Under --unsat the deadline is tightened below what the
        // capacity permits, forcing a refutation.
        long long total_len = 0;
        for (auto & l : lengths)
            total_len += l.raw_value;
        long long need = (total_len + cap_tasks - 1) / cap_tasks; // area lower bound on makespan
        long long deadline = unsat ? (need * (100 - (100 - tightness))) / 100 : (need * (200 - tightness)) / 100;
        if (deadline < 1)
            deadline = 1;
        if (deadline > D)
            deadline = D;
        for (int i = 0; i < n; ++i)
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[i], Integer{deadline - lengths[i].raw_value}});

        objective = x[0];
    }
    else {
        println(stderr, "Unknown --problem '{}' (want linear | pairwise | cumulative)", problem);
        return EXIT_FAILURE;
    }

    // Objective for --optimise: minimise the sum of positions (a proxy for a
    // compact packing). Uses a fresh variable tied by a linear equality-free
    // pair of inequalities is overkill; a single objective variable coupled by
    // a >= over the sum suffices for a minimisation direction.
    if (optimise) {
        auto obj = p.create_integer_variable(0_i, Integer{static_cast<long long>(n) * D}, "obj");
        WeightedSum tot;
        for (int i = 0; i < n; ++i)
            tot += 1_i * x[i];
        // obj >= sum(x)  =>  minimising obj minimises the packing spread.
        tot += -1_i * obj;
        p.post(LinearLessThanEqual{tot, 0_i}); // sum(x) - obj <= 0  i.e. obj >= sum(x)
        p.minimise(obj);
        objective = obj;
    }
    (void)objective;

    // Branching. Value order split_smallest_first => `var <= v` (ge). The
    // eq-minting `smallest` is offered only for eq-heavy control instances.
    BranchValueGenerator values = value_order == "split_largest" ? value_order::split_largest_first()
        : value_order == "smallest"                              ? value_order::smallest_first()
                                                                 : value_order::split_smallest_first();

    BranchVariableHeuristic vars = var_order == "in_order" ? variable_order::in_order(vector<IntegerVariableID>{x.begin(), x.end()})
        : var_order == "dom"                               ? variable_order::dom(p)
                                                           : variable_order::dom_then_deg(p);

    unsigned long long solutions = 0;
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                           ++solutions;
                           // First-solution SAT stops immediately; optimise keeps going
                           // for improving solutions; unsat never gets here.
                           return optimise;
                       },
            .branch = branch_with(vars, values)},
        o.contains("prove") ? make_optional<ProofOptions>(o["proof-files-basename"].as<string>()) : nullopt);

    println("problem={} size={} domain=0..{} window={} tightness={} unsat={} optimise={} var_order={} value_order={} seed={}", problem, n, D, window,
        tightness, unsat, optimise, var_order, value_order, seed);
    if (o.contains("stats"))
        print("{}", stats);
    else
        println("recursions: {}\npropagations: {}\nsolutions: {}", stats.recursions, stats.propagations, stats.solutions);

    return EXIT_SUCCESS;
}
