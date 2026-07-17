// Directed test for the conflict-matching upper-bound propagator of MinDistance
// (paper Section 4.4, Algorithm 1). It posts the verified prototype instance --
// 5 sites with D[0,1] = D[2,3] = 3 and all other off-diagonal distances 5, and
// p = 4 selected points -- for which the matching {(0,1),(2,3)} is the ONLY
// reason z can be pruned below 5: the pairwise forward/support bounds never
// tighten past 5 here (every site still has a distance-5 partner). So observing
// z's root upper bound drop to 4 (or the node fail when z is pinned to 5) proves
// the matching bound fired, and the accompanying proof exercises the counting
// derivation end to end.

#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/min_distance.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <string>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::test_innards;

using std::cerr;
using std::make_optional;
using std::nullopt;
using std::optional;
using std::string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

namespace
{
    auto prototype_matrix() -> MinDistance::Matrix
    {
        const int n = 5;
        MinDistance::Matrix d(n, vector<Integer>(n, 5_i));
        for (int a = 0; a < n; ++a)
            d[a][a] = 0_i;
        d[0][1] = d[1][0] = 3_i;
        d[2][3] = d[3][2] = 3_i;
        return d;
    }

    // Solve the instance and report: whether it had any solution, the recursion
    // count, and (via a trace callback on the first node) z's upper bound at the
    // root after propagation. With proofs on, the proof is written and veripb-run.
    struct Probe
    {
        bool has_solution = false;
        long long recursions = 0;
        int root_z_upper = -1;
        optional<int> best_z;
        bool verified = true;
    };

    auto solve_probe(MinDistancePropagation mode, int z_lo, int z_hi, bool proofs, const string & tag) -> Probe
    {
        Problem problem;
        auto d = prototype_matrix();
        auto x = problem.create_integer_variable_vector(4, 0_i, 4_i, "x");
        auto z = problem.create_integer_variable(Integer{z_lo}, Integer{z_hi}, "z");
        problem.post(MinDistance{x, z, d, nullopt, mode});
        problem.maximise(z);

        vector<IntegerVariableID> branch_vars = x;
        branch_vars.push_back(z);

        Probe probe;
        bool first_node = true;

        auto proof_name = proofs ? make_optional("min_distance_matching_test_" + tag) : nullopt;
        optional<ProofOptions> proof_opts = proof_name ? make_optional(ProofOptions{*proof_name}) : nullopt;

        auto stats = solve_with(problem,
            SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                               probe.has_solution = true;
                               probe.best_z = static_cast<int>(s(z).raw_value);
                               return true;
                           },
                .trace = [&](const CurrentState & s) -> bool {
                    if (first_node) {
                        probe.root_z_upper = static_cast<int>(s.upper_bound(z).raw_value);
                        first_node = false;
                    }
                    return true;
                },
                .branch = branch_with(variable_order::in_order(branch_vars), value_order::smallest_first())},
            proof_opts);

        probe.recursions = static_cast<long long>(stats.recursions);

        if (proof_name && can_run_veripb()) {
            auto opb = *proof_name + ".opb", pbp = *proof_name + ".pbp";
            probe.verified = run_veripb(opb, pbp);
            // as in the shared test utilities: delete the proofs on success,
            // keep them around for debugging on failure
            if (probe.verified) {
                std::remove(opb.c_str());
                std::remove(pbp.c_str());
            }
        }

        return probe;
    }

    int failures = 0;

    auto expect(bool cond, const string & what) -> void
    {
        if (! cond) {
            println(cerr, "FAIL: {}", what);
            ++failures;
        }
        else
            println(cerr, "ok: {}", what);
    }
}

auto main() -> int
{
    const bool proofs = can_run_veripb();
    if (! proofs)
        println(cerr, "veripb not available: running without proof verification");

    // 1. Tightening: z in [0,5]. The matching refutes level 5 (matching size 2,
    //    |A| - |M| = 3 < p = 4), so z's root upper bound must drop to 4. Without
    //    the matching (plain ForwardBound / PairSupport) it stays at 5.
    for (auto mode : {MinDistancePropagation::ForwardBoundMatch, MinDistancePropagation::PairSupportMatch}) {
        const bool ps = mode == MinDistancePropagation::PairSupportMatch;
        auto p = solve_probe(mode, 0, 5, proofs, string{ps ? "psm" : "fbm"} + "_tighten");
        expect(p.root_z_upper == 4, string{ps ? "psm" : "fbm"} + ": matching lowers root z upper bound to 4 (was 5)");
        expect(p.best_z.has_value() && *p.best_z == 3, "optimal z = 3 found");
        expect(p.verified, string{ps ? "psm" : "fbm"} + ": proof verifies (tightening)");
    }

    // Baselines: the non-matching variants do NOT tighten z at the root here.
    for (auto mode : {MinDistancePropagation::ForwardBound, MinDistancePropagation::PairSupport}) {
        const bool ps = mode == MinDistancePropagation::PairSupport;
        auto p = solve_probe(mode, 0, 5, false, string{ps ? "ps" : "fb"} + "_base");
        expect(p.root_z_upper == 5, string{ps ? "ps" : "fb"} + ": base variant leaves root z upper bound at 5");
    }

    // 2. Contradiction: z pinned to [5,5]. z >= 5 is unachievable (max independent
    //    set in the conflict graph is 3 < 4), so the matching must fail the node
    //    -- at the root, before any branching. The counting derivation then closes
    //    by RUP because the guard [z <= 4] is domain-false.
    for (auto mode : {MinDistancePropagation::ForwardBoundMatch, MinDistancePropagation::PairSupportMatch}) {
        const bool ps = mode == MinDistancePropagation::PairSupportMatch;
        auto p = solve_probe(mode, 5, 5, proofs, string{ps ? "psm" : "fbm"} + "_contradiction");
        expect(! p.has_solution, string{ps ? "psm" : "fbm"} + ": z pinned to 5 is infeasible");
        expect(p.recursions <= 1, string{ps ? "psm" : "fbm"} + ": matching fails z=5 at the root (recursions <= 1)");
        expect(p.verified, string{ps ? "psm" : "fbm"} + ": proof verifies (contradiction)");
    }

    if (failures == 0)
        println(cerr, "all directed matching checks passed");
    else
        println(cerr, "{} directed matching checks FAILED", failures);
    return failures == 0 ? EXIT_SUCCESS : EXIT_FAILURE;
}
