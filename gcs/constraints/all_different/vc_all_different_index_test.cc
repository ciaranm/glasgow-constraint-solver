/* The value-to-positions index in the value-consistent all-different pass
 * (issue #1482).
 *
 * propagate_non_gac_alldifferent checks each newly fixed variable against the
 * fixed values still waiting in the same call. Past index_from waiting values
 * it switches from a linear scan to an index from each value to its positions
 * (#1453), and that index has to find a clash exactly as the scan does. Only a
 * large fixed ring under Circuit reaches the index otherwise, and that never
 * clashes, so deleting the index's clash detection left every test green while
 * the solver returned wrong solutions.
 *
 * Here every variable is a view of one y in {0, 1}, so branching on y fixes the
 * whole scope in one call. The offsets y + 0 .. y + (n - 1) are all different,
 * and -y + 6 collides with one of them whichever value y takes, so the problem
 * is unsatisfiable. With n = 10 the call takes the scan; with n = 17 and n = 40
 * it takes the index. */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <set>
#include <tuple>
#include <vector>

using namespace gcs;
using namespace gcs::test_innards;

using std::cerr;
using std::make_optional;
using std::nullopt;
using std::set;
using std::tuple;
using std::vector;

namespace
{
    auto run_index_test(bool proofs, int n) -> void
    {
        cerr << "vc all different, " << n << " offsets and a negation" << (proofs ? " with proofs:" : ":") << '\n';
        Problem p;
        auto y = p.create_integer_variable(0_i, 1_i, "y");
        vector<IntegerVariableID> vars;
        for (int i = 0; i < n; ++i)
            vars.push_back(y + Integer{i});
        vars.push_back(-y + 6_i);
        p.post(AllDifferent{vars}.with_consistency(consistency::VC{}));

        set<tuple<int>> expected, actual;
        auto proof_name = proofs ? make_optional("vc_all_different_index_test") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{y});
        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (int n : {10, 17, 40})
            run_index_test(proofs, n);
    }
    return EXIT_SUCCESS;
}
