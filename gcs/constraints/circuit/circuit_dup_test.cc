#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <vector>

using namespace gcs;
using namespace gcs::test_innards;

using std::cerr;
using std::make_optional;
using std::nullopt;
using std::set;
using std::string;
using std::tuple;
using std::vector;

namespace
{
    auto run_dup_test(bool proofs, CircuitAlgorithm algorithm, bool gac_all_different, const string & which) -> void
    {
        // Circuit's successor array must be all-different, so aliasing two slots
        // to the same variable handle is unsatisfiable. That is a legal post,
        // which MiniZinc makes whenever a model equates two successors (#1047),
        // so it is answered with a root contradiction whichever algorithm is
        // selected, and with or without the child all-different.
        cerr << "circuit dup " << which << (gac_all_different ? " gac" : "") << (proofs ? " with proofs:" : ":") << '\n';
        Problem p;
        auto x = p.create_integer_variable_vector(4, 0_i, 3_i);
        p.post(Circuit{{x[0], x[1], x[2], x[1]}}.with_algorithm(algorithm).with_gac_all_different(gac_all_different));

        set<tuple<vector<int>>> expected, actual;
        auto proof_name = proofs ? make_optional("circuit_dup_test") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{x});
        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (bool gac : {false, true}) {
            run_dup_test(proofs, circuit::SCC{}, gac, "circuit::SCC");
            run_dup_test(proofs, circuit::Prevent{}, gac, "circuit::Prevent");
        }
    }
    return EXIT_SUCCESS;
}
