#include <gcs/constraints/circuit.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>

#include <cstdlib>
#include <iostream>

using namespace gcs;

using std::cerr;

namespace
{
    auto expect_throw_on_dup(SubCircuitAlgorithm algorithm, const char * which) -> bool
    {
        // SubCircuit's successor array must be all-different -- a node off the tour points
        // at itself, which is what stops anyone else pointing at it -- so aliasing two
        // slots to the same variable handle is trivially infeasible. As Circuit, we reject
        // at construction rather than making the user wait for search to say UNSAT. The
        // rejection is in the constructor, so it fires whichever algorithm is selected.
        Problem p;
        auto x = p.create_integer_variable_vector(4, 0_i, 3_i);
        try {
            p.post(SubCircuit{{x[0], x[1], x[2], x[1]}}.with_algorithm(algorithm));
        }
        catch (const InvalidProblemDefinitionException &) {
            return true;
        }
        cerr << which << ": expected InvalidProblemDefinitionException on duplicate successor var\n";
        return false;
    }
}

auto main(int, char *[]) -> int
{
    bool ok = true;
    ok &= expect_throw_on_dup(subcircuit::Check{}, "subcircuit::Check");
    ok &= expect_throw_on_dup(subcircuit::Prevent{}, "subcircuit::Prevent");
    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
