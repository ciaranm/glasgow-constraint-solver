#include <gcs/constraints/circuit.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>

#include <cstdlib>
#include <iostream>

using namespace gcs;

using std::cerr;

namespace
{
    auto expect_throw_on_dup(CircuitAlgorithm algorithm, const char * which) -> bool
    {
        // Circuit's successor array must be all-different; aliasing two
        // slots to the same variable handle is trivially infeasible. We
        // reject at construction so users don't wait for search to UNSAT.
        // The rejection is in the constructor, so it fires whichever
        // algorithm is later selected.
        Problem p;
        auto x = p.create_integer_variable_vector(4, 0_i, 3_i);
        try {
            p.post(Circuit{{x[0], x[1], x[2], x[1]}}.with_algorithm(algorithm));
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
    ok &= expect_throw_on_dup(circuit::SCC{}, "circuit::SCC");
    ok &= expect_throw_on_dup(circuit::Prevent{}, "circuit::Prevent");
    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
