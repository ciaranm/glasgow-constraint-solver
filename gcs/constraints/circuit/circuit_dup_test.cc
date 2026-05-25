#include <gcs/constraints/circuit.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>

#include <cstdlib>
#include <iostream>

using namespace gcs;

using std::cerr;

namespace
{
    template <typename Constraint_>
    auto expect_throw_on_dup(const char * which) -> bool
    {
        // Circuit's successor array must be all-different; aliasing two
        // slots to the same variable handle is trivially infeasible. We
        // reject at construction so users don't wait for search to UNSAT.
        Problem p;
        auto x = p.create_integer_variable_vector(4, 0_i, 3_i);
        try {
            p.post(Constraint_{{x[0], x[1], x[2], x[1]}});
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
    ok &= expect_throw_on_dup<CircuitSCC>("CircuitSCC");
    ok &= expect_throw_on_dup<CircuitPrevent>("CircuitPrevent");
    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
