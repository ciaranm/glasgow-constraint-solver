#include <gcs/constraints/smart_table.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>

#include <cstdlib>
#include <iostream>

using namespace gcs;

using std::cerr;

namespace
{
    auto expect_throw(const char * label, const SmartTuples & tuples) -> bool
    {
        // SmartTable's build_forests keys adjacent_edges by the underlying
        // (deviewed) variable, so any BinaryEntry whose two sides share
        // an underlying handle silently drops out of the tree — the OPB
        // and propagator end up disagreeing. Construction must reject.
        Problem p;
        auto x = p.create_integer_variable(0_i, 5_i, "x");
        auto y = p.create_integer_variable(0_i, 5_i, "y");
        (void) x;
        (void) y;
        try {
            p.post(SmartTable{{x, y}, tuples});
        }
        catch (const InvalidProblemDefinitionException &) {
            return true;
        }
        cerr << label << ": expected InvalidProblemDefinitionException\n";
        return false;
    }
}

auto main(int, char *[]) -> int
{
    Problem dummy;
    auto x = dummy.create_integer_variable(0_i, 5_i, "x");
    auto y = dummy.create_integer_variable(0_i, 5_i, "y");

    bool ok = true;

    // BinaryEntry{x, x, Equal} — same handle.
    ok &= expect_throw("equals(x, x)", SmartTuples{{SmartTable::equals(x, x)}});
    // NotEqual is the case the audit called "the worst correctness bug":
    // without the throw, the tuple becomes silently always-feasible.
    ok &= expect_throw("not_equals(x, x)", SmartTuples{{SmartTable::not_equals(x, x)}});
    // The same on view-aliased operands: x and x + 1 also deview to the
    // same underlying var, so build_forests still collapses them.
    ok &= expect_throw("not_equals(x, x + 1)",
        SmartTuples{{SmartTable::not_equals(x, x + 1_i)}});
    // The same on negated views (-x deviews to the same underlying).
    ok &= expect_throw("less_than(x, -x)",
        SmartTuples{{SmartTable::less_than(x, -x)}});
    // The bad entry is inside a multi-entry tuple alongside good ones.
    ok &= expect_throw("mixed tuple with dup",
        SmartTuples{{SmartTable::equals(x, y), SmartTable::greater_than(x, x)}});
    // And only in one of several tuples in the table.
    ok &= expect_throw("dup in second tuple",
        SmartTuples{
            {SmartTable::equals(x, y)},
            {SmartTable::not_equals(x, x)}});

    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
