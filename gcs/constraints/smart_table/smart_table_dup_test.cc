#include <gcs/constraints/at_most_one.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/lex_smart_table.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/proof.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>

using namespace gcs;

using std::cerr;
using std::getline;
using std::ifstream;
using std::string;

namespace
{
    auto posting_throws(const SmartTuples & tuples) -> bool
    {
        Problem p;
        auto x = p.create_integer_variable(0_i, 5_i, "x");
        auto y = p.create_integer_variable(0_i, 5_i, "y");
        auto z = p.create_integer_variable(0_i, 5_i, "z");
        try {
            p.post(SmartTable{{x, y, z}, tuples});
        }
        catch (const InvalidProblemDefinitionException &) {
            return true;
        }
        return false;
    }

    auto expect_throw(const char * label, const SmartTuples & tuples) -> bool
    {
        // SmartTable's build_forests keys adjacent_edges by the underlying
        // (deviewed) variable, so any BinaryEntry whose two sides share
        // an underlying handle silently drops out of the tree — the OPB
        // and propagator end up disagreeing. So does any BinaryEntry that
        // closes a cycle among a tuple's underlying variables (issue #1014).
        // Construction must reject both.
        if (posting_throws(tuples))
            return true;
        cerr << label << ": expected InvalidProblemDefinitionException\n";
        return false;
    }

    auto expect_accept(const char * label, const SmartTuples & tuples) -> bool
    {
        if (! posting_throws(tuples))
            return true;
        cerr << label << ": unexpected InvalidProblemDefinitionException\n";
        return false;
    }

    // LexSmartTable and AtMostOneSmartTable delegate to a SmartTable they build
    // in prepare(), and that child has to carry the posted constraint's ID, or
    // its assertion hints name no constraint at all (issue #1121). So solve at
    // AssertionLevel::Inferences, where the hints are on the wire, and check
    // that some smart_table hint names the posted constraint, which is the
    // problem's first, and that none says unnamed.
    auto hints_name_posted_constraint(const char * label, Problem & p) -> bool
    {
        const string proof_name = "smart_table_dup_test_hints";
        auto options = ProofOptions{ProofFileNames{proof_name}};
        options.set_assertion_level(AssertionLevel::Inferences);
        solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) { return true; }}, options);

        int named = 0, unnamed = 0;
        ifstream proof{proof_name + ".pbp"};
        for (string line; getline(proof, line);) {
            if (line.find("::smart_table:((constraint_id _1))") != string::npos)
                ++named;
            if (line.find("::smart_table:((constraint_id unnamed))") != string::npos)
                ++unnamed;
        }
        proof.close();
        test_innards::dispose_of_proof_files(proof_name);

        if (named > 0 && unnamed == 0)
            return true;
        cerr << label << ": expected smart_table hints naming _1 and none unnamed, got " << named << " named and " << unnamed << " unnamed\n";
        return false;
    }
}

auto main(int, char *[]) -> int
{
    Problem dummy;
    auto x = dummy.create_integer_variable(0_i, 5_i, "x");
    auto y = dummy.create_integer_variable(0_i, 5_i, "y");
    auto z = dummy.create_integer_variable(0_i, 5_i, "z");

    bool ok = true;

    // BinaryEntry{x, x, Equal} — same handle.
    ok &= expect_throw("equals(x, x)", SmartTuples{{SmartTable::equals(x, x)}});
    // NotEqual is the case the audit called "the worst correctness bug":
    // without the throw, the tuple becomes silently always-feasible.
    ok &= expect_throw("not_equals(x, x)", SmartTuples{{SmartTable::not_equals(x, x)}});
    // The same on view-aliased operands: x and x + 1 also deview to the
    // same underlying var, so build_forests still collapses them.
    ok &= expect_throw("not_equals(x, x + 1)", SmartTuples{{SmartTable::not_equals(x, x + 1_i)}});
    // The same on negated views (-x deviews to the same underlying).
    ok &= expect_throw("less_than(x, -x)", SmartTuples{{SmartTable::less_than(x, -x)}});
    // The bad entry is inside a multi-entry tuple alongside good ones.
    ok &= expect_throw("mixed tuple with dup", SmartTuples{{SmartTable::equals(x, y), SmartTable::greater_than(x, x)}});
    // And only in one of several tuples in the table.
    ok &= expect_throw("dup in second tuple", SmartTuples{{SmartTable::equals(x, y)}, {SmartTable::not_equals(x, x)}});

    // Issue #1014: a tuple's binary entries must form a forest. Two different
    // entries on one pair are the smallest cycle, in either orientation.
    ok &= expect_throw("less_than and greater_than on one pair", SmartTuples{{SmartTable::less_than(x, y), SmartTable::greater_than(x, y)}});
    ok &= expect_throw("one pair both ways round", SmartTuples{{SmartTable::less_than(x, y), SmartTable::less_than(y, x)}});
    // A view joins the same pair of underlying variables.
    ok &= expect_throw("one pair through a view", SmartTuples{{SmartTable::less_than(x, y), SmartTable::not_equals(x + 1_i, y)}});
    ok &= expect_throw("triangle", SmartTuples{{SmartTable::less_than(x, y), SmartTable::less_than(y, z), SmartTable::less_than(z, x)}});
    ok &= expect_throw("triangle in second tuple",
        SmartTuples{{SmartTable::equals(x, y)}, {SmartTable::less_than(x, y), SmartTable::less_than(y, z), SmartTable::less_than(x, z)}});
    // Unary entries in among the binary ones do not hide a cycle.
    ok &= expect_throw("triangle among unary entries",
        SmartTuples{{SmartTable::less_than(x, y), SmartTable::equals(x, 1_i), SmartTable::less_than(y, z), SmartTable::less_than(z, x)}});

    // Forests are fine: a path, a star, and the same pair in different tuples.
    ok &= expect_accept("path", SmartTuples{{SmartTable::less_than(x, y), SmartTable::less_than(y, z)}});
    ok &= expect_accept("star", SmartTuples{{SmartTable::less_than(x, y), SmartTable::not_equals(x, z)}});
    // A unary entry adds no edge, so unary entries on a path do not make a cycle.
    ok &= expect_accept("path with unary entries",
        SmartTuples{{SmartTable::equals(x, 1_i), SmartTable::less_than(x, y), SmartTable::in_set(y, {2_i, 3_i}), SmartTable::less_than(y, z)}});
    ok &= expect_accept("one pair in two tuples", SmartTuples{{SmartTable::less_than(x, y)}, {SmartTable::greater_than(x, y)}});
    // An exact repeat of an entry adds nothing, so it is not a cycle.
    // AtMostOneSmartTable produces these when its array repeats a variable.
    ok &= expect_accept("exact repeat", SmartTuples{{SmartTable::not_equals(x, y), SmartTable::not_equals(x, y)}});

    // LexSmartTable builds its SmartTable when the problem is prepared for solving,
    // so a repeated variable that makes a cycle is rejected there, rather than
    // giving wrong answers: {a, b} >lex {b, a} has the tuple {a = b, b > a}.
    try {
        Problem p;
        auto a = p.create_integer_variable(0_i, 5_i, "a");
        auto b = p.create_integer_variable(0_i, 5_i, "b");
        p.post(LexSmartTable{{a, b}, {b, a}});
        solve(p, [](const CurrentState &) { return true; });
        cerr << "LexSmartTable({a, b}, {b, a}): expected InvalidProblemDefinitionException\n";
        ok = false;
    }
    catch (const InvalidProblemDefinitionException &) {
    }

    {
        Problem p;
        auto a = p.create_integer_variable_vector(2, 0_i, 2_i, "a");
        auto b = p.create_integer_variable_vector(2, 0_i, 2_i, "b");
        p.post(LexSmartTable{a, b});
        ok &= hints_name_posted_constraint("LexSmartTable", p);
    }
    {
        Problem p;
        auto a = p.create_integer_variable_vector(3, 0_i, 2_i, "a");
        auto v = p.create_integer_variable(0_i, 2_i, "v");
        p.post(AtMostOneSmartTable{a, v});
        ok &= hints_name_posted_constraint("AtMostOneSmartTable", p);
    }

    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
