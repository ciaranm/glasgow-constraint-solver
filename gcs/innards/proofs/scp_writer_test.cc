#include <gcs/constraint.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/problem.hh>
#include <gcs/proof.hh>
#include <gcs/solve.hh>

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <memory>
#include <optional>
#include <string>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::make_unique;
using std::string;
using std::unique_ptr;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

// Issue #908: write_scp renders the whole file before it opens it, so a
// constraint whose s_expr() throws leaves no .scp at all rather than one
// truncated mid-(constraints. A partial .scp is worse than none --- it parses
// as far as it goes, and the complete .opb sitting next to it says nothing is
// wrong. Nothing in the tree throws from s_expr() today (the two families that
// did, the negated reification forms of comparison and linear, are spelled out
// now), so the guarantee is pinned here with a constraint written to have no
// .scp spelling at all.
namespace
{
    struct UnspellableConstraint final : Constraint
    {
        [[nodiscard]] auto constraint_type() const -> string override
        {
            return "unspellable";
        }

        [[nodiscard]] auto clone() const -> unique_ptr<Constraint> override
        {
            return make_unique<UnspellableConstraint>();
        }

        [[nodiscard]] auto s_expr(const ProofModel * const) const -> SExpr override
        {
            throw UnexpectedException{"this constraint has no .scp spelling"};
        }
    };

    [[nodiscard]] auto file_exists(const string & name) -> bool
    {
        return static_cast<bool>(std::ifstream{name});
    }

    [[nodiscard]] auto check_file(const string & name, bool expected) -> bool
    {
        if (file_exists(name) == expected)
            return true;
        print(stderr, "{} {}, expected it {}\n", name, expected ? "is missing" : "was written", expected ? "written" : "absent");
        return false;
    }

    auto clean_up(const string & basename) -> void
    {
        for (const auto & ext : {".opb", ".pbp", ".scp", ".varmap"})
            std::remove((basename + ext).c_str());
    }
}

auto main() -> int
{
    auto ok = true;

    // Control: an ordinary problem writes every file, so the absence below is
    // about the throw and not about proof files never being written here.
    {
        Problem p;
        auto x = p.create_integer_variable(0_i, 3_i, "x");
        auto y = p.create_integer_variable(0_i, 3_i, "y");
        p.post(LessThan{x, y});
        static_cast<void>(solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; }},
            make_optional<ProofOptions>(ProofFileNames{"scp_writer_test_control"})));
        ok &= check_file("scp_writer_test_control.opb", true);
        ok &= check_file("scp_writer_test_control.scp", true);
        clean_up("scp_writer_test_control");
    }

    // The same, plus a constraint the .scp grammar cannot express.
    {
        Problem p;
        auto x = p.create_integer_variable(0_i, 3_i, "x");
        auto y = p.create_integer_variable(0_i, 3_i, "y");
        p.post(LessThan{x, y});
        p.post(UnspellableConstraint{});

        auto threw = false;
        try {
            static_cast<void>(solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; }},
                make_optional<ProofOptions>(ProofFileNames{"scp_writer_test_unspellable"})));
        }
        catch (const UnexpectedException &) {
            threw = true;
        }

        if (! threw) {
            print(stderr, "posting an unspellable constraint under proofs did not throw\n");
            ok = false;
        }
        // The .opb is complete by the time the .scp is written, which is what
        // makes a truncated .scp next to it so misleading.
        ok &= check_file("scp_writer_test_unspellable.opb", true);
        ok &= check_file("scp_writer_test_unspellable.scp", false);
        clean_up("scp_writer_test_unspellable");
    }

    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
