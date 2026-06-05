#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/scp_writer.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/problem.hh>

#include <fstream>
#include <ios>
#include <ostream>
#include <string>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using std::ios;
using std::ios_base;
using std::ofstream;
using std::string;

using namespace gcs;
using namespace gcs::innards;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

auto gcs::innards::write_scp(const string & file_name, const Problem & problem, const ProofModel * const model) -> void
{
    try {
        ofstream s_expr;
        s_expr.exceptions(ios::failbit | ios::badbit);
        s_expr.open(file_name);

        println(s_expr, "(");
        println(s_expr, "    (");
        for (const auto & [_, l, u, n] : problem.each_variable_with_bounds_and_name())
            println(s_expr, "        ({} {} {})", n, l, u);
        println(s_expr, "    )");
        println(s_expr, "    (");
        for (const auto & c : problem.each_constraint())
            println(s_expr, "        {}", c.s_expr(model));
        println(s_expr, "    )");
        println(s_expr, ")");
    }
    catch (const ios_base::failure &) {
        throw ProofError{"Error writing proof s-expr file to '" + file_name + "'"};
    }
}
