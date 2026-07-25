#include <gcs/constraint.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_model.hh>
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

        // Format version 1: exactly four tagged sections, in this order. A
        // reader checks the version first and refuses anything else, so bumping
        // this number is how an incompatible grammar change is announced.
        println(s_expr, "(");
        println(s_expr, "    (version 1)");
        println(s_expr, "    (variables");
        for (const auto & [_, l, u, n] : problem.each_variable_with_bounds_and_name())
            println(s_expr, "        ({} {} {})", n, l, u);
        println(s_expr, "    )");
        println(s_expr, "    (constraints");
        for (const auto & c : problem.each_constraint())
            println(s_expr, "        {}", c.s_expr(model));
        println(s_expr, "    )");
        // The problem type is the objective, or the bare atom `enumerate` for a
        // satisfaction / enumeration problem. cake_pb_cp uses it to decide
        // whether to emit a `preserved:` set -- which veripb needs to
        // log/exclude solutions, so with the alternative `decide` only
        // refutation (UNSAT) proofs would verify through the chain.
        if (auto objective = problem.optional_minimise_variable())
            println(s_expr, "    (prob_type {})", model->names_and_ids_tracker().s_expr_render_of(*objective));
        else
            println(s_expr, "    (prob_type enumerate)");
        println(s_expr, ")");
    }
    catch (const ios_base::failure &) {
        throw ProofError{"Error writing proof s-expr file to '" + file_name + "'"};
    }
}
