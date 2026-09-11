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
#include <sstream>
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
using std::ostringstream;
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
    // Rendered in full before the file is touched. Constraint::s_expr() can
    // throw --- a constraint whose form has no spelling in the .scp grammar
    // says so that way --- and serialising straight to the stream would leave a
    // file truncated mid-section behind when it did. A partial .scp is worse
    // than none: it parses as far as it goes, and the .opb next to it is
    // complete. The whole .opb is built in memory too, so this costs nothing
    // the model was not already paying.
    ostringstream rendered;

    // Format version 1: exactly four tagged sections, in this order. A
    // reader checks the version first and refuses anything else, so bumping
    // this number is how an incompatible grammar change is announced.
    println(rendered, "(");
    println(rendered, "    (version 1)");
    println(rendered, "    (variables");
    for (const auto & [_, l, u, n] : problem.each_variable_with_bounds_and_name())
        println(rendered, "        ({} {} {})", n, l, u);
    println(rendered, "    )");
    println(rendered, "    (constraints");
    for (const auto & c : problem.each_constraint())
        println(rendered, "        {}", c.s_expr(model));
    println(rendered, "    )");
    // The problem type is the objective, or the bare atom `enumerate` for a
    // satisfaction / enumeration problem. cake_pb_cp uses it to decide
    // whether to emit a `preserved:` set -- which veripb needs to
    // log/exclude solutions, so with the alternative `decide` only
    // refutation (UNSAT) proofs would verify through the chain.
    if (auto objective = problem.optional_minimise_variable())
        println(rendered, "    (prob_type {})", model->names_and_ids_tracker().s_expr_render_of(*objective));
    else
        println(rendered, "    (prob_type enumerate)");
    println(rendered, ")");

    try {
        ofstream s_expr;
        s_expr.exceptions(ios::failbit | ios::badbit);
        s_expr.open(file_name);
        s_expr << rendered.str();
    }
    catch (const ios_base::failure &) {
        throw ProofError{"Error writing proof s-expr file to '" + file_name + "'"};
    }
}
