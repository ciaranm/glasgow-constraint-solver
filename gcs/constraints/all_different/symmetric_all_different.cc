#include <gcs/constraints/all_different/symmetric_all_different.hh>
#include <gcs/constraints/inverse.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <sstream>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

SymmetricAllDifferent::SymmetricAllDifferent(vector<IntegerVariableID> vars, Integer start) :
    _vars(move(vars)),
    _start(start)
{
}

auto SymmetricAllDifferent::clone() const -> unique_ptr<Constraint>
{
    return make_unique<SymmetricAllDifferent>(_vars, _start);
}

auto SymmetricAllDifferent::install(Propagators & propagators, State & initial_state,
    ProofModel * const optional_model) && -> void
{
    auto vars_copy = _vars;
    Inverse{move(_vars), move(vars_copy), _start, _start}.install(propagators, initial_state, optional_model);
}

auto SymmetricAllDifferent::s_exprify(const string & name, const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} symmetric_all_different (", name);
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") {}", _start);

    return s.str();
}
