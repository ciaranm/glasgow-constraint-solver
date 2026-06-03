#include <gcs/constraints/among.hh>
#include <gcs/constraints/global_cardinality/decomposed_global_cardinality.hh>
#include <gcs/constraints/in.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <sstream>
#include <string>

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

GlobalCardinalityDecomposition::GlobalCardinalityDecomposition(vector<IntegerVariableID> vars, vector<Integer> values,
    vector<IntegerVariableID> counts, bool closed) :
    _vars(move(vars)),
    _values(move(values)),
    _counts(move(counts)),
    _closed(closed)
{
}

auto GlobalCardinalityDecomposition::clone() const -> unique_ptr<Constraint>
{
    return make_unique<GlobalCardinalityDecomposition>(_vars, _values, _counts, _closed);
}

auto GlobalCardinalityDecomposition::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    // Decomposition baseline: link each cover value's occurrence count to its
    // count variable with an Among constraint, and (when closed) confine each
    // variable to the cover values with an In constraint. Both sub-constraints
    // are already proof-logged, so no OPB definition of our own is needed.
    for (const auto & [idx, value] : enumerate(_values))
        Among{_vars, vector<Integer>{value}, _counts[idx]}.install(propagators, initial_state, optional_model);

    if (_closed)
        for (const auto & var : _vars)
            In{var, _values}.install(propagators, initial_state, optional_model);
}

auto GlobalCardinalityDecomposition::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} globalcardinality{} (", _name, _closed ? "closed" : "");
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") (");
    for (const auto & val : _values)
        print(s, " {}", val);
    print(s, ") (");
    for (const auto & c : _counts)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(c));
    print(s, ")");

    return s.str();
}
