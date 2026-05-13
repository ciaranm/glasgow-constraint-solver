#include <gcs/constraints/minus.hh>
#include <gcs/constraints/plus.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <sstream>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::unique_ptr;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

Minus::Minus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result) :
    _a(a),
    _b(b),
    _result(result)
{
}

auto Minus::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Minus>(_a, _b, _result);
}

auto Minus::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Minus::define_proof_model(ProofModel & model) -> void
{
    _sum_line = model.add_constraint("Minus", "sum", WPBSum{} + 1_i * _a + -1_i * _b == 1_i * _result);
}

auto Minus::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_bounds.insert(triggers.on_bounds.end(), {_a, _b, _result});

    propagators.install(
        [a = _a, b = _b, result = _result, sum_line = _sum_line](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            return propagate_plus(a, -b, result, state, inference, logger, sum_line);
        },
        triggers);
}

auto Minus::s_exprify(const innards::ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} minus (", _name);
    print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(_a));
    print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(_b));
    print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(_result));
    print(s, ")");

    return s.str();
}
