#include <gcs/constraints/arithmetic.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <fmt/ostream.h>

#include <cmath>
#include <tuple>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::llroundl;
using std::move;
using std::optional;
using std::pow;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

using fmt::print;

template <ArithmeticOperator op_>
GACArithmetic<op_>::GACArithmetic(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result) :
    _v1(v1),
    _v2(v2),
    _result(result)
{
}

template <ArithmeticOperator op_>
auto GACArithmetic<op_>::clone() const -> unique_ptr<Constraint>
{
    return make_unique<GACArithmetic<op_>>(_v1, _v2, _result);
}

template <ArithmeticOperator op_>
auto GACArithmetic<op_>::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (!prepare(propagators, initial_state, optional_model)) 
        return;

    // The prepare() function does all the work and always returns false, so this code is unreachable.
    // It's only here to match the pattern of Constraint::install() so maybe we can implement install()
    // in the base class only at some point.
    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

template <ArithmeticOperator op_>
auto GACArithmetic<op_>::prepare(Propagators & propagators, State & initial_state, ProofModel * const optional_model) -> bool
{
    // This is the exact logic of the old install function.  Because we are delegating the work
    // to propagators.define_and_install_table(), we do everything in prepare() and return false
    // to skip the rest of the install() logic.  Similar to how we would handle a contradiction.
    vector<vector<Integer>> permitted;
    bool v2_zero_is_ok = (op_ != ArithmeticOperator::Div && op_ != ArithmeticOperator::Mod);

    for (const auto & v1 : initial_state.each_value_immutable(_v1))
        for (const auto & v2 : initial_state.each_value_immutable(_v2))
            if ((v2_zero_is_ok || v2 != 0_i) && initial_state.in_domain(_v2, v2)) {
                Integer r = 0_i;
                switch (op_) {
                case ArithmeticOperator::Plus: r = v1 + v2; break;
                case ArithmeticOperator::Minus: r = v1 - v2; break;
                case ArithmeticOperator::Times: r = v1 * v2; break;
                case ArithmeticOperator::Div: r = v1 / v2; break;
                case ArithmeticOperator::Mod: r = v1 % v2; break;
                case ArithmeticOperator::Power: r = Integer{llroundl(pow(v1.raw_value, v2.raw_value))}; break;
                }
                if (initial_state.in_domain(_result, r))
                    permitted.push_back(vector{v1, v2, r});
            }

    propagators.define_and_install_table(initial_state, optional_model, vector{_v1, _v2, _result}, move(permitted), "arithmetic");
    return false;
}

namespace gcs::innards
{
    template class GACArithmetic<ArithmeticOperator::Plus>;
    template class GACArithmetic<ArithmeticOperator::Minus>;
    template class GACArithmetic<ArithmeticOperator::Times>;
    template class GACArithmetic<ArithmeticOperator::Div>;
    template class GACArithmetic<ArithmeticOperator::Mod>;
    template class GACArithmetic<ArithmeticOperator::Power>;
}

template <ArithmeticOperator op_>
auto GACArithmetic<op_>::s_exprify(const std::string & name, const innards::ProofModel * const model) const -> std::string
{
    // (name op v1 v2 result)
    string op_str;
    switch (op_) {
    case ArithmeticOperator::Plus: op_str = "plus"; break;
    case ArithmeticOperator::Minus: op_str = "minus"; break;
    case ArithmeticOperator::Times: op_str = "times"; break;
    case ArithmeticOperator::Div: op_str = "div"; break;
    case ArithmeticOperator::Mod: op_str = "mod"; break;
    case ArithmeticOperator::Power: op_str = "power"; break;
    }

    return fmt::format("({} {} {} {} {})", name, op_str,
        model->names_and_ids_tracker().s_expr_name_of(_v1),
        model->names_and_ids_tracker().s_expr_name_of(_v2),
        model->names_and_ids_tracker().s_expr_name_of(_result));
}
