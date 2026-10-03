#include <gcs/constraints/power/power_table.hh>
#include <gcs/constraints/table.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <optional>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::unique_ptr;
using std::vector;

namespace
{
    // The table is written over the underlying variables, and each view value
    // translated back through its view. A view's values can reach twice as far
    // as a declared variable's, past the range a tuple value may take, whereas
    // an underlying variable's values cannot (dev_docs/integer-ranges.md).
    auto underlying_of(const IntegerVariableID & var) -> IntegerVariableID
    {
        return overloaded{
            [&](const SimpleIntegerVariableID & v) -> IntegerVariableID { return v; },                 //
            [&](const ViewOfIntegerVariableID & v) -> IntegerVariableID { return v.actual_variable; }, //
            [&](const ConstantIntegerVariableID & v) -> IntegerVariableID { return v; }                //
        }
            .visit(var);
    }

    auto underlying_value_of(const IntegerVariableID & var, Integer value) -> Integer
    {
        if (const auto * view = std::get_if<ViewOfIntegerVariableID>(&var))
            return view->negate_first ? -(value - view->then_add) : value - view->then_add;
        return value;
    }
}

PowerTable::PowerTable(IntegerVariableID base, IntegerVariableID exponent, IntegerVariableID result) :
    _base(base), _exponent(exponent), _result(result)
{
}

auto PowerTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<PowerTable>(_base, _exponent, _result);
}

auto PowerTable::prepare(Propagators & propagators, State & initial_state, ProofModel * const optional_model) -> bool
{
    // Delegates entirely to a materialised Table over the reachable triples, which
    // is why this reads the initial domains here.
    vector<vector<Integer>> permitted;
    for (const auto & v1 : initial_state.each_value_immutable(_base))
        for (const auto & v2 : initial_state.each_value_immutable(_exponent)) {
            if (! initial_state.in_domain(_exponent, v2))
                continue;
            auto r = checked_integer_power(v1, v2);
            if (r && initial_state.in_domain(_result, *r))
                permitted.push_back(vector{underlying_value_of(_base, v1), underlying_value_of(_exponent, v2), underlying_value_of(_result, *r)});
        }

    Table table{vector<IntegerVariableID>{underlying_of(_base), underlying_of(_exponent), underlying_of(_result)}, move(permitted)};
    table.set_constraint_id(constraint_id());
    move(table).install(propagators, initial_state, optional_model);

    return false;
}

auto PowerTable::constraint_type() const -> std::string
{
    return "power";
}

auto PowerTable::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()),
        SExpr::list({tracker.s_expr_term_of(_base), tracker.s_expr_term_of(_exponent), tracker.s_expr_term_of(_result)})});
}
