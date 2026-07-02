#include <gcs/constraints/power/power_table.hh>
#include <gcs/constraints/table.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <optional>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::unique_ptr;
using std::vector;

PowerTable::PowerTable(IntegerVariableID base, IntegerVariableID exponent, IntegerVariableID result) :
    _base(base), _exponent(exponent), _result(result)
{
}

auto PowerTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<PowerTable>(_base, _exponent, _result);
}

auto PowerTable::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    vector<vector<Integer>> permitted;
    for (const auto & v1 : initial_state.each_value_immutable(_base))
        for (const auto & v2 : initial_state.each_value_immutable(_exponent)) {
            if (! initial_state.in_domain(_exponent, v2))
                continue;
            auto r = checked_integer_power(v1, v2);
            if (r && initial_state.in_domain(_result, *r))
                permitted.push_back(vector{v1, v2, *r});
        }

    Table table{vector<IntegerVariableID>{_base, _exponent, _result}, move(permitted)};
    table.set_constraint_id(constraint_id());
    move(table).install(propagators, initial_state, optional_model);
}

auto PowerTable::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("power"),
        SExpr::list({tracker.s_expr_term_of(_base), tracker.s_expr_term_of(_exponent), tracker.s_expr_term_of(_result)})});
}
