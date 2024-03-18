#include <algorithm>
#include <gcs/constraints/at_most_one.hh>
#include <gcs/constraints/smart_table.hh>
#include <optional>
#include <utility>

using std::cmp_less;
using std::move;
using std::optional;
using std::unique_ptr;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

AtMostOneSmartTable::AtMostOneSmartTable(vector<IntegerVariableID> vars, IntegerVariableID val) :
    _vars(move(vars)),
    _val(val)
{
}

auto AtMostOneSmartTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<AtMostOneSmartTable>(_vars, _val);
}

auto AtMostOneSmartTable::install(Propagators & propagators, State & initial_state,
    ProofModel * const optional_model) && -> void
{
    // Build the constraint as smart table
    // Question: Do we trust this encoding as a smart table?
    // Should we morally have a simpler PB encoding and reformulate?
    // Like an auto-smart-table proof?
    SmartTuples tuples;

    for (int i = 0; cmp_less(i, _vars.size()); ++i) {
        vector<SmartEntry> tuple;
        for (int j = 0; cmp_less(j, _vars.size()); ++j) {
            if (j != i) {
                tuple.emplace_back(SmartTable::not_equals(_vars[j], _val));
            }
        }
        tuples.emplace_back(tuple);
    }

    auto all_vars = _vars;
    all_vars.emplace_back(_val);

    SmartTable smt_table{all_vars, tuples};
    move(smt_table).install(propagators, initial_state, optional_model);
}

auto AtMostOneSmartTable::describe_for_proof() -> std::string
{
    return "at most one (as a smart table)";
}
