#include <algorithm>
#include <gcs/constraints/lex.hh>
#include <gcs/constraints/smart_table.hh>
#include <optional>
#include <utility>

using std::min;
using std::move;
using std::unique_ptr;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

LexSmartTable::LexSmartTable(vector<IntegerVariableID> vars_1, vector<IntegerVariableID> vars_2) :
    _vars_1(move(vars_1)),
    _vars_2(move(vars_2))
{
}

auto LexSmartTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<LexSmartTable>(_vars_1, _vars_2);
}

auto LexSmartTable::install(Propagators & propagators, State & initial_state) && -> void
{
    // Build the constraint as smart table
    // Question: Do we trust this encoding as a smart table?
    // Should we morally have a simpler PB encoding and reformulate?
    // Like an auto-smart-table proof?
    SmartTuples tuples;

    for (unsigned int i = 0; i < min(_vars_1.size(), _vars_2.size()); ++i) {
        vector<SmartEntry> tuple;
        for (unsigned int j = 0; j < i + 1; ++j) {
            if (j < i)
                tuple.emplace_back(SmartTable::equals(_vars_1[j], _vars_2[j]));
            else if (j == i)
                tuple.emplace_back(SmartTable::greater_than(_vars_1[j], _vars_2[j]));
        }
        tuples.emplace_back(tuple);
    }

    auto all_vars = _vars_1;
    all_vars.insert(all_vars.end(), _vars_2.begin(), _vars_2.end());

    auto smt_table = SmartTable{all_vars, tuples};
    move(smt_table).install(propagators, initial_state);
}

auto LexSmartTable::describe_for_proof() -> std::string
{
    return "at most one (as a smart table)";
}