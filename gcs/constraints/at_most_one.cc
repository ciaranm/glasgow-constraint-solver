#include <algorithm>
#include <gcs/constraints/at_most_one.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <optional>
#include <sstream>
#include <utility>

#include <fmt/ostream.h>

using std::cmp_less;
using std::move;
using std::optional;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

using fmt::print;

AtMostOneSmartTable::AtMostOneSmartTable(vector<IntegerVariableID> vars, IntegerVariableID val) :
    _vars(move(vars)),
    _val(val)
{
}

auto AtMostOneSmartTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<AtMostOneSmartTable>(_vars, _val);
}

auto AtMostOneSmartTable::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto AtMostOneSmartTable::prepare(Propagators & propagators, State & initial_state,
    ProofModel * const optional_model) -> bool
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
    return false;
}

// The "semantics of cp document" says "at_most_one (smart table wrapper, don’t bother and just use count)"
auto AtMostOneSmartTable::s_exprify(const string & name, const innards::ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} at_most_one (", name);
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") {}", model->names_and_ids_tracker().s_expr_name_of(_val));

    return s.str();
}
