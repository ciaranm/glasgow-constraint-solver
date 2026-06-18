#include <gcs/constraints/lex_smart_table.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>

#include <algorithm>
#include <sstream>
#include <utility>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using std::min;
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

auto LexSmartTable::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
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
    move(smt_table).install(propagators, initial_state, optional_model);
}

auto LexSmartTable::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> a, b;
    for (const auto & var : _vars_1)
        a.push_back(tracker.s_expr_term_of(var));
    for (const auto & var : _vars_2)
        b.push_back(tracker.s_expr_term_of(var));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("lex"),
        SExpr::list(std::move(a)), SExpr::list(std::move(b))});
}
