#include <gcs/constraints/all_different/all_different_except.hh>
#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/constraints/all_different/gac_all_different.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <map>
#include <sstream>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::adjacent_find;
using std::find;
using std::make_shared;
using std::make_unique;
using std::map;
using std::move;
using std::ranges::sort;
using std::shared_ptr;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

AllDifferentExcept::AllDifferentExcept(vector<IntegerVariableID> vars, vector<Integer> excluded) :
    _vars(move(vars)),
    _excluded(move(excluded))
{
}

auto AllDifferentExcept::clone() const -> unique_ptr<Constraint>
{
    return make_unique<AllDifferentExcept>(_vars, _excluded);
}

auto AllDifferentExcept::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    auto sanitised_vars = move(_vars);
    sort(sanitised_vars);
    if (adjacent_find(sanitised_vars.begin(), sanitised_vars.end()) != sanitised_vars.end()) {
        propagators.model_contradiction(initial_state, optional_model, "AllDifferentExcept with duplicate variables");
        return;
    }

    // Drop excluded values that don't appear in any variable's initial domain.
    // Such values can never be taken anyway, so they neither shape the OPB
    // encoding nor warrant phantom edges in the propagator's matching graph.
    auto sanitised_excluded = move(_excluded);
    sort(sanitised_excluded);
    sanitised_excluded.erase(std::unique(sanitised_excluded.begin(), sanitised_excluded.end()), sanitised_excluded.end());
    sanitised_excluded.erase(std::remove_if(sanitised_excluded.begin(), sanitised_excluded.end(),
                                 [&](const Integer & s) {
                                     for (const auto & v : sanitised_vars)
                                         if (initial_state.in_domain(v, s))
                                             return false;
                                     return true;
                                 }),
        sanitised_excluded.end());

    shared_ptr<map<Integer, ProofLine>> value_am1_constraint_numbers;

    if (optional_model) {
        value_am1_constraint_numbers = make_shared<map<Integer, ProofLine>>();
        define_clique_not_equals_except_encoding(*optional_model, sanitised_vars, sanitised_excluded);
    }

    Triggers triggers;
    triggers.on_change = {sanitised_vars.begin(), sanitised_vars.end()};

    // Compressed value list for the propagator: real (non-excluded) values
    // from the union of variable domains. Excluded values are not part of
    // the bipartite right side; phantoms cover them.
    vector<Integer> compressed_vals;
    for (auto & var : sanitised_vars)
        for (const auto & val : initial_state.each_value_immutable(var))
            if (find(sanitised_excluded.begin(), sanitised_excluded.end(), val) == sanitised_excluded.end())
                if (find(compressed_vals.begin(), compressed_vals.end(), val) == compressed_vals.end())
                    compressed_vals.push_back(val);

    propagators.install(
        [vars = move(sanitised_vars),
            vals = move(compressed_vals),
            excluded = move(sanitised_excluded),
            value_am1_constraint_numbers = move(value_am1_constraint_numbers)](const State & state, auto & inference,
            ProofLogger * const logger) -> PropagatorState {
            propagate_gac_all_different(vars, vals, excluded, *value_am1_constraint_numbers.get(), state, inference, logger);
            return PropagatorState::Enable;
        },
        triggers, "alldiff_except");
}

auto AllDifferentExcept::s_exprify(const string & name, const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} all_different_except (", name);
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") (");
    for (const auto & v : _excluded)
        print(s, " {}", v);
    print(s, ")");

    return s.str();
}
