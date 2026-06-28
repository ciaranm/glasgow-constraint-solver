#include <gcs/constraints/all_different/all_different_except.hh>
#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/constraints/all_different/gac_all_different.hh>
#include <gcs/constraints/all_different/hints.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <gcs/proof.hh>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <iterator>
#include <map>
#include <sstream>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::adjacent_find;
using std::distance;
using std::find;
using std::find_if;
using std::make_shared;
using std::make_unique;
using std::map;
using std::move;
using std::next;
using std::shared_ptr;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

AllDifferentExcept::AllDifferentExcept(vector<IntegerVariableID> vars, vector<Integer> excluded) : _vars(move(vars)), _excluded(move(excluded))
{
}

auto AllDifferentExcept::clone() const -> unique_ptr<Constraint>
{
    return make_unique<AllDifferentExcept>(_vars, _excluded);
}

auto AllDifferentExcept::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto AllDifferentExcept::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _sanitised_vars = move(_vars);
    sort(_sanitised_vars);

    // Drop excluded values that don't appear in any variable's initial domain.
    // Such values can never be taken anyway, so they don't warrant phantom
    // edges in the propagator's matching graph. The OPB encoding keeps the
    // original list (a copy, so s_expr and define_proof_model still see it):
    // cake_pb_cp encodes every listed exception value uniformly, and dropping
    // one changes the rows' unit-propagation strength, which the aliased-pair
    // case turns into a chain-verification failure (issue #480).
    _sanitised_excluded = _excluded;
    sort(_sanitised_excluded);
    _sanitised_excluded.erase(std::unique(_sanitised_excluded.begin(), _sanitised_excluded.end()), _sanitised_excluded.end());
    _sanitised_excluded.erase(std::remove_if(_sanitised_excluded.begin(), _sanitised_excluded.end(),
                                  [&](const Integer & s) {
                                      for (const auto & v : _sanitised_vars)
                                          if (initial_state.in_domain(v, s))
                                              return false;
                                      return true;
                                  }),
        _sanitised_excluded.end());

    // A variable that appears more than once must equal itself, so the
    // constraint forces it into the excluded set. With no usable excluded
    // values left, the encoding emitted by define_clique_not_equals_except
    // collapses to a self-contradicting half-reified pair (no excluded
    // relaxation), and install_propagators installs a clique-duplicate
    // contradiction initialiser to fail at search start.
    _has_duplicates = adjacent_find(_sanitised_vars.begin(), _sanitised_vars.end()) != _sanitised_vars.end();

    if (_has_duplicates) {
        for (auto it = _sanitised_vars.begin(); it != _sanitised_vars.end();) {
            auto run_end = find_if(next(it), _sanitised_vars.end(), [&](const IntegerVariableID & v) { return v != *it; });
            if (distance(it, run_end) > 1)
                _duplicated_vars.push_back(*it);
            it = run_end;
        }
    }

    // Compressed value list for the propagator: real (non-excluded) values
    // from the union of variable domains. Excluded values are not part of
    // the bipartite right side; phantoms cover them.
    for (auto & var : _sanitised_vars)
        for (const auto & val : initial_state.each_value_immutable(var))
            if (find(_sanitised_excluded.begin(), _sanitised_excluded.end(), val) == _sanitised_excluded.end())
                if (find(_compressed_vals.begin(), _compressed_vals.end(), val) == _compressed_vals.end())
                    _compressed_vals.push_back(val);

    return true;
}

auto AllDifferentExcept::define_proof_model(ProofModel & model) -> void
{
    _value_am1_constraint_numbers = make_shared<map<Integer, ProofLine>>();
    // Encode from the original exception list, matching cake_pb_cp: an
    // out-of-domain exception value still contributes its (statically-true)
    // literals to the pair rows, keeping the rows' propagation strength -- and
    // hence the proof steps they support -- identical on both sides.
    _duplicate_selectors = define_clique_not_equals_except_encoding(model, _sanitised_vars, _excluded);
}

auto AllDifferentExcept::install_propagators(Propagators & propagators) -> void
{
    // Only the genuinely-no-exceptions form may assert the duplicate
    // contradiction bare: its pair rows collapse to units on both our and
    // cake's side, so the contradiction is unit-propagatable everywhere. With
    // exception values present (even out-of-domain ones, which the encoding
    // keeps -- see define_proof_model), the rows need the per-value inferences
    // of the general duplicate path below to reach the wipeout.
    if (_has_duplicates && _excluded.empty()) {
        install_clique_duplicate_contradiction_initialiser(propagators, hints::AllDifferentExcept{constraint_id()});
        return;
    }

    // For each duplicated variable, install an initialiser that forces it
    // into the excluded set: for every value v in its current domain that is
    // not in `excluded`, infer var != v. The justification rests on the two
    // half-reified constraints emitted for the duplicate pair: each on its
    // own implies "selector OR var-in-excluded" or "!selector OR
    // var-in-excluded", so under the hypothesis var = v with v not in
    // excluded, both directions of the selector are simultaneously forced.
    if (_has_duplicates) {
        propagators.install_initialiser(
            [duplicated_vars = move(_duplicated_vars), excluded = _sanitised_excluded, duplicate_selectors = move(_duplicate_selectors),
                owner = constraint_id()](const State & state, auto & inf, ProofLogger * const logger) -> void {
                for (const auto & x : duplicated_vars) {
                    vector<Integer> non_excluded_values;
                    for (const auto & v : state.each_value_immutable(x))
                        if (find(excluded.begin(), excluded.end(), v) == excluded.end())
                            non_excluded_values.push_back(v);
                    for (const auto & v : non_excluded_values) {
                        // var != v by a complete 2-way case split on the duplicate-pair
                        // selector: each polarity forces var into the excluded set by RUP.
                        // The selector is a proof-model flag, so it only exists when
                        // proving; look it up rather than asserting its presence (with
                        // proofs off the flags are unused and the map is empty).
                        std::vector<ProofFlag> case_flags;
                        if (auto it = duplicate_selectors.find(x); it != duplicate_selectors.end())
                            case_flags.push_back(it->second);
                        inf.infer_not_equal(logger, x, v, JustifyUsingCases{std::move(case_flags), hints::AllDifferentExcept{owner}}, NoReason{});
                    }
                }
            });

        // Dedupe before the propagator runs: bipartite matching can't model
        // duplicate left-vertices correctly, but the initialiser has already
        // forced each duplicate's domain into `excluded`, so the propagator
        // sees a single instance of each variable with its restricted domain.
        _sanitised_vars.erase(std::unique(_sanitised_vars.begin(), _sanitised_vars.end()), _sanitised_vars.end());
    }

    Triggers triggers;
    triggers.on_change = {_sanitised_vars.begin(), _sanitised_vars.end()};

    if (! _value_am1_constraint_numbers)
        _value_am1_constraint_numbers = make_shared<map<Integer, ProofLine>>();

    propagators.install(
        constraint_id(),
        [vars = move(_sanitised_vars), vals = move(_compressed_vals), excluded = move(_sanitised_excluded),
            value_am1_constraint_numbers = _value_am1_constraint_numbers,
            constraint_id = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            propagate_gac_all_different(constraint_id, vars, vals, excluded, *value_am1_constraint_numbers.get(), state, inference, logger);
            return PropagatorState::Enable;
        },
        triggers);
}

auto AllDifferentExcept::constraint_type() const -> std::string
{
    return "all_different_except";
}

auto AllDifferentExcept::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> vars, excluded;
    for (const auto & var : _vars)
        vars.push_back(tracker.s_expr_term_of(var));
    for (const auto & v : _excluded)
        excluded.push_back(SExpr::atom(v.to_string()));
    return SExpr::list(
        {SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(vars)), SExpr::list(std::move(excluded))});
}
