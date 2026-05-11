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
#include <iterator>
#include <map>
#include <optional>
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
    // Such values can never be taken anyway, so they neither shape the OPB
    // encoding nor warrant phantom edges in the propagator's matching graph.
    _sanitised_excluded = move(_excluded);
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
            auto run_end = find_if(next(it), _sanitised_vars.end(),
                [&](const IntegerVariableID & v) { return v != *it; });
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
    _duplicate_selectors = define_clique_not_equals_except_encoding(model, _sanitised_vars, _sanitised_excluded);
}

auto AllDifferentExcept::install_propagators(Propagators & propagators) -> void
{
    if (_has_duplicates && _sanitised_excluded.empty()) {
        // Same shape as plain AllDifferent on duplicates: with empty excluded,
        // the encoding's half-reified relaxation terms disappear and the
        // duplicate pair's two constraints jointly force selector and
        // !selector simultaneously. Install the shared clique-contradiction
        // initialiser instead of the per-value path below; the propagator
        // also can't run, so we early-return.
        auto witness = _duplicate_selectors.empty()
            ? std::nullopt
            : std::optional{*_duplicate_selectors.begin()};
        install_clique_duplicate_contradiction_initialiser(propagators, move(witness));
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
            [duplicated_vars = move(_duplicated_vars),
                excluded = _sanitised_excluded,
                duplicate_selectors = move(_duplicate_selectors)](
                const State & state, auto & inf, ProofLogger * const logger) -> void {
                for (const auto & x : duplicated_vars) {
                    vector<Integer> non_excluded_values;
                    for (const auto & v : state.each_value_immutable(x))
                        if (find(excluded.begin(), excluded.end(), v) == excluded.end())
                            non_excluded_values.push_back(v);
                    for (const auto & v : non_excluded_values) {
                        inf.infer(logger, x != v,
                            JustifyExplicitlyThenRUP{
                                [&logger, x, v, &duplicate_selectors](const ReasonFunction &) -> void {
                                    const auto & selector = duplicate_selectors.at(x);
                                    logger->emit(RUPProofRule{},
                                        WPBSum{} + 1_i * (x != v) + 1_i * selector >= 1_i,
                                        ProofLevel::Temporary);
                                    logger->emit(RUPProofRule{},
                                        WPBSum{} + 1_i * (x != v) + 1_i * (! selector) >= 1_i,
                                        ProofLevel::Temporary);
                                }},
                            []() -> Reason { return Reason{}; });
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
        [vars = move(_sanitised_vars),
            vals = move(_compressed_vals),
            excluded = move(_sanitised_excluded),
            value_am1_constraint_numbers = _value_am1_constraint_numbers](const State & state, auto & inference,
            ProofLogger * const logger) -> PropagatorState {
            propagate_gac_all_different(vars, vals, excluded, *value_am1_constraint_numbers.get(), state, inference, logger);
            return PropagatorState::Enable;
        },
        triggers);
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
