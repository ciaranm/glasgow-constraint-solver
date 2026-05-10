#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <functional>
#include <list>
#include <optional>
#include <sstream>
#include <type_traits>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::decay_t;
using std::function;
using std::is_same_v;
using std::list;
using std::pair;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::variant;
using std::vector;
using std::ranges::adjacent_find;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

auto gcs::innards::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle,
    const State & state, auto & inference, ProofLogger * const logger) -> void
{
    auto & unassigned = any_cast<list<IntegerVariableID> &>(state.get_constraint_state(unassigned_handle));

    vector<pair<IntegerVariableID, Integer>> to_propagate;
    {
        // Collect any newly assigned values
        for (auto i = unassigned.begin(); i != unassigned.end();) {
            auto s = *i;
            if (auto val = state.optional_single_value(s)) {
                to_propagate.emplace_back(s, *val);
                unassigned.erase(i++);
            }
            else
                i++;
        }
    }

    while (! to_propagate.empty()) {
        auto [var, val] = to_propagate.back();
        to_propagate.pop_back();
        auto i = unassigned.begin();

        for (auto other : to_propagate) {
            if (other.second == val) {
                // we're already in a contradicting state
                inference.infer_not_equal(logger, var, val, JustifyUsingRUP{},
                    ReasonFunction{[var = other.first, val = val]() { return Reason{{var == val}}; }});
            }
        }

        while (i != unassigned.end()) {
            auto other = *i;
            if (other != var) {
                inference.infer_not_equal(logger, other, val, JustifyUsingRUP{}, ReasonFunction{[var = var, val = val]() { return Reason{{var == val}}; }});
                if (auto other_val = state.optional_single_value(other)) {
                    to_propagate.emplace_back(other, *other_val);
                    unassigned.erase(i++);
                }
                else
                    ++i;
            }
        }
    }
}

VCAllDifferent::VCAllDifferent(vector<IntegerVariableID> v) :
    _vars(move(v))
{
}

auto VCAllDifferent::clone() const -> unique_ptr<Constraint>
{
    return make_unique<VCAllDifferent>(_vars);
}

auto VCAllDifferent::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto VCAllDifferent::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _sanitised_vars = move(_vars);
    sort(_sanitised_vars);
    _has_duplicate_vars = adjacent_find(_sanitised_vars) != _sanitised_vars.end();
    if (_has_duplicate_vars) {
        // The bipartite-matching propagator can't model duplicate left-vertices,
        // so install_propagators will only install a contradiction initialiser.
        // We still let define_proof_model run unchanged: the encoding emits a
        // self-contradicting half-reified pair for the duplicated variable,
        // which the initialiser cites in its proof.
        return true;
    }

    // Keep track of unassigned vars
    // Might want a more centralised way of doing this in future.
    list<IntegerVariableID> unassigned{};
    for (auto & var : _sanitised_vars)
        if (! initial_state.has_single_value(var))
            unassigned.push_back(var);

    _unassigned_handle = initial_state.add_constraint_state(unassigned);
    return true;
}

auto VCAllDifferent::define_proof_model(ProofModel & model) -> void
{
    _duplicate_selectors = define_clique_not_equals_encoding(model, _sanitised_vars);
}

auto VCAllDifferent::install_propagators(Propagators & propagators) -> void
{
    if (_has_duplicate_vars) {
        install_clique_duplicate_contradiction_initialiser(propagators, move(_duplicate_selectors));
        return;
    }

    Triggers triggers;
    triggers.on_change = {_sanitised_vars.begin(), _sanitised_vars.end()};

    propagators.install(
        [unassigned_handle = _unassigned_handle](const State & state, auto & tracker, ProofLogger * const logger) -> PropagatorState {
            propagate_non_gac_alldifferent(unassigned_handle, state, tracker, logger);
            return PropagatorState::Enable;
        },
        triggers);
}

template auto gcs::innards::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, const State & state,
    SimpleInferenceTracker & inference_tracker, ProofLogger * const logger) -> void;

template auto gcs::innards::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, const State & state,
    EagerProofLoggingInferenceTracker & inference_tracker, ProofLogger * const logger) -> void;

auto VCAllDifferent::s_exprify(const string & name, const innards::ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} all_different (", name);
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ")");

    return s.str();
}
