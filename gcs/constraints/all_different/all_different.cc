#include <gcs/constraint.hh>
#include <gcs/constraints/all_different/all_different.hh>
#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/constraints/all_different/hints.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <map>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::make_unique;
using std::map;
using std::move;
using std::unique_ptr;
using std::vector;
using std::ranges::adjacent_find;
using std::ranges::find;
using std::ranges::sort;

AllDifferent::AllDifferent(vector<IntegerVariableID> v) : _vars(move(v))
{
}

auto AllDifferent::with_consistency(AllDifferentConsistency level) -> AllDifferent &
{
    _level = level;
    return *this;
}

auto AllDifferent::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto AllDifferent::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _sanitised_vars = move(_vars);
    sort(_sanitised_vars);
    _has_duplicate_vars = adjacent_find(_sanitised_vars) != _sanitised_vars.end();
    if (_has_duplicate_vars) {
        // Neither propagator can model duplicate left-vertices, so
        // install_propagators only installs a contradiction initialiser. We
        // still let define_proof_model run unchanged: the encoding emits a
        // self-contradicting half-reified pair for the duplicated variable
        // for the initialiser to cite.
        return true;
    }

    // Set up only what the requested propagator needs: GAC wants the compressed
    // value set; VC wants the not-yet-assigned variables as backtrackable state.
    overloaded{[&](const consistency::GAC &) {
                   for (auto & var : _sanitised_vars)
                       for (const auto & val : initial_state.each_value_immutable(var))
                           if (_compressed_vals.end() == find(_compressed_vals, val))
                               _compressed_vals.push_back(val);
               },
        [&](const consistency::VC &) {
            NonGacAllDifferentUnassigned unassigned{};
            for (auto & var : _sanitised_vars)
                if (! initial_state.has_single_value(var))
                    unassigned.push_back(var);
            _unassigned_handle = initial_state.add_constraint_state(unassigned);
        }}
        .visit(_level);

    return true;
}

auto AllDifferent::define_proof_model(ProofModel & model) -> void
{
    // Identical for both consistency levels: the choice is a propagation-strength
    // knob and never changes the encoding.
    define_clique_not_equals_encoding(model, _constraint_id, _sanitised_vars);
}

auto AllDifferent::install_propagators(Propagators & propagators) -> void
{
    if (_has_duplicate_vars) {
        install_clique_duplicate_contradiction_initialiser(propagators, hints::AllDifferent{constraint_id()});
        return;
    }

    Triggers triggers;
    triggers.on_change = {_sanitised_vars.begin(), _sanitised_vars.end()};

    overloaded{
        [&](const consistency::GAC &) {
            auto value_am1_constraint_numbers = make_shared<map<Integer, ProofLine>>();
            propagators.install(
                constraint_id(),
                [vars = move(_sanitised_vars), vals = move(_compressed_vals), value_am1_constraint_numbers = move(value_am1_constraint_numbers),
                    constraint_id = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    propagate_gac_all_different(
                        constraint_id, vars, vals, vector<Integer>{}, *value_am1_constraint_numbers.get(), state, inference, logger);
                    // Idempotent: one call prunes to the GAC closure. The
                    // matching and SCCs are built from an entry snapshot, and
                    // what survives is exactly the union of maximum matchings,
                    // so a re-run deletes nothing (every remaining edge is in
                    // some maximum matching) and a matching still exists (no
                    // contradiction). Duplicate scope variables never reach here
                    // (prepare rejects them), and triggers are 1:1 with the
                    // scope, so view aliasing is caught by the install-time
                    // downgrade.
                    return PropagatorState::EnableButIdempotent;
                },
                triggers);
        },
        [&](const consistency::VC &) {
            // Prebuild the per-variable "v == its single value" reason once, indexed by the
            // variable's own SimpleIntegerVariableID index (offset by reason_base). This is a
            // deferred ExactSingleValue, so it materialises to v == whatever value v is fixed
            // to at the point of inference. It is constraint-owned (moved into the propagator
            // closure), not backtracked: the table never changes during search. Views and
            // constants get no entry and fall back to inline construction in the propagator.
            unsigned long long reason_base = 0;
            vector<Reason> reasons;
            {
                auto lo = ~0ull, hi = 0ull;
                bool any_simple = false;
                for (const auto & v : _sanitised_vars)
                    if (auto s = std::get_if<SimpleIntegerVariableID>(&v)) {
                        lo = std::min(lo, s->index);
                        hi = std::max(hi, s->index);
                        any_simple = true;
                    }
                if (any_simple) {
                    reason_base = lo;
                    reasons.resize(hi - lo + 1);
                    for (const auto & v : _sanitised_vars)
                        if (auto s = std::get_if<SimpleIntegerVariableID>(&v))
                            reasons[s->index - lo] = Reason{ExactSingleValue{ReasonVars{vector<IntegerVariableID>{v}}}};
                }
            }

            propagators.install(
                constraint_id(),
                [unassigned_handle = _unassigned_handle, owner = constraint_id(), reasons = std::move(reasons), reason_base](
                    const State & state, auto & tracker, ProofLogger * const logger) -> PropagatorState {
                    if (! propagate_non_gac_alldifferent(
                            unassigned_handle, state, tracker, logger, owner, reasons.empty() ? nullptr : &reasons, reason_base))
                        return PropagatorState::Enable; // contradiction: loop sees tracker.contradicted()
                    // Idempotent: the to_propagate worklist re-checks
                    // optional_single_value after every removal and processes the
                    // whole cascade in this call, so at return no variable left in
                    // unassigned is single-valued and a re-run collects nothing.
                    // Duplicate scope variables never reach here (prepare rejects
                    // them), and triggers are 1:1 with the scope, so view aliasing
                    // is caught by the install-time downgrade. The claim is this
                    // call site's, deliberately not the shared helper's: circuit
                    // wraps the same helper in propagators that do more work in
                    // the same run and must not claim.
                    return PropagatorState::EnableButIdempotent;
                },
                triggers);
        }}
        .visit(_level);
}

auto AllDifferent::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<AllDifferent>(_vars);
    cloned->with_consistency(_level);
    return cloned;
}

auto AllDifferent::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> vars;
    for (const auto & var : _vars)
        vars.push_back(tracker.s_expr_term_of(var));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("all_different"), SExpr::list(std::move(vars))});
}
