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

using std::holds_alternative;
using std::make_shared;
using std::make_unique;
using std::map;
using std::move;
using std::unique_ptr;
using std::vector;
using std::ranges::adjacent_find;
using std::ranges::find;
using std::ranges::sort;

namespace
{
    // Whether the GAC propagator runs the cheap value-consistency pass as a
    // first stage, deferring the matching/SCC work while that pass is still
    // finding removals. Deferral splits a wake into two propagator
    // invocations and adds an unassigned-list scan per wake, so it only pays
    // when the deferred work is expensive -- that is, when the bipartite
    // variable-value graph is big. Measured on the (vars x values) product:
    // 22 x 33 = 726 (langford --size=11) is 1.36x faster staged, while
    // 10 x 10 = 100 (QWH quasigroup7) is ~2% slower, so the cutoff sits
    // between them, at the rounded geometric mean.
    constexpr std::size_t min_var_val_pairs_for_staged_gac = 256;

    // Prebuilt per-variable "v == its single value" reasons for the
    // value-consistency pass, indexed by the variable's own
    // SimpleIntegerVariableID index (offset by base). Each is a deferred
    // ExactSingleValue, so it materialises to v == whatever value v is fixed
    // to at the point of inference. Constraint-owned (moved into the
    // propagator closure), not backtracked: the table never changes during
    // search. Views and constants get no entry and fall back to inline
    // construction in the propagator.
    struct SingleValueReasons
    {
        unsigned long long base = 0;
        vector<Reason> table;
    };

    auto build_single_value_reasons(const vector<IntegerVariableID> & vars) -> SingleValueReasons
    {
        SingleValueReasons result;
        auto lo = ~0ull, hi = 0ull;
        bool any_simple = false;
        for (const auto & v : vars)
            if (auto s = std::get_if<SimpleIntegerVariableID>(&v)) {
                lo = std::min(lo, s->index);
                hi = std::max(hi, s->index);
                any_simple = true;
            }
        if (any_simple) {
            result.base = lo;
            result.table.resize(hi - lo + 1);
            for (const auto & v : vars)
                if (auto s = std::get_if<SimpleIntegerVariableID>(&v))
                    result.table[s->index - lo] = Reason{ExactSingleValue{ReasonVars{vector<IntegerVariableID>{v}}}};
        }
        return result;
    }
}

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

    // GAC wants the compressed value set. It has to be built before the
    // staging decision below, which depends on its size.
    if (holds_alternative<consistency::GAC>(_level)) {
        for (auto & var : _sanitised_vars)
            for (const auto & val : initial_state.each_value_immutable(var))
                if (_compressed_vals.end() == find(_compressed_vals, val))
                    _compressed_vals.push_back(val);
        _gac_staged = _sanitised_vars.size() * _compressed_vals.size() >= min_var_val_pairs_for_staged_gac;
    }

    // The value-consistency pass needs the not-yet-assigned variables as
    // backtrackable state: VC runs it as its whole propagator, GAC as the
    // cheap first stage of its staged propagator when the constraint is big
    // enough for staging to pay. Skipped otherwise: an unused constraint
    // state would still be saved and restored at every search node.
    if (holds_alternative<consistency::VC>(_level) || _gac_staged) {
        NonGacAllDifferentUnassigned unassigned{};
        for (auto & var : _sanitised_vars)
            if (! initial_state.has_single_value(var))
                unassigned.push_back(var);
        _unassigned_handle = initial_state.add_constraint_state(unassigned);
    }

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
            auto reasons = _gac_staged ? build_single_value_reasons(_sanitised_vars) : SingleValueReasons{};
            propagators.install(
                constraint_id(),
                [vars = move(_sanitised_vars), vals = move(_compressed_vals), value_am1_constraint_numbers = move(value_am1_constraint_numbers),
                    scratch = make_gac_all_different_scratch(), staged = _gac_staged, unassigned_handle = _unassigned_handle, reasons = move(reasons),
                    constraint_id = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    // Stage 1, cheap (only when the constraint is big enough
                    // for staging to pay; see min_var_val_pairs_for_staged_gac):
                    // push newly assigned values through the clique -- the same
                    // value-consistency pass, over the same backtrackable
                    // unassigned list, as the VC propagator below. The first
                    // flag read discards any stale value:
                    // did_anything_since_last_call_inside_propagator is set by
                    // every inference from every propagator and only cleared
                    // when read, and acting on a leftover true after an
                    // inference-free stage 1 would skip stage 2 with none of
                    // our own triggers guaranteeing a re-wake.
                    if (staged) {
                        inference.did_anything_since_last_call_inside_propagator();
                        if (! propagate_non_gac_alldifferent(unassigned_handle, state, inference, logger, constraint_id,
                                reasons.table.empty() ? nullptr : &reasons.table, reasons.base))
                            return PropagatorState::Enable; // contradiction: loop sees tracker.contradicted()

                        // If stage 1 inferred anything, defer the expensive
                        // stage: return Enable *without* an idempotence claim,
                        // so the removals just made -- all on our own on_change
                        // trigger variables -- requeue us at the round
                        // boundary. Cheaper propagators react to the removals
                        // first, and the matching/SCC stage runs once against
                        // the accumulated state instead of once per wake.
                        // Stage 2 cannot be starved: a deferral only happens
                        // when stage 1 strictly shrank a domain, which can only
                        // happen finitely often, and the engine cannot reach
                        // its fixpoint while we are still being requeued. The
                        // per-node fixpoint is therefore still exactly the GAC
                        // closure (stage 1 never removes anything GAC would
                        // not), so the search is unchanged, though propagation
                        // counts and proof shape differ from running GAC on
                        // every wake.
                        if (inference.did_anything_since_last_call_inside_propagator())
                            return PropagatorState::Enable;
                    }

                    // Stage 2, expensive: full GAC via matching + SCCs.
                    propagate_gac_all_different(
                        constraint_id, vars, vals, vector<Integer>{}, *value_am1_constraint_numbers.get(), *scratch, state, inference, logger);
                    // Idempotent: one call prunes to the GAC closure. The
                    // matching and SCCs are built from an entry snapshot, and
                    // what survives is exactly the union of maximum matchings,
                    // so a re-run deletes nothing (every remaining edge is in
                    // some maximum matching) and a matching still exists (no
                    // contradiction). Stage 1 cannot break the claim: the
                    // closure has already removed every value a newly fixed
                    // variable would push through the clique (an edge (y, v)
                    // with x fixed to v is in no maximum matching), so a
                    // re-run's stage 1 infers nothing. Duplicate scope
                    // variables never reach here (prepare rejects them), and
                    // triggers are 1:1 with the scope, so view aliasing is
                    // caught by the install-time downgrade.
                    return PropagatorState::EnableButIdempotent;
                },
                triggers);
        },
        [&](const consistency::VC &) {
            auto reasons = build_single_value_reasons(_sanitised_vars);
            propagators.install(
                constraint_id(),
                [unassigned_handle = _unassigned_handle, owner = constraint_id(), reasons = std::move(reasons)](
                    const State & state, auto & tracker, ProofLogger * const logger) -> PropagatorState {
                    if (! propagate_non_gac_alldifferent(
                            unassigned_handle, state, tracker, logger, owner, reasons.table.empty() ? nullptr : &reasons.table, reasons.base))
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

auto AllDifferent::constraint_type() const -> std::string
{
    return "all_different";
}

auto AllDifferent::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> vars;
    for (const auto & var : _vars)
        vars.push_back(tracker.s_expr_term_of(var));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(vars))});
}
