#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/constraints/all_different/hints.hh>
#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <functional>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::decay_t;
using std::function;
using std::is_same_v;
using std::pair;
using std::string;
using std::unique_ptr;
using std::variant;
using std::vector;
using std::ranges::adjacent_find;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

// Returns false if an inference contradicted (the caller must stop and not read
// state again until backtrack); true if propagation completed. Uses the
// non-throwing infer_not_equal_or_stop path so a contradiction does not unwind via
// an exception -- this propagator fails roughly once per node in circuit-style
// models, so the throw was a large per-node cost.
auto gcs::innards::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, const State & state, auto & inference,
    ProofLogger * const logger, const ConstraintID & owner, const std::vector<Reason> * single_value_reasons, unsigned long long reason_base) -> bool
{
    auto & unassigned = any_cast<NonGacAllDifferentUnassigned &>(state.get_constraint_state(unassigned_handle));

    // The reason every removal cites is "v == val", where v is a variable already
    // fixed to val. When the caller hands us a prebuilt table, look it up by v's own
    // index and return a reference -- no per-inference construction. A view/constant,
    // or a variable outside the table, falls back to building the reason inline (the
    // want_reasons() guard still applies there, since that construction is not free).
    auto reason_for = [&](const IntegerVariableID & v, Integer val, Reason & inline_storage) -> const Reason & {
        if (single_value_reasons)
            if (auto s = std::get_if<SimpleIntegerVariableID>(&v))
                if (auto idx = s->index - reason_base; idx < single_value_reasons->size())
                    return (*single_value_reasons)[idx];
        inline_storage = inference.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{{v == val}}}} : Reason{};
        return inline_storage;
    };

    vector<pair<IntegerVariableID, Integer>> to_propagate;
    {
        // Collect any newly assigned values. Erasing by swap-and-pop (order of
        // unassigned is irrelevant) keeps this O(1) per removal on a flat container.
        for (std::size_t k = 0; k < unassigned.size();) {
            auto s = unassigned[k];
            if (auto val = state.optional_single_value(s)) {
                to_propagate.emplace_back(s, *val);
                unassigned[k] = unassigned.back();
                unassigned.pop_back();
            }
            else
                ++k;
        }
    }

    while (! to_propagate.empty()) {
        auto [var, val] = to_propagate.back();
        to_propagate.pop_back();

        // The same "var == val" reason justifies every removal this popped variable
        // triggers, so resolve it once here and reuse the reference in the inner loop.
        Reason var_inline_storage;
        const Reason & var_assigned_reason = reason_for(var, val, var_inline_storage);

        for (auto other : to_propagate) {
            if (other.second == val) {
                // we're already in a contradicting state
                Reason other_inline_storage;
                if (! inference.infer_not_equal_or_stop(
                        logger, var, val, JustifyUsingRUP{hints::AllDifferent{owner}}, reason_for(other.first, val, other_inline_storage)))
                    return false;
            }
        }

        for (std::size_t k = 0; k < unassigned.size();) {
            auto other = unassigned[k];
            // var is no longer in unassigned (it was popped into to_propagate), so the
            // other != var guard from the list version always held; kept for safety.
            if (other != var) {
                if (! inference.infer_not_equal_or_stop(logger, other, val, JustifyUsingRUP{hints::AllDifferent{owner}}, var_assigned_reason))
                    return false;
                if (auto other_val = state.optional_single_value(other)) {
                    to_propagate.emplace_back(other, *other_val);
                    unassigned[k] = unassigned.back();
                    unassigned.pop_back();
                    continue;
                }
            }
            ++k;
        }
    }

    return true;
}

VCAllDifferent::VCAllDifferent(vector<IntegerVariableID> v) : _vars(move(v))
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
    NonGacAllDifferentUnassigned unassigned{};
    for (auto & var : _sanitised_vars)
        if (! initial_state.has_single_value(var))
            unassigned.push_back(var);

    _unassigned_handle = initial_state.add_constraint_state(unassigned);
    return true;
}

auto VCAllDifferent::define_proof_model(ProofModel & model) -> void
{
    define_clique_not_equals_encoding(model, _constraint_id, _sanitised_vars);
}

auto VCAllDifferent::install_propagators(Propagators & propagators) -> void
{
    if (_has_duplicate_vars) {
        install_clique_duplicate_contradiction_initialiser(propagators, hints::AllDifferent{constraint_id()});
        return;
    }

    Triggers triggers;
    triggers.on_change = {_sanitised_vars.begin(), _sanitised_vars.end()};

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
            if (! propagate_non_gac_alldifferent(unassigned_handle, state, tracker, logger, owner, reasons.empty() ? nullptr : &reasons, reason_base))
                return PropagatorState::Enable; // contradiction: loop sees tracker.contradicted()
            return PropagatorState::Enable;
        },
        triggers);
}

template auto gcs::innards::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, const State & state,
    SimpleInferenceTracker & inference_tracker, ProofLogger * const logger, const ConstraintID & owner,
    const std::vector<Reason> * single_value_reasons, unsigned long long reason_base) -> bool;

template auto gcs::innards::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, const State & state,
    EagerProofLoggingInferenceTracker & inference_tracker, ProofLogger * const logger, const ConstraintID & owner,
    const std::vector<Reason> * single_value_reasons, unsigned long long reason_base) -> bool;

auto VCAllDifferent::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> vars;
    for (const auto & var : _vars)
        vars.push_back(tracker.s_expr_term_of(var));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("all_different"), SExpr::list(std::move(vars))});
}
