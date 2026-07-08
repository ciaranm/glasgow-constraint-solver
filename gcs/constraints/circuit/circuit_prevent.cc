#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/constraints/circuit/circuit_base.hh>
#include <gcs/constraints/circuit/circuit_prevent.hh>
#include <gcs/constraints/circuit/hints.hh>

#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/propagators.hh>

#include <any>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::circuit;

using std::any_cast;
using std::size_t;
using std::vector;

namespace
{
    // Incremental "prevent" state: the fixed successor edges partition the nodes into
    // simple paths (chains). For each node we record the chain it belongs to by its
    // endpoints. These are maintained in O(1) as edges are fixed and restored on
    // backtrack (held as backtrackable constraint state), rather than recomputed from
    // scratch each call. orig[v] is valid when v is a chain *end*, dest[v]/len[v] when
    // v is a chain *start* -- which is exactly how they are queried below.
    struct PreventChainData
    {
        std::vector<long> orig;      // start node of the chain ending at this node
        std::vector<long> dest;      // end node of the chain starting at this node
        std::vector<long> len;       // number of fixed edges in the chain starting at this node
        std::vector<long> unspliced; // node indices whose fixed successor edge is not yet folded in
    };

    // Fold every newly-fixed edge into the chain endpoints and make the same inferences
    // the from-scratch prevent_small_cycles would: forbid a short chain from closing
    // (succ[end] != start), force the full chain to close (succ[end] == start), and
    // contradict if a sub-cycle has actually closed. Each edge is processed once, in
    // O(1); the outer loop re-runs only because forcing an edge fixes a new one.
    // Returns whether any successor became single-valued along the way -- the one
    // event whose alldifferent consequences this pass does not handle itself, so the
    // caller knows whether another alldifferent pass is needed.
    auto prevent_small_cycles_incrementally(const vector<IntegerVariableID> & succ, const ConstraintID & owner, const PosVarDataMap & pos_var_data,
        const ConstraintStateHandle & chain_handle, const State & state, auto & inference, ProofLogger * const logger) -> bool
    {
        bool fixed_a_successor = false;
        auto & chain = any_cast<PreventChainData &>(state.get_constraint_state(chain_handle));
        auto n = static_cast<long>(succ.size());

        bool progress = true;
        while (progress) {
            progress = false;
            for (std::size_t k = 0; k < chain.unspliced.size();) {
                auto i = chain.unspliced[k];
                auto val = state.optional_single_value(succ[i]);
                if (! val) {
                    ++k;
                    continue;
                }

                // Edge i -> j is fixed; remove i from the unspliced set (swap-and-pop)
                // and fold it in. i was a chain end (its successor had been unfixed);
                // by all-different j had no predecessor, so j is a chain start.
                auto j = val->raw_value;
                chain.unspliced[k] = chain.unspliced.back();
                chain.unspliced.pop_back();
                progress = true;

                auto o = chain.orig[i];
                if (j == o) {
                    // This edge closes the chain o..i into a cycle of len[o] + 1 edges.
                    if (chain.len[o] + 1 < n) {
                        if (logger && logger->get_assertion_level() == AssertionLevel::Off)
                            output_cycle_to_proof(succ, o, chain.len[o] + 1, pos_var_data, state, *logger);
                        inference.contradiction(logger, JustifyUsingRUP{hints::Circuit{owner}}, generic_reason(succ));
                    }
                    // else: the final edge of the full Hamiltonian cycle -- nothing to infer.
                }
                else {
                    // Splice chain (o..i) and chain (j..d) into (o..d).
                    auto d = chain.dest[j];
                    auto new_len = chain.len[o] + 1 + chain.len[j];
                    chain.dest[o] = d;
                    chain.orig[d] = o;
                    chain.len[o] = new_len;
                    if (new_len < n - 1) {
                        auto justf = [&](const ReasonLiterals &) {
                            output_cycle_to_proof(succ, o, new_len, pos_var_data, state, *logger, Integer{d}, Integer{o});
                        };
                        inference.infer(
                            logger, succ[d] != Integer{o}, JustifyExplicitly{justf, ThenRUP::Yes, hints::Circuit{owner}}, generic_reason(succ));
                        if (state.optional_single_value(succ[d]))
                            fixed_a_successor = true;
                    }
                    else {
                        // The chain spans every node; it must close to complete the tour.
                        inference.infer(logger, succ[d] == Integer{o}, JustifyUsingRUP{hints::Circuit{owner}}, generic_reason(succ));
                        fixed_a_successor = true;
                    }
                }
            }
        }

        return fixed_a_successor;
    }

}

auto gcs::innards::circuit::propagate_circuit_using_prevent(const std::vector<IntegerVariableID> & succ, const ConstraintID & owner,
    const PosVarDataMap & pos_var_data, const ConstraintStateHandle & unassigned_handle, const ConstraintStateHandle & chain_handle,
    const State & state, auto & inference, ProofLogger * const logger) -> void
{
    // Each phase runs its own internal cascade to quiescence, but they feed
    // each other: a small-cycle prevention (succ[end] != start) or a forced
    // closing (succ[end] == start) can fix a successor, whose alldifferent
    // consequences -- and any chain work those fixings cascade into -- used
    // to be caught only by the self-requeue. Alternate the phases until the
    // prevention pass stops fixing successors (mere removals need no
    // alldifferent attention, so the common run still makes exactly one pass
    // of each), so a single call reaches this propagator's own fixpoint and
    // the caller can claim idempotence.
    while (true) {
        if (! propagate_non_gac_alldifferent(unassigned_handle, state, inference, logger, owner))
            return; // contradiction: the cycle checks below would read junk state; the loop sees contradicted()
        if (! prevent_small_cycles_incrementally(succ, owner, pos_var_data, chain_handle, state, inference, logger))
            return;
    }
}

template auto gcs::innards::circuit::propagate_circuit_using_prevent(const std::vector<IntegerVariableID> & succ, const ConstraintID & owner,
    const PosVarDataMap & pos_var_data, const ConstraintStateHandle & unassigned_handle, const ConstraintStateHandle & chain_handle,
    const State & state, SimpleInferenceTracker & inference, ProofLogger * const logger) -> void;

template auto gcs::innards::circuit::propagate_circuit_using_prevent(const std::vector<IntegerVariableID> & succ, const ConstraintID & owner,
    const PosVarDataMap & pos_var_data, const ConstraintStateHandle & unassigned_handle, const ConstraintStateHandle & chain_handle,
    const State & state, EagerProofLoggingInferenceTracker & inference, ProofLogger * const logger) -> void;

auto gcs::innards::circuit::install_circuit_prevent(Propagators & propagators, State & initial_state, const ConstraintID & owner,
    const vector<IntegerVariableID> & succ, PosVarDataMap pos_var_data) -> void
{
    // Keep track of unassigned vars
    NonGacAllDifferentUnassigned unassigned{};
    for (auto v : succ) {
        unassigned.emplace_back(v);
    }
    auto unassigned_handle = initial_state.add_constraint_state(unassigned);

    // Backtrackable chain endpoints for the incremental small-cycle prevention. Each
    // node starts as its own length-zero chain; edges fold in as successors are fixed.
    auto num_nodes = succ.size();
    PreventChainData chain;
    chain.orig.resize(num_nodes);
    chain.dest.resize(num_nodes);
    chain.len.assign(num_nodes, 0);
    chain.unspliced.resize(num_nodes);
    for (size_t i = 0; i < num_nodes; ++i) {
        chain.orig[i] = static_cast<long>(i);
        chain.dest[i] = static_cast<long>(i);
        chain.unspliced[i] = static_cast<long>(i);
    }
    auto chain_handle = initial_state.add_constraint_state(std::move(chain));

    Triggers triggers;
    triggers.on_instantiated = {succ.begin(), succ.end()};
    propagators.install(
        owner,
        [succ, owner, pvd = std::move(pos_var_data), unassigned_handle = unassigned_handle, chain_handle = chain_handle](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            propagate_circuit_using_prevent(succ, owner, pvd, unassigned_handle, chain_handle, state, inference, logger);
            // Idempotent: propagate_circuit_using_prevent alternates its
            // alldifferent and small-cycle passes until the latter stops
            // inferring, so at return no unassigned successor is
            // single-valued and every fixed edge is folded into its chain
            // with the closing inference made -- a re-run finds nothing.
            // (This was the propagator whose skipped self-requeue made the
            // global-skip prototype unsound on tsp; the alternation is what
            // makes the claim honest.) Triggers are 1:1 with the scope, so
            // view aliasing is caught by the install-time downgrade, and the
            // Circuit constructor rejects repeated variable handles outright.
            return PropagatorState::EnableButIdempotent;
        },
        triggers);
}
