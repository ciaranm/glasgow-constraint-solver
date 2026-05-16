#include <gcs/constraints/bin_packing.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::make_unique;
using std::move;
using std::pair;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

namespace
{
    // Stage 3 partial-load DAG per bin. Each layer i ∈ [0..n] holds the set of
    // partial-sum values w ∈ [0..C_b] that survived static reduction: forward
    // reachability from (0, 0) under initial item domains, intersected with
    // backward reachability from the layer-n accepting set (w ∈ initial
    // dom(loads[b]) for variable-load, or w ≤ caps[b] for constant-cap).
    struct PerBinDag
    {
        // nodes_at[layer] = surviving partial-sum w values at this layer
        // (sorted, deduplicated). Always contains 0 at layer 0.
        vector<vector<long long>> nodes_at;
        // Membership index over nodes_at[layer], for O(1) lookups during the
        // per-call sweep.
        vector<unordered_set<long long>> node_set;
    };

    // Reified Top-level proof flags for one bin's DAG, populated by the
    // install_initialiser callback (so empty if proofs are disabled, or if
    // bounds_only is set on the BinPacking constructor).
    struct PerBinFlags
    {
        struct NodeFlags
        {
            ProofFlag g_up; // sum_{j<i} sizes[j] * (items[j]==b) >= w
            ProofFlag g_dn; // sum_{j<i} sizes[j] * (items[j]==b) <= w
            ProofFlag s;    // g_up ∧ g_dn (sum exactly w)
        };
        vector<unordered_map<long long, NodeFlags>> flags;
    };

    // Cap on per-bin partial-sum values:
    // min(upper bound of loads[b] [variable-load form] or capacities[b]
    //     [constant-cap form], sum of all item sizes).
    auto per_bin_cap(const State & state, const vector<Integer> & sizes,
        bool have_loads, const vector<IntegerVariableID> & loads,
        const vector<Integer> & capacities, size_t b) -> long long
    {
        long long total = 0;
        for (auto & s : sizes)
            total += s.raw_value;
        long long ext = have_loads
            ? state.upper_bound(loads[b]).raw_value
            : capacities[b].raw_value;
        return std::min(total, ext);
    }

    // Build the static-reduced DAG for one bin from the initial state. Forward
    // pass: starting from {0} at layer 0, follow whichever of the two edges
    // are admissible given the initial items[i] domain (== b if b ∈ dom,
    // != b if dom \ {b} is non-empty). Backward pass: from the accepting
    // terminals at layer n, propagate backward similarly. The DAG's nodes
    // at each layer are the intersection.
    auto build_dag(const State & state, const vector<IntegerVariableID> & items,
        const vector<Integer> & sizes, bool have_loads,
        const vector<IntegerVariableID> & loads, const vector<Integer> & capacities,
        size_t b, long long cap) -> PerBinDag
    {
        auto n = items.size();
        auto bin_idx = Integer{static_cast<long long>(b)};

        // For each layer i ∈ [0..n], which edges are admissible from layer i
        // (into layer i+1)?
        vector<bool> can_be_b(n), can_be_notb(n);
        for (size_t i = 0; i < n; ++i) {
            can_be_b[i] = state.in_domain(items[i], bin_idx);
            auto v = state.optional_single_value(items[i]);
            can_be_notb[i] = ! (v && *v == bin_idx);
        }

        // Forward reachable from (0, 0).
        vector<unordered_set<long long>> fwd(n + 1);
        fwd[0].insert(0);
        for (size_t i = 0; i < n; ++i) {
            for (auto w : fwd[i]) {
                if (can_be_notb[i])
                    fwd[i + 1].insert(w);
                if (can_be_b[i]) {
                    auto w2 = w + sizes[i].raw_value;
                    if (w2 <= cap)
                        fwd[i + 1].insert(w2);
                }
            }
        }

        // Backward reachable from accepting terminals.
        vector<unordered_set<long long>> bwd(n + 1);
        for (long long w = 0; w <= cap; ++w) {
            bool accept = have_loads
                ? state.in_domain(loads[b], Integer{w})
                : (w <= capacities[b].raw_value);
            if (accept)
                bwd[n].insert(w);
        }
        for (long long i = static_cast<long long>(n) - 1; i >= 0; --i) {
            for (auto w : bwd[i + 1]) {
                if (can_be_notb[i])
                    bwd[i].insert(w);
                if (can_be_b[i]) {
                    auto w_prev = w - sizes[i].raw_value;
                    if (w_prev >= 0)
                        bwd[i].insert(w_prev);
                }
            }
        }

        PerBinDag dag;
        dag.nodes_at.assign(n + 1, {});
        dag.node_set.assign(n + 1, {});
        for (size_t i = 0; i <= n; ++i) {
            for (auto w : fwd[i])
                if (bwd[i].contains(w))
                    dag.nodes_at[i].push_back(w);
            std::ranges::sort(dag.nodes_at[i]);
            dag.node_set[i].insert(dag.nodes_at[i].begin(), dag.nodes_at[i].end());
        }
        return dag;
    }

    // Build the running sum WPBSum for "sum_{j < i} sizes[j] * (items[j]==b)".
    // Used inside the Top-level scaffolding to define each g_up / g_dn flag's
    // reification.
    auto running_sum(const vector<IntegerVariableID> & items,
        const vector<Integer> & sizes, Integer bin_idx, size_t i) -> WPBSum
    {
        WPBSum s;
        for (size_t j = 0; j < i; ++j)
            s += sizes[j] * (items[j] == bin_idx);
        return s;
    }

    auto emit_bin_scaffolding(ProofLogger * logger, size_t b,
        const vector<IntegerVariableID> & items, const vector<Integer> & sizes,
        const PerBinDag & dag, PerBinFlags & flags) -> void
    {
        auto n = items.size();
        auto bin_idx = Integer{static_cast<long long>(b)};

        flags.flags.assign(n + 1, {});
        for (size_t i = 0; i <= n; ++i) {
            auto sum_expr = running_sum(items, sizes, bin_idx, i);
            for (auto w : dag.nodes_at[i]) {
                auto wI = Integer{w};
                auto [g_up, gu_fwd, gu_rev] = logger->create_proof_flag_reifying(
                    sum_expr >= wI, format("bpup_{}_{}_{}", b, i, w), ProofLevel::Top);
                auto [g_dn, gd_fwd, gd_rev] = logger->create_proof_flag_reifying(
                    sum_expr <= wI, format("bpdn_{}_{}_{}", b, i, w), ProofLevel::Top);
                auto [s, s_fwd, s_rev] = logger->create_proof_flag_reifying(
                    WPBSum{} + 1_i * g_up + 1_i * g_dn >= 2_i,
                    format("bpat_{}_{}_{}", b, i, w), ProofLevel::Top);
                flags.flags[i].emplace(w, PerBinFlags::NodeFlags{g_up, g_dn, s});
                (void) gu_fwd;
                (void) gu_rev;
                (void) gd_fwd;
                (void) gd_rev;
                (void) s_fwd;
                (void) s_rev;
            }
        }
    }

    // Stage 3 per-bin DAG sweep. For each bin, recompute alive (i, w) nodes
    // under the current item domains (forward + backward reachability), then
    // for each candidate items[i] == b that has no support at any alive (i, w)
    // with (i+1, w + sizes[i]) also alive, prune items[i] != b.
    //
    // Proof: a plain JustifyUsingRUP at the prune site is sufficient — the
    // chain through the bridge's reified flags + the natural per-bin OPB
    // equation gives VeriPB enough unit-propagation reach to close the
    // contradiction. No explicit per-node dead-node lines are emitted (in
    // contrast to MDD::propagate_mdd, where the at-each-layer exactly-one
    // OPB axiom requires them); the inequality reifications carry that
    // chain implicitly. If a future case is found where RUP can't close
    // the prune, the structured chain in MDD's log_additional_inference is
    // the template to copy here.
    auto run_stage3_for_bin(const State & state, auto & inference, ProofLogger * logger,
        const vector<IntegerVariableID> & items, const vector<Integer> & sizes,
        const PerBinDag & dag, const PerBinFlags & flags, size_t b,
        const ReasonFunction & reason) -> void
    {
        auto n = items.size();
        auto bin_idx = Integer{static_cast<long long>(b)};

        vector<bool> can_be_b(n), can_be_notb(n);
        for (size_t i = 0; i < n; ++i) {
            can_be_b[i] = state.in_domain(items[i], bin_idx);
            auto v = state.optional_single_value(items[i]);
            can_be_notb[i] = ! (v && *v == bin_idx);
        }

        // Forward reachability under current domains, restricted to static DAG.
        vector<unordered_set<long long>> fwd(n + 1);
        if (dag.node_set[0].contains(0))
            fwd[0].insert(0);
        for (size_t i = 0; i < n; ++i) {
            for (auto w : fwd[i]) {
                if (can_be_notb[i] && dag.node_set[i + 1].contains(w))
                    fwd[i + 1].insert(w);
                if (can_be_b[i]) {
                    auto w2 = w + sizes[i].raw_value;
                    if (dag.node_set[i + 1].contains(w2))
                        fwd[i + 1].insert(w2);
                }
            }
        }

        // Backward reachability from accepting terminals (the layer-n nodes
        // already encode the acceptance predicate via static reduction).
        vector<unordered_set<long long>> bwd(n + 1);
        for (auto w : dag.nodes_at[n])
            if (fwd[n].contains(w))
                bwd[n].insert(w);
        for (long long i = static_cast<long long>(n) - 1; i >= 0; --i) {
            for (auto w : bwd[i + 1]) {
                if (can_be_notb[i] && dag.node_set[i].contains(w))
                    bwd[i].insert(w);
                if (can_be_b[i]) {
                    auto w_prev = w - sizes[i].raw_value;
                    if (dag.node_set[i].contains(w_prev))
                        bwd[i].insert(w_prev);
                }
            }
        }

        // Alive = forward ∩ backward.
        vector<unordered_set<long long>> alive(n + 1);
        for (size_t i = 0; i <= n; ++i)
            for (auto w : fwd[i])
                if (bwd[i].contains(w))
                    alive[i].insert(w);

        (void) flags;

        // Prune items[i] != b when no support exists in the alive DAG.
        for (size_t i = 0; i < n; ++i) {
            if (! can_be_b[i])
                continue;
            bool supported = false;
            for (auto w : alive[i]) {
                auto w2 = w + sizes[i].raw_value;
                if (alive[i + 1].contains(w2)) {
                    supported = true;
                    break;
                }
            }
            if (! supported)
                inference.infer_not_equal(logger, items[i], bin_idx,
                    JustifyUsingRUP{}, reason);
        }
    }

    auto run_stage2(const State & state, auto & inference, ProofLogger * logger,
        const vector<IntegerVariableID> & items, const vector<Integer> & sizes,
        const vector<IntegerVariableID> & loads, const vector<Integer> & capacities,
        bool have_loads) -> void
    {
        auto num_bins = have_loads ? loads.size() : capacities.size();
        for (size_t b = 0; b < num_bins; ++b) {
            auto bin_idx = Integer(static_cast<long long>(b));

            Reason forced_reason, excluded_reason;
            Integer floor = 0_i, ceiling = 0_i;
            vector<size_t> still_possible;
            for (size_t i = 0; i < items.size(); ++i) {
                auto v = state.optional_single_value(items[i]);
                if (v && *v == bin_idx) {
                    floor += sizes[i];
                    ceiling += sizes[i];
                    forced_reason.emplace_back(items[i] == bin_idx);
                }
                else if (! state.in_domain(items[i], bin_idx)) {
                    excluded_reason.emplace_back(items[i] != bin_idx);
                }
                else {
                    still_possible.push_back(i);
                    ceiling += sizes[i];
                }
            }

            if (have_loads) {
                auto load_lo = state.lower_bound(loads[b]);
                auto load_hi = state.upper_bound(loads[b]);

                if (floor > load_lo) {
                    inference.infer_greater_than_or_equal(logger, loads[b], floor,
                        JustifyUsingRUP{}, [r = forced_reason]() { return r; });
                    load_lo = floor;
                }
                if (ceiling < load_hi) {
                    inference.infer_less_than(logger, loads[b], ceiling + 1_i,
                        JustifyUsingRUP{}, [r = excluded_reason]() { return r; });
                    load_hi = ceiling;
                }

                for (auto i : still_possible) {
                    if (floor + sizes[i] > load_hi) {
                        Reason r = forced_reason;
                        r.emplace_back(loads[b] < load_hi + 1_i);
                        inference.infer_not_equal(logger, items[i], bin_idx,
                            JustifyUsingRUP{}, [r = move(r)]() { return r; });
                    }
                    else if (ceiling - sizes[i] < load_lo) {
                        Reason r = excluded_reason;
                        r.emplace_back(loads[b] >= load_lo);
                        inference.infer_equal(logger, items[i], bin_idx,
                            JustifyUsingRUP{}, [r = move(r)]() { return r; });
                    }
                }
            }
            else {
                if (floor > capacities[b]) {
                    inference.contradiction(logger, JustifyUsingRUP{},
                        [r = forced_reason]() { return r; });
                }
                for (auto i : still_possible) {
                    if (floor + sizes[i] > capacities[b]) {
                        inference.infer_not_equal(logger, items[i], bin_idx,
                            JustifyUsingRUP{}, [r = forced_reason]() { return r; });
                    }
                }
            }
        }
    }
}

struct BinPacking::DagBridge
{
    vector<PerBinDag> dags;
    vector<PerBinFlags> flags;
};

BinPacking::BinPacking(vector<IntegerVariableID> items, vector<Integer> sizes,
    vector<IntegerVariableID> loads, bool bounds_only) :
    _items(move(items)),
    _sizes(move(sizes)),
    _loads(move(loads)),
    _capacities(),
    _have_loads(true),
    _bounds_only(bounds_only)
{
}

BinPacking::BinPacking(vector<IntegerVariableID> items, vector<Integer> sizes,
    vector<Integer> capacities, bool bounds_only) :
    _items(move(items)),
    _sizes(move(sizes)),
    _loads(),
    _capacities(move(capacities)),
    _have_loads(false),
    _bounds_only(bounds_only)
{
}

auto BinPacking::clone() const -> unique_ptr<Constraint>
{
    if (_have_loads)
        return make_unique<BinPacking>(_items, _sizes, _loads, _bounds_only);
    return make_unique<BinPacking>(_items, _sizes, _capacities, _bounds_only);
}

auto BinPacking::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto BinPacking::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    if (_items.size() != _sizes.size())
        throw InvalidProblemDefinitionException{"BinPacking: items and sizes must have the same size"};

    for (auto & s : _sizes)
        if (s < 0_i)
            throw InvalidProblemDefinitionException{"BinPacking: item sizes must be non-negative"};

    auto num_bins = _have_loads ? _loads.size() : _capacities.size();
    if (num_bins == 0)
        throw InvalidProblemDefinitionException{"BinPacking: at least one bin is required"};

    auto max_bin = Integer(static_cast<long long>(num_bins) - 1);
    for (auto & item : _items) {
        auto [lo, hi] = initial_state.bounds(item);
        if (lo < 0_i || hi > max_bin)
            throw InvalidProblemDefinitionException{"BinPacking: item variable domain must lie within 0..num_bins-1"};
    }

    if (_have_loads) {
        for (auto & l : _loads)
            if (initial_state.lower_bound(l) < 0_i)
                throw InvalidProblemDefinitionException{"BinPacking: load variables must be non-negative"};
    }
    else {
        for (auto & c : _capacities)
            if (c < 0_i)
                throw InvalidProblemDefinitionException{"BinPacking: capacities must be non-negative"};
    }

    if (! _bounds_only) {
        // Build the static-reduced per-bin DAGs from the initial domains. Flag
        // handles are populated later by install_initialiser (once the logger
        // is available).
        _bridge = make_shared<DagBridge>();
        _bridge->dags.reserve(num_bins);
        _bridge->flags.assign(num_bins, {});
        for (size_t b = 0; b < num_bins; ++b) {
            auto cap = per_bin_cap(initial_state, _sizes, _have_loads,
                _loads, _capacities, b);
            _bridge->dags.push_back(build_dag(initial_state, _items, _sizes,
                _have_loads, _loads, _capacities, b, cap));
        }
    }

    return true;
}

auto BinPacking::define_proof_model(ProofModel & model) -> void
{
    // Natural definition: for each bin b,
    //   sum_i { sizes[i] * [items[i] == b] } == loads[b]   (variable-load form)
    //   sum_i { sizes[i] * [items[i] == b] } <= cap[b]     (constant-cap form)
    //
    // The DAG-shaped scaffolding used by the Stage 3 GAC propagator is not
    // part of this encoding; it is emitted at ProofLevel::Top by an
    // install_initialiser, derived from these per-bin equations. See
    // dev_docs/bin-packing.md.
    auto num_bins = _have_loads ? _loads.size() : _capacities.size();
    for (size_t b = 0; b < num_bins; ++b) {
        auto bin_idx = Integer(static_cast<long long>(b));
        WPBSum sum;
        for (const auto & [i, item] : enumerate(_items))
            sum += _sizes[i] * (item == bin_idx);

        if (_have_loads)
            model.add_constraint(sum == 1_i * _loads[b]);
        else
            model.add_constraint(sum <= _capacities[b]);
    }
}

auto BinPacking::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _items.begin(), _items.end());
    if (_have_loads)
        triggers.on_bounds.insert(triggers.on_bounds.end(), _loads.begin(), _loads.end());

    if (! _bounds_only) {
        // Emit per-bin Stage 3 scaffolding once at search root: for every
        // statically reduced (b, i, w) node, create reified flags
        //   g_up_{b,i,w}  ⇔  sum_{j<i} sizes[j]·(items[j]==b) ≥ w
        //   g_dn_{b,i,w}  ⇔  sum_{j<i} sizes[j]·(items[j]==b) ≤ w
        //   S_{b,i,w}     ⇔  g_up ∧ g_dn   (partial sum exactly w)
        // at ProofLevel::Top. The S flag is the "main state" — the
        // conjunction-of-sub-states pattern from Demirović et al., CP 2024
        // §3 ("Knapsack as a Constraint"), specialised to one partial-sum
        // dimension. Both the initialiser and the propagator capture a
        // shared_ptr<DagBridge>; the initialiser writes the flag handles,
        // the propagator reads them inside its per-call proof callbacks.
        propagators.install_initialiser(
            [items = _items, sizes = _sizes, bridge = _bridge](
                State &, auto &, ProofLogger * const logger) -> void {
                if (! logger)
                    return;
                for (size_t b = 0; b < bridge->dags.size(); ++b)
                    emit_bin_scaffolding(logger, b, items, sizes,
                        bridge->dags[b], bridge->flags[b]);
            });
    }

    // Stage 2 always runs (as a fast bounds pass). When bounds_only is set,
    // this is the entire propagator; otherwise Stage 3's per-bin DAG sweep
    // follows and tightens to GAC. Stage 2's inferences are RUP-justified
    // against the natural per-bin OPB equations alone; Stage 3 RUPs against
    // the per-bin scaffolding emitted by the initialiser. The two passes
    // share state through `state` — Stage 3 sees the bounds Stage 2 derived.
    //
    // dev_docs/bin-packing.md walks the inference shapes and reasons.
    propagators.install(
        [items = _items, sizes = _sizes, loads = _loads, capacities = _capacities,
            have_loads = _have_loads, bounds_only = _bounds_only, bridge = _bridge](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            run_stage2(state, inference, logger, items, sizes, loads, capacities, have_loads);

            if (! bounds_only && bridge) {
                auto num_bins = have_loads ? loads.size() : capacities.size();
                auto reason = generic_reason(state, items);
                for (size_t b = 0; b < num_bins; ++b)
                    run_stage3_for_bin(state, inference, logger, items, sizes,
                        bridge->dags[b], bridge->flags[b], b, reason);
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto BinPacking::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} binpacking (", _name);
    for (const auto & item : _items)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(item));
    print(s, " ) ( ");
    for (const auto & sz : _sizes)
        print(s, " {}", sz);
    print(s, " ) ");
    if (_have_loads) {
        print(s, "loads (");
        for (const auto & l : _loads)
            print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(l));
        print(s, " )");
    }
    else {
        print(s, "capacities (");
        for (const auto & c : _capacities)
            print(s, " {}", c);
        print(s, " )");
    }

    return s.str();
}
