#include <gcs/constraints/knapsack/knapsack.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
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
#include <any>
#include <list>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <unordered_map>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::any_cast;
using std::list;
using std::make_shared;
using std::make_unique;
using std::map;
using std::move;
using std::next;
using std::optional;
using std::pair;
using std::set;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::unordered_map;
using std::vector;
using std::ranges::minmax_element;
using std::ranges::none_of;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

namespace
{
    // Forward-reach DAG built once from initial domains. For k totals,
    // each node at layer i is a k-vector of partial sums. Layer 0 holds
    // exactly the zero vector; layer i+1 contains every state reachable
    // from some layer-i node by some value in initial dom(vars[i]) that
    // doesn't exceed the per-coord cap (initial upper(totals[x]) or sum
    // of max contributions, whichever is tighter). No backward filter:
    // every forward-reachable node gets a Top-level reified flag so the
    // per-call proof chain has a handle to reference.
    struct Dag
    {
        vector<vector<vector<Integer>>> nodes_at;
        vector<set<vector<Integer>>> node_set;
    };

    struct CoordFlags
    {
        ProofFlag g_up;
        ProofLine g_up_fwd;
        ProofLine g_up_rev;
        ProofFlag g_dn;
        ProofLine g_dn_fwd;
        ProofLine g_dn_rev;
    };

    struct Flags
    {
        // per_coord_flags[i][x] maps coord raw value -> {g_up, g_dn, fwd/rev lines}.
        vector<vector<unordered_map<long long, CoordFlags>>> per_coord_flags;
        // state_flags[i] maps full state vector -> S flag.
        vector<map<vector<Integer>, ProofFlag>> state_flags;
    };

    // Per-coordinate cap on partial sums: sum of max item contributions.
    // We deliberately do not intersect with initial upper(totals[x]) here:
    // the static DAG must contain every partial-sum vector that any
    // assignment of items in their initial domains can produce, even ones
    // that already violate the initial totals bound. The per-call
    // propagator's "eliminated by current bound" case needs a Top-level
    // flag for the over-bound successor to emit its pol step against;
    // dropping the bound filter here guarantees that flag exists.
    auto compute_caps(const State & initial_state,
        const vector<vector<Integer>> & coeffs,
        const vector<IntegerVariableID> & vars,
        const vector<IntegerVariableID> & totals) -> vector<Integer>
    {
        vector<Integer> caps;
        caps.reserve(totals.size());
        for (const auto & [x, t] : enumerate(totals)) {
            Integer sum_x = 0_i;
            for (const auto & [i, v] : enumerate(vars))
                sum_x += initial_state.upper_bound(v) * coeffs[x][i];
            caps.push_back(sum_x);
            (void) t;
        }
        return caps;
    }

    auto step(const vector<Integer> & w, Integer v, size_t i,
        const vector<vector<Integer>> & coeffs, const vector<Integer> & caps,
        vector<Integer> & out) -> bool
    {
        for (size_t x = 0; x < w.size(); ++x) {
            out[x] = w[x] + v * coeffs[x][i];
            if (out[x] > caps[x])
                return false;
        }
        return true;
    }

    auto build_static_dag(const State & initial_state,
        const vector<IntegerVariableID> & vars,
        const vector<vector<Integer>> & coeffs,
        const vector<IntegerVariableID> & totals,
        const vector<Integer> & caps) -> Dag
    {
        auto n = vars.size();
        auto k = totals.size();

        vector<set<vector<Integer>>> fwd(n + 1);
        fwd[0].insert(vector<Integer>(k, 0_i));
        vector<Integer> next_w(k, 0_i);
        for (size_t i = 0; i < n; ++i) {
            for (const auto & w : fwd[i]) {
                for (auto v : initial_state.each_value_immutable(vars[i])) {
                    if (step(w, v, i, coeffs, caps, next_w))
                        fwd[i + 1].insert(next_w);
                }
            }
        }

        Dag dag;
        dag.nodes_at.assign(n + 1, {});
        dag.node_set.assign(n + 1, {});
        for (size_t i = 0; i <= n; ++i) {
            for (const auto & w : fwd[i])
                dag.nodes_at[i].push_back(w);
            std::ranges::sort(dag.nodes_at[i]);
            dag.node_set[i].insert(dag.nodes_at[i].begin(), dag.nodes_at[i].end());
        }
        return dag;
    }

    auto running_sum(const vector<IntegerVariableID> & vars,
        const vector<vector<Integer>> & coeffs, size_t x, size_t i) -> WPBSum
    {
        WPBSum s;
        for (size_t j = 0; j < i; ++j)
            s += coeffs[x][j] * vars[j];
        return s;
    }

    auto emit_scaffolding(ProofLogger * const logger,
        const State & initial_state,
        const vector<IntegerVariableID> & vars,
        const vector<vector<Integer>> & coeffs,
        size_t k,
        const Dag & dag, Flags & flags) -> void
    {
        auto n = vars.size();
        flags.per_coord_flags.assign(n + 1, vector<unordered_map<long long, CoordFlags>>(k));
        flags.state_flags.assign(n + 1, {});

        vector<vector<WPBSum>> running(n + 1, vector<WPBSum>(k));
        for (size_t i = 0; i <= n; ++i)
            for (size_t x = 0; x < k; ++x)
                running[i][x] = running_sum(vars, coeffs, x, i);

        // Reifications. Per-coord g_up_{i,x,w} ⇔ running_sum_at_i_x ≥ w
        // and g_dn ⇔ ≤. State conjunction S_{i,w} ⇔ all coord g_up and
        // g_dn at this w are true (i.e., running sum equals w exactly).
        for (size_t i = 0; i <= n; ++i) {
            for (const auto & w : dag.nodes_at[i]) {
                for (size_t x = 0; x < k; ++x) {
                    if (! flags.per_coord_flags[i][x].contains(w[x].raw_value)) {
                        auto [g_up, gu_fwd, gu_rev] = logger->create_proof_flag_reifying(
                            running[i][x] >= w[x],
                            format("kpup_{}_{}_{}", i, x, w[x].raw_value),
                            ProofLevel::Top);
                        auto [g_dn, gd_fwd, gd_rev] = logger->create_proof_flag_reifying(
                            running[i][x] <= w[x],
                            format("kpdn_{}_{}_{}", i, x, w[x].raw_value),
                            ProofLevel::Top);
                        flags.per_coord_flags[i][x].emplace(w[x].raw_value,
                            CoordFlags{g_up, gu_fwd, gu_rev, g_dn, gd_fwd, gd_rev});
                    }
                }

                WPBSum all;
                for (size_t x = 0; x < k; ++x) {
                    const auto & cf = flags.per_coord_flags[i][x].at(w[x].raw_value);
                    all += 1_i * cf.g_up;
                    all += 1_i * cf.g_dn;
                }
                auto [s_flag, s_fwd, s_rev] = logger->create_proof_flag_reifying(
                    all >= Integer(static_cast<long long>(2 * k)),
                    [&] {
                        stringstream nm;
                        nm << "kpat_" << i;
                        for (const auto & wi : w)
                            nm << '_' << wi.raw_value;
                        return nm.str();
                    }(),
                    ProofLevel::Top);
                flags.state_flags[i].emplace(w, s_flag);
                (void) s_fwd;
                (void) s_rev;
            }
        }

        // Phantom states: non-negative partial-sum vectors that arise as
        // backward edges from DAG[i+1] states under some initial-domain
        // val but aren't themselves forward-reachable (not in DAG[i]).
        // Without flags for these, backward chains from DAG[i+1] states
        // for the corresponding val have no handle for UP to use during
        // per-call dead-state derivations.
        //
        // For each phantom we:
        //   1. Create reified g_up / g_dn / S flags at Top, same shape
        //      as for DAG states.
        //   2. Emit ~S_phantom >= 1 as a Top-level RUP — closes by:
        //      assume S_phantom = 1, conjunction reification forces the
        //      partial sum at layer i to exactly equal the phantom's
        //      coord values, and VeriPB's UP slack-propagation through
        //      the bit encoding of the natural OPB equation finds the
        //      integer infeasibility (no assignment of vars[0..i-1] in
        //      their initial domains hits this sum).
        // Phantoms are computed in descending layer order so that
        // phantoms[i] also contains the backward edges from phantoms[i+1]
        // (not just from DAG[i+1]). The phantom-rule derivation below
        // walks the same backward edges and requires every parent of a
        // phantom to already have a flag (DAG or phantom) at its layer.
        vector<set<vector<Integer>>> phantoms(n + 1);
        {
            vector<Integer> p_w(k, 0_i);
            auto backward_into = [&](size_t i, const auto & succ_set) {
                for (const auto & s : succ_set) {
                    for (auto val : initial_state.each_value_immutable(vars[i])) {
                        bool valid = true;
                        for (size_t x = 0; x < k; ++x) {
                            p_w[x] = s[x] - val * coeffs[x][i];
                            if (p_w[x] < 0_i) {
                                valid = false;
                                break;
                            }
                        }
                        if (! valid)
                            continue;
                        if (dag.node_set[i].contains(p_w))
                            continue;
                        phantoms[i].insert(p_w);
                    }
                }
            };
            for (size_t i = n; i-- > 0;) {
                backward_into(i, dag.nodes_at[i + 1]);
                backward_into(i, phantoms[i + 1]);
            }
        }

        // Phantom flags only — the ~S_phantom RUPs are emitted after the
        // joint layer ALOs (below), since UP relies on them to close.
        for (size_t i = 0; i <= n; ++i) {
            for (const auto & p : phantoms[i]) {
                for (size_t x = 0; x < k; ++x) {
                    if (! flags.per_coord_flags[i][x].contains(p[x].raw_value)) {
                        auto [g_up, gu_fwd, gu_rev] = logger->create_proof_flag_reifying(
                            running[i][x] >= p[x],
                            format("kpup_{}_{}_{}", i, x, p[x].raw_value),
                            ProofLevel::Top);
                        auto [g_dn, gd_fwd, gd_rev] = logger->create_proof_flag_reifying(
                            running[i][x] <= p[x],
                            format("kpdn_{}_{}_{}", i, x, p[x].raw_value),
                            ProofLevel::Top);
                        flags.per_coord_flags[i][x].emplace(p[x].raw_value,
                            CoordFlags{g_up, gu_fwd, gu_rev, g_dn, gd_fwd, gd_rev});
                    }
                }

                WPBSum all;
                for (size_t x = 0; x < k; ++x) {
                    const auto & cf = flags.per_coord_flags[i][x].at(p[x].raw_value);
                    all += 1_i * cf.g_up;
                    all += 1_i * cf.g_dn;
                }
                auto [s_flag, s_fwd, s_rev] = logger->create_proof_flag_reifying(
                    all >= Integer(static_cast<long long>(2 * k)),
                    [&] {
                        stringstream nm;
                        nm << "kphantom_" << i;
                        for (const auto & pi : p)
                            nm << '_' << pi.raw_value;
                        return nm.str();
                    }(),
                    ProofLevel::Top);
                flags.state_flags[i].emplace(p, s_flag);
                (void) s_fwd;
                (void) s_rev;
            }
        }

        // Per-coord forward chains. For every (parent in DAG[i], val in
        // initial_dom(vars[i]), succ in DAG[i+1]) edge and each coord x:
        //   pol succ.g_up.rev + parent.g_up.fwd ; saturate
        //   rup ~parent.g_up_x + (vars[i] != val) + succ.g_up_x >= 1
        // and same for g_dn.
        //
        // Per-state forward chain RUPs follow trivially from the per-coord
        // chains via the conjunction reification.
        vector<Integer> next_w(k, 0_i);
        for (size_t i = 0; i < n; ++i) {
            for (const auto & parent_w : dag.nodes_at[i]) {
                const auto & parent_s = flags.state_flags[i].at(parent_w);
                for (auto val : initial_state.each_value_immutable(vars[i])) {
                    for (size_t x = 0; x < k; ++x)
                        next_w[x] = parent_w[x] + val * coeffs[x][i];
                    if (! dag.node_set[i + 1].contains(next_w))
                        continue;
                    auto not_choice = vars[i] != val;
                    const auto & succ_s = flags.state_flags[i + 1].at(next_w);

                    for (size_t x = 0; x < k; ++x) {
                        const auto & parent_cf = flags.per_coord_flags[i][x].at(parent_w[x].raw_value);
                        const auto & succ_cf = flags.per_coord_flags[i + 1][x].at(next_w[x].raw_value);

                        PolBuilder{}.add(succ_cf.g_up_rev).add(parent_cf.g_up_fwd).saturate().emit(*logger, ProofLevel::Top);
                        logger->emit_rup_proof_line(
                            WPBSum{} + 1_i * ! parent_cf.g_up + 1_i * not_choice + 1_i * succ_cf.g_up >= 1_i,
                            ProofLevel::Top);

                        PolBuilder{}.add(succ_cf.g_dn_rev).add(parent_cf.g_dn_fwd).saturate().emit(*logger, ProofLevel::Top);
                        logger->emit_rup_proof_line(
                            WPBSum{} + 1_i * ! parent_cf.g_dn + 1_i * not_choice + 1_i * succ_cf.g_dn >= 1_i,
                            ProofLevel::Top);
                    }

                    // Per-state forward chain RUP-closes from the per-coord
                    // chains plus the conjunction reification of succ.S.
                    logger->emit_rup_proof_line(
                        WPBSum{} + 1_i * ! parent_s + 1_i * not_choice + 1_i * succ_s >= 1_i,
                        ProofLevel::Top);
                }
            }
        }

        // Layer-0 ALO: S_{0, 0..0} >= 1. RUP-closes from the reverse
        // reification axioms (running sum at layer 0 is the empty sum =
        // 0, so g_up_{0,x,0} = 1 always; conjunction gives S_0 = 1).
        if (! dag.nodes_at[0].empty()) {
            const auto & root_s = flags.state_flags[0].at(dag.nodes_at[0].front());
            logger->emit_rup_proof_line(WPBSum{} + 1_i * root_s >= 1_i, ProofLevel::Top);
        }

        // Induction: for each layer k from 0 to n-1, emit per-state
        // implications and layer-(k+1) ALO, all as RUPs.
        //
        //   For each state s in DAG[k]:
        //     RUP ~S_{k,s} + Σ_v S_{k+1, s + v·coeffs} >= 1   (per-state implication)
        //   (closes from the D forward chains for (s, v) and the
        //    var-domain axiom for vars[k]: assume goal negation, each
        //    chain forces (vars[k] != v), then var-domain → contradiction)
        //
        //   RUP Σ_{w in DAG[k+1]} S_{k+1, w} >= 1   (layer-(k+1) ALO)
        //   (closes from the per-state implications and the layer-k ALO:
        //    each implication forces ~S_{k,s}; layer-k ALO contradicts)
        for (size_t i = 0; i < n; ++i) {
            for (const auto & parent_w : dag.nodes_at[i]) {
                const auto & parent_s = flags.state_flags[i].at(parent_w);
                WPBSum impl = WPBSum{} + 1_i * ! parent_s;
                for (auto val : initial_state.each_value_immutable(vars[i])) {
                    for (size_t x = 0; x < k; ++x)
                        next_w[x] = parent_w[x] + val * coeffs[x][i];
                    if (! dag.node_set[i + 1].contains(next_w))
                        continue;
                    impl += 1_i * flags.state_flags[i + 1].at(next_w);
                }
                logger->emit_rup_proof_line(move(impl) >= 1_i, ProofLevel::Top);
            }

            WPBSum alo;
            for (const auto & w : dag.nodes_at[i + 1])
                alo += 1_i * flags.state_flags[i + 1].at(w);
            logger->emit_rup_proof_line(move(alo) >= 1_i, ProofLevel::Top);
        }

        // Per-coord feasible projections, used below for phantom rules.
        vector<vector<set<Integer>>> per_coord_feasible(n + 1, vector<set<Integer>>(k));
        for (size_t i = 0; i <= n; ++i)
            for (const auto & w : dag.nodes_at[i])
                for (size_t x = 0; x < k; ++x)
                    per_coord_feasible[i][x].insert(w[x]);

        // Backward chains. For each (succ at layer i+1, val in
        // initial_dom(vars[i])), where succ is either in DAG[i+1] or in
        // phantoms[i+1]:
        //
        //   * parent_w = succ - val·coeffs[i] all coords ≥ 0 AND in
        //     DAG[i] OR phantom set: emit
        //       pol succ.g_up.fwd + parent.g_up.rev ; saturate
        //       rup ~succ.g_up_x + (vars[i] != val) + parent.g_up_x >= 1
        //     (and the g_dn twin and the per-state chain).
        //
        //   * parent_w has a negative coord (the val takes us below zero):
        //     emit ~succ.S + (vars[i] != val) >= 1 directly. RUP-closes
        //     from succ.S forcing running_sum_at_(i+1) = succ_w, then
        //     vars[i] = val would force running_sum_at_i < 0, which UP
        //     contradicts against the non-negativity of the partial sum.
        //
        // Including phantoms-as-succ is what lets the joint-only-phantom
        // rule below close: that rule's RUP needs a backward chain from
        // the phantom into layer i-1 where some prior phantom rule has
        // discharged the parent.
        auto emit_backward_chain = [&](size_t i, const vector<Integer> & succ_w) {
            vector<Integer> parent_w_for_val(k, 0_i);
            const auto & succ_s = flags.state_flags[i + 1].at(succ_w);
            for (auto val : initial_state.each_value_immutable(vars[i])) {
                bool valid_coords = true;
                for (size_t x = 0; x < k; ++x) {
                    parent_w_for_val[x] = succ_w[x] - val * coeffs[x][i];
                    if (parent_w_for_val[x] < 0_i) {
                        valid_coords = false;
                        break;
                    }
                }

                auto not_choice = vars[i] != val;

                if (! valid_coords) {
                    logger->emit_rup_proof_line(
                        WPBSum{} + 1_i * ! succ_s + 1_i * not_choice >= 1_i,
                        ProofLevel::Top);
                    continue;
                }

                const auto & parent_s = flags.state_flags[i].at(parent_w_for_val);

                for (size_t x = 0; x < k; ++x) {
                    const auto & parent_cf = flags.per_coord_flags[i][x].at(parent_w_for_val[x].raw_value);
                    const auto & succ_cf = flags.per_coord_flags[i + 1][x].at(succ_w[x].raw_value);

                    PolBuilder{}.add(succ_cf.g_up_fwd).add(parent_cf.g_up_rev).saturate().emit(*logger, ProofLevel::Top);
                    logger->emit_rup_proof_line(
                        WPBSum{} + 1_i * ! succ_cf.g_up + 1_i * not_choice + 1_i * parent_cf.g_up >= 1_i,
                        ProofLevel::Top);

                    PolBuilder{}.add(succ_cf.g_dn_fwd).add(parent_cf.g_dn_rev).saturate().emit(*logger, ProofLevel::Top);
                    logger->emit_rup_proof_line(
                        WPBSum{} + 1_i * ! succ_cf.g_dn + 1_i * not_choice + 1_i * parent_cf.g_dn >= 1_i,
                        ProofLevel::Top);
                }

                logger->emit_rup_proof_line(
                    WPBSum{} + 1_i * ! succ_s + 1_i * not_choice + 1_i * parent_s >= 1_i,
                    ProofLevel::Top);
            }
        };

        for (size_t i = 0; i < n; ++i) {
            for (const auto & succ_w : dag.nodes_at[i + 1])
                emit_backward_chain(i, succ_w);
            for (const auto & succ_w : phantoms[i + 1])
                emit_backward_chain(i, succ_w);
        }

        // Phantom rules in ascending layer order. Two cases by category:
        //
        //   Per-coord-phantom (some coord x* of p has p[x*] outside the
        //   DAG projection): emit pol steps combining g_up{u}.fwd with
        //   g_dn{p[x*]}.fwd (or the swapped variant for u < p[x*]) for
        //   every u ∈ per_coord_feasible[i][x*]. These pair-wise lines
        //   plus the joint layer-i ALO close the ~S_phantom RUP via
        //   conjunction-rev of every DAG joint state with s[x*] = u.
        //
        //   Joint-only-phantom (every coord projection feasible, joint
        //   isn't): no extra pol needed. The backward chains above plus
        //   the recursively-derived ~S_phantom of any non-DAG parent
        //   (which is guaranteed at all backward parents since DAG is
        //   forward-closed) plus the var-domain ALO let UP close the
        //   ~S_phantom RUP directly. Layer-0 phantoms always fall into
        //   the per-coord-phantom branch because per_coord_feasible[0][x]
        //   is {0}, so layer 0 closes without recursion.
        for (size_t i = 0; i <= n; ++i) {
            for (const auto & p : phantoms[i]) {
                optional<size_t> phantom_coord;
                for (size_t x = 0; x < k; ++x) {
                    if (! per_coord_feasible[i][x].contains(p[x])) {
                        phantom_coord = x;
                        break;
                    }
                }

                if (phantom_coord) {
                    auto x_star = *phantom_coord;
                    auto w_phantom = p[x_star];
                    const auto & phantom_cf = flags.per_coord_flags[i][x_star].at(w_phantom.raw_value);

                    for (auto u : per_coord_feasible[i][x_star]) {
                        const auto & u_cf = flags.per_coord_flags[i][x_star].at(u.raw_value);

                        if (u > w_phantom) {
                            PolBuilder{}
                                .add(u_cf.g_up_fwd)
                                .add(phantom_cf.g_dn_fwd)
                                .saturate()
                                .emit(*logger, ProofLevel::Top);
                        }
                        else if (u < w_phantom) {
                            PolBuilder{}
                                .add(phantom_cf.g_up_fwd)
                                .add(u_cf.g_dn_fwd)
                                .saturate()
                                .emit(*logger, ProofLevel::Top);
                        }
                    }
                }

                const auto & s_flag = flags.state_flags[i].at(p);
                logger->emit_rup_proof_line(
                    WPBSum{} + 1_i * ! s_flag >= 1_i, ProofLevel::Top);
            }
        }
    }

    auto add_bound_p_term(PolBuilder & b, const State & state, ProofLogger * logger,
        IntegerVariableID v, bool upper) -> void
    {
        overloaded{
            [&](const SimpleIntegerVariableID & sv) {
                b.add_for_literal(logger->names_and_ids_tracker(),
                    upper ? sv <= state.upper_bound(sv) : sv >= state.lower_bound(sv));
            },
            [&](const ConstantIntegerVariableID &) { throw UnimplementedException{}; },
            [&](const ViewOfIntegerVariableID &) { throw UnimplementedException{}; }}
            .visit(v);
    }

    // Information tracked per "currently reachable" state during the
    // per-call forward proof walk. The flags reference Top-level handles;
    // predecessors records which (parent state, val) edges arrived here,
    // for the later backward pass.
    struct LiveNode
    {
        // Predecessor (parent_sums, val) pairs that landed in this state.
        vector<pair<vector<Integer>, Integer>> predecessors;
    };

    // Backtrack-restored "we have already emitted ~S_{i,w} / ~g_dn at or
    // shallower than the current search depth" cache. Promoting those
    // pure dead-state lines to ProofLevel::Current and skipping their
    // re-emission collapses what would otherwise be hundreds of repeats
    // per state across the proof.
    struct DeadCache
    {
        // dead_states[i] = layer-i state vectors already emitted as dead.
        vector<set<vector<Integer>>> dead_states;
        // dead_g_dn[i][x] = (layer, coord) values whose g_dn flag is known
        // to be false (only populated for layer n at the lower-bound filter).
        vector<vector<set<long long>>> dead_g_dn;
    };

    // Per-call full GAC propagation, with proof emission when logger != null.
    // Structurally a port of KnapsackLegacy::knapsack_gac<true>: walks the
    // static DAG layer by layer under current item domains, emitting
    // per-(parent, val, succ) implication chains, per-parent "must-pick"
    // selectors, per-layer at-least-one constraints, then filters layer-n
    // by current totals domain, then a backward pass that emits ~S for
    // dead states and surfaces unsupported item values. All scaffolding
    // is at ProofLevel::Temporary; flag handles come from the Top-level
    // bridge populated by emit_scaffolding.
    auto propagate(const State & state, auto & inference, ProofLogger * const logger,
        const vector<IntegerVariableID> & vars,
        const vector<vector<Integer>> & coeffs,
        const vector<IntegerVariableID> & totals,
        const Dag & dag, const Flags & flags,
        const vector<pair<ProofLine, ProofLine>> & opb_lines,
        DeadCache & cache) -> void
    {
        auto n = vars.size();
        auto k = totals.size();

        vector<IntegerVariableID> reason_vars;
        reason_vars.reserve(vars.size() + totals.size());
        reason_vars.insert(reason_vars.end(), vars.begin(), vars.end());
        reason_vars.insert(reason_vars.end(), totals.begin(), totals.end());
        auto reason = generic_reason(state, reason_vars);

        int temporary_proof_level = 0;
        if (logger)
            temporary_proof_level = logger->temporary_proof_level();

        // Per-layer map of currently-reachable states. completed_layers[0]
        // holds the zero vector; completed_layers[i+1] is populated as we
        // forward-walk layer i. Membership predicates against dag.node_set
        // ensure we never address a state whose Top-level flag doesn't exist.
        list<map<vector<Integer>, LiveNode>> completed_layers;
        completed_layers.emplace_back();
        completed_layers.back().emplace(vector<Integer>(k, 0_i), LiveNode{});

        vector<Integer> next_w(k, 0_i);

        for (size_t i = 0; i < n; ++i) {
            map<vector<Integer>, LiveNode> growing;
            set<Integer> supported_values;

            for (const auto & [parent_w, parent_node] : completed_layers.back()) {
                for (auto val : state.each_value_mutable(vars[i])) {
                    for (size_t x = 0; x < k; ++x)
                        next_w[x] = parent_w[x] + val * coeffs[x][i];

                    if (! dag.node_set[i + 1].contains(next_w))
                        continue;

                    auto succ_iter = growing.find(next_w);
                    if (succ_iter == growing.end())
                        succ_iter = growing.emplace(next_w, LiveNode{}).first;
                    succ_iter->second.predecessors.emplace_back(parent_w, val);

                    // Cap-exceeded: succ exceeds the CURRENT upper bound
                    // of totals[x]. The Top-level forward chain plus the
                    // pol step below let VeriPB UP derive ~succ.g_up and
                    // hence ~succ.S, which is what we'll eventually need.
                    // (Marking the state as cap-exceeded for later
                    // dead-state emission happens implicitly via the
                    // growing-set filter below.)
                    bool eliminated = false;
                    for (size_t x = 0; x < k; ++x) {
                        if (next_w[x] > state.upper_bound(totals[x])) {
                            eliminated = true;
                            break;
                        }
                    }

                    if (! eliminated)
                        supported_values.emplace(val);
                }
            }

            // Eliminate cap-exceeding states from the layer we just grew.
            erase_if(growing, [&](const auto & item) {
                for (size_t x = 0; x < k; ++x)
                    if (item.first[x] > state.upper_bound(totals[x]))
                        return true;
                return false;
            });

            // For every state in DAG[i+1] that the current call has
            // ruled out (not in `growing`), emit ~S at ProofLevel::Current
            // with cache gating. Two flavours:
            //   * cap-exceeded — pol against the natural OPB equation +
            //     current upper-bound term derives ~g_up directly, then
            //     ~S follows by conjunction reification.
            //   * forward-unreachable — RUP closes from Top-level backward
            //     chains plus cached ~parent.S facts for the dead
            //     predecessors and the var-domain axiom; no extra pol
            //     scaffolding needed in proof terms.
            if (logger) {
                for (const auto & w : dag.nodes_at[i + 1]) {
                    if (growing.contains(w))
                        continue;
                    if (cache.dead_states[i + 1].contains(w))
                        continue;

                    optional<size_t> cap_coord;
                    for (size_t x = 0; x < k; ++x)
                        if (w[x] > state.upper_bound(totals[x])) {
                            cap_coord = x;
                            break;
                        }

                    if (cap_coord) {
                        auto x = *cap_coord;
                        const auto & cf = flags.per_coord_flags[i + 1][x].at(w[x].raw_value);
                        PolBuilder b;
                        b.add(cf.g_up_fwd).add(opb_lines[x].first);
                        add_bound_p_term(b, state, logger, totals[x], true);
                        b.emit(*logger, ProofLevel::Temporary);
                    }

                    ProofFlag s_flag = flags.state_flags[i + 1].at(w);
                    logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * ! s_flag >= 1_i, ProofLevel::Current);
                    cache.dead_states[i + 1].insert(w);
                }
            }

            // Item values that never produced a feasible new state: prune.
            // The Top-level layer ALO + Top-level chains + cached ~S for
            // dead states give VeriPB UP enough to close the RUP.
            for (auto val : state.each_value_mutable(vars[i])) {
                if (! supported_values.contains(val))
                    inference.infer(logger, vars[i] != val, JustifyUsingRUP{}, reason);
            }

            completed_layers.emplace_back(move(growing));
        }

        // Filter layer-n by current totals lower bounds. ~g_dn / ~S lines
        // are pure dead-state facts that hold for the whole subtree below
        // the current search node — emit each at most once across the
        // subtree by promoting to ProofLevel::Current and gating on the
        // backtrack-restored DeadCache.
        for (auto it = completed_layers.back().begin(), end = completed_layers.back().end(); it != end;) {
            bool eliminated = false;
            for (size_t x = 0; x < k; ++x) {
                if (it->first[x] < state.lower_bound(totals[x])) {
                    if (logger) {
                        bool need_s = ! cache.dead_states[n].contains(it->first);
                        bool need_g_dn = ! cache.dead_g_dn[n][x].contains(it->first[x].raw_value);
                        if (need_s || need_g_dn) {
                            const auto & cf = flags.per_coord_flags[n][x].at(it->first[x].raw_value);
                            PolBuilder b;
                            b.add(cf.g_dn_fwd).add(opb_lines[x].second);
                            add_bound_p_term(b, state, logger, totals[x], false);
                            b.emit(*logger, ProofLevel::Temporary);
                            if (need_g_dn) {
                                logger->emit_rup_proof_line_under_reason(reason,
                                    WPBSum{} + 1_i * ! cf.g_dn >= 1_i, ProofLevel::Current);
                                cache.dead_g_dn[n][x].insert(it->first[x].raw_value);
                            }
                            if (need_s) {
                                ProofFlag s_flag = flags.state_flags[n].at(it->first);
                                logger->emit_rup_proof_line_under_reason(reason,
                                    WPBSum{} + 1_i * ! s_flag >= 1_i, ProofLevel::Current);
                                cache.dead_states[n].insert(it->first);
                            }
                        }
                    }
                    completed_layers.back().erase(it++);
                    eliminated = true;
                    break;
                }
            }
            if (! eliminated)
                ++it;
        }

        // Filter layer-n by interior totals-domain holes. Same caching
        // logic — the pol-pol-RUP chain that derives ~S only needs to
        // run when the state isn't already proven dead in this subtree.
        for (auto it = completed_layers.back().begin(), end = completed_layers.back().end(); it != end;) {
            bool eliminated = false;
            for (size_t x = 0; x < k; ++x) {
                if (! state.in_domain(totals[x], it->first[x])) {
                    if (logger && ! cache.dead_states[n].contains(it->first)) {
                        ProofFlag s_flag = flags.state_flags[n].at(it->first);
                        const auto & cf = flags.per_coord_flags[n][x].at(it->first[x].raw_value);
                        PolBuilder{}.add(cf.g_dn_fwd).add(opb_lines[x].second).emit(*logger, ProofLevel::Temporary);
                        PolBuilder{}.add(cf.g_up_fwd).add(opb_lines[x].first).emit(*logger, ProofLevel::Temporary);
                        logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * ! s_flag + 1_i * (totals[x] == it->first[x]) >= 1_i,
                            ProofLevel::Temporary);
                        logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * ! s_flag >= 1_i, ProofLevel::Current);
                        cache.dead_states[n].insert(it->first);
                    }
                    completed_layers.back().erase(it++);
                    eliminated = true;
                    break;
                }
            }
            if (! eliminated)
                ++it;
        }

        if (completed_layers.back().empty()) {
            if (logger)
                logger->emit_rup_proof_line_under_reason(reason, WPBSum{} >= 1_i, ProofLevel::Temporary);
            inference.contradiction(logger, JustifyUsingRUP{}, reason);
            if (logger)
                logger->forget_proof_level(temporary_proof_level);
            return;
        }

        vector<Literal> inferences;
        for (size_t x = 0; x < k; ++x) {
            auto x_capture = x;
            auto [lo_iter, hi_iter] = minmax_element(completed_layers.back(),
                [&](const pair<vector<Integer>, LiveNode> & a, const pair<vector<Integer>, LiveNode> & b) {
                    return a.first[x_capture] < b.first[x_capture];
                });

            auto lo = lo_iter->first[x];
            auto hi = hi_iter->first[x];
            inferences.emplace_back(totals[x] >= lo);
            inferences.emplace_back(totals[x] < hi + 1_i);

            for (auto v : state.each_value_immutable(totals[x])) {
                if (v > lo && v < hi + 1_i && none_of(completed_layers.back(), [&](const pair<vector<Integer>, LiveNode> & a) {
                        return a.first[x] == v;
                    }))
                    inferences.emplace_back(totals[x] != v);
            }

            if (logger) {
                for (const auto & [w, _] : completed_layers.back()) {
                    const auto & cf = flags.per_coord_flags[n][x].at(w[x].raw_value);
                    PolBuilder{}.add(opb_lines[x].first).add(cf.g_up_fwd).emit(*logger, ProofLevel::Temporary);
                    logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * ! cf.g_up + 1_i * (totals[x] >= lo) >= 1_i,
                        ProofLevel::Temporary);

                    PolBuilder{}.add(opb_lines[x].second).add(cf.g_dn_fwd).emit(*logger, ProofLevel::Temporary);
                    logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * ! cf.g_dn + 1_i * (totals[x] <= hi) >= 1_i,
                        ProofLevel::Temporary);
                }
                logger->emit_rup_proof_line_under_reason(reason,
                    WPBSum{} + 1_i * (totals[x] >= lo) >= 1_i, ProofLevel::Temporary);
                logger->emit_rup_proof_line_under_reason(reason,
                    WPBSum{} + 1_i * (totals[x] <= hi) >= 1_i, ProofLevel::Temporary);
            }
        }

        inference.infer_all(logger, inferences, JustifyUsingRUP{}, reason);

        // Backward pass: identify states/values supported by a path to
        // the surviving layer-n set; emit ~S for dead intermediate states;
        // infer ~val for unsupported item values per layer.
        int var_number = static_cast<int>(n) - 1;
        for (auto layer = completed_layers.rbegin();
             layer != completed_layers.rend() && next(layer) != completed_layers.rend();
             ++layer, --var_number) {
            set<vector<Integer>> reached;
            set<Integer> supported;
            for (const auto & [_, node] : *layer) {
                for (const auto & [parent_w, val] : node.predecessors) {
                    reached.insert(parent_w);
                    supported.insert(val);
                }
            }

            for (auto it = next(layer)->begin(), end = next(layer)->end(); it != end;) {
                if (reached.contains(it->first))
                    ++it;
                else {
                    if (logger && ! cache.dead_states[var_number].contains(it->first)) {
                        ProofFlag s_flag = flags.state_flags[var_number].at(it->first);
                        logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * ! s_flag >= 1_i, ProofLevel::Current);
                        cache.dead_states[var_number].insert(it->first);
                    }
                    next(layer)->erase(it++);
                }
            }

            for (auto val : state.each_value_mutable(vars[var_number])) {
                if (! supported.contains(val))
                    inference.infer(logger, vars[var_number] != val, JustifyUsingRUP{}, reason);
            }
        }

        if (logger)
            logger->forget_proof_level(temporary_proof_level);
    }
}

struct Knapsack::DagBridge
{
    Dag dag;
    Flags flags;
    vector<pair<ProofLine, ProofLine>> opb_lines;
};

Knapsack::Knapsack(vector<Integer> weights, vector<Integer> profits,
    vector<IntegerVariableID> vars, IntegerVariableID weight, IntegerVariableID profit) :
    _coeffs({move(weights), move(profits)}),
    _vars(move(vars)),
    _totals({weight, profit})
{
}

Knapsack::Knapsack(vector<vector<Integer>> coefficients,
    vector<IntegerVariableID> vars,
    vector<IntegerVariableID> totals) :
    _coeffs(move(coefficients)),
    _vars(move(vars)),
    _totals(move(totals))
{
}

auto Knapsack::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Knapsack>(_coeffs, _vars, _totals);
}

auto Knapsack::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Knapsack::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    if (_coeffs.size() != _totals.size())
        throw InvalidProblemDefinitionException{"Knapsack: coefficients and totals must have the same number of equations"};
    if (_coeffs.empty())
        throw InvalidProblemDefinitionException{"Knapsack: at least one equation is required"};

    auto n_vars = _coeffs.front().size();
    for (const auto & c : _coeffs)
        if (c.size() != n_vars)
            throw InvalidProblemDefinitionException{"Knapsack: every coefficient row must have the same length"};
    if (n_vars != _vars.size())
        throw InvalidProblemDefinitionException{"Knapsack: coefficient row length must match number of variables"};

    for (const auto & cc : _coeffs)
        for (const auto & c : cc)
            if (c < 0_i)
                throw InvalidProblemDefinitionException{"Knapsack: coefficients must be non-negative"};

    for (const auto & v : _vars)
        if (initial_state.lower_bound(v) < 0_i)
            throw InvalidProblemDefinitionException{"Knapsack: item variables must be non-negative"};

    for (const auto & t : _totals)
        if (initial_state.lower_bound(t) < 0_i)
            throw InvalidProblemDefinitionException{"Knapsack: total variables must be non-negative"};

    auto caps = compute_caps(initial_state, _coeffs, _vars, _totals);
    _bridge = make_shared<DagBridge>();
    _bridge->dag = build_static_dag(initial_state, _vars, _coeffs, _totals, caps);

    // Backtrack-restored cache of pure dead-state proof lines we've
    // already emitted at or above the current search depth, so the
    // per-call propagator can skip the entire pol+RUP scaffolding for
    // a state that's already been proven dead in this subtree.
    DeadCache initial_cache{
        vector<set<vector<Integer>>>(_vars.size() + 1),
        vector<vector<set<long long>>>(_vars.size() + 1, vector<set<long long>>(_totals.size()))};
    _dead_cache_handle = initial_state.add_constraint_state(move(initial_cache));

    return true;
}

auto Knapsack::define_proof_model(ProofModel & model) -> void
{
    for (const auto & [cc_idx, cc] : enumerate(_coeffs)) {
        WPBSum sum_eq;
        for (const auto & [idx, v] : enumerate(_vars))
            sum_eq += cc.at(idx) * v;
        auto [eq1, eq2] = model.add_constraint(move(sum_eq) == 1_i * _totals.at(cc_idx));
        _bridge->opb_lines.emplace_back(eq1.value(), eq2.value());
    }
}

auto Knapsack::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};
    triggers.on_change.insert(triggers.on_change.end(), _totals.begin(), _totals.end());

    // Emit per-(i, w) Top-level scaffolding once at search root: for
    // every forward-reachable node in the static DAG, create reified flags
    //   g_up_{i,x,w_x}  ⇔  Σ_{j<i} coeffs[x][j]·vars[j] ≥ w_x
    //   g_dn_{i,x,w_x}  ⇔  Σ_{j<i} coeffs[x][j]·vars[j] ≤ w_x
    //   S_{i,w}         ⇔  Σ_x (g_up_{i,x,w_x} + g_dn_{i,x,w_x}) ≥ 2k
    // The conjunction-of-sub-states pattern is from Demirović et al.,
    // CP 2024 §3.3 ("Knapsack as a Constraint"), generalised to k
    // partial-sum dimensions. The initialiser writes flag handles; the
    // propagator reads them inside the per-call proof chain emitted at
    // ProofLevel::Temporary.
    propagators.install_initialiser(
        [vars = _vars, coeffs = _coeffs, k = _totals.size(), bridge = _bridge](
            State & state, auto &, ProofLogger * const logger) -> void {
            if (! logger)
                return;
            emit_scaffolding(logger, state, vars, coeffs, k, bridge->dag, bridge->flags);
        });

    propagators.install(
        [vars = _vars, coeffs = _coeffs, totals = _totals, bridge = _bridge,
            dead_cache_handle = *_dead_cache_handle](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            auto & cache = any_cast<DeadCache &>(state.get_constraint_state(dead_cache_handle));
            propagate(state, inference, logger, vars, coeffs, totals,
                bridge->dag, bridge->flags, bridge->opb_lines, cache);
            return PropagatorState::Enable;
        },
        triggers);
}

auto Knapsack::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} knapsack\n            (", _name);
    for (const auto & cs : _coeffs) {
        print(s, "\n                (");
        for (const auto & c : cs)
            print(s, " {}", c);
        print(s, ")");
    }
    print(s, "\n            )\n            (");
    for (const auto & v : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, ")\n            (");
    for (const auto & t : _totals)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(t));
    print(s, ")\n        ");

    return s.str();
}
