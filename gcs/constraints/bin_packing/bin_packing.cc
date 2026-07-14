#include <gcs/constraints/bin_packing/bin_packing.hh>
#include <gcs/constraints/bin_packing/hints.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>
#include <gcs/proof.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/core.h>
#endif

#include <algorithm>
#include <any>
#include <cstdint>
#include <list>
#include <map>
#include <optional>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::any_cast;
using std::holds_alternative;
using std::list;
using std::make_shared;
using std::make_unique;
using std::map;
using std::move;
using std::next;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::unique_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;
using std::ranges::minmax_element;
using std::ranges::none_of;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
#else
using fmt::format;
#endif

namespace
{
    // Forward-only DAG per bin, plus a transitively-computed phantom set for
    // the proof scaffolding. Both nodes_at and phantoms_at are sorted and
    // deduplicated; node_set / phantom_set are O(1) membership indexes.
    //
    // The DAG is the k=1 specialisation of Knapsack's static DAG: layer i
    // holds the surviving partial-load values w reachable from (0,0) under
    // initial item domains within the per-bin cap. We do NOT intersect with
    // backward reachability — that information becomes the "statically dead"
    // ~S lines emitted at Top, mirroring Knapsack's design (see
    // dev_docs/knapsack.md "Static reduction").
    struct PerBinDag
    {
        vector<vector<long long>> nodes_at;
        vector<unordered_set<long long>> node_set;
        vector<vector<long long>> phantoms_at;
        vector<unordered_set<long long>> phantom_set;

        // Precomputed static DAG edges for the per-call sweep, indexed by
        // layer i in [0, n) and node position p within nodes_at[i]. The value
        // is the position of the branch's successor within nodes_at[i+1], or
        // -1 if that successor is not a DAG node. These are structural (the
        // DAG never changes across the search); the per-wake sweep gates them
        // by the current item domains. Computed once, so the hot path needs no
        // hash lookups at all.
        //   exclude_succ[i][p]: items[i] != b  (partial load unchanged)
        //   include_succ[i][p]: items[i] == b  (partial load += sizes[i])
        vector<vector<int>> exclude_succ;
        vector<vector<int>> include_succ;
    };

    // Per-bin scratch for the per-call sweep (run_stage3_for_bin), owned by the
    // DagBridge and reused across every wake so the hot path allocates nothing
    // after warm-up. fwd/bwd are position-indexed reachability bitmaps parallel
    // to PerBinDag::nodes_at; can_be_b/can_be_notb hold the current per-item
    // admissibility. Each search gets its own constraint clone (and hence its
    // own bridge), so no synchronisation is needed even across threads.
    struct Stage3Scratch
    {
        vector<vector<uint8_t>> fwd;
        vector<vector<uint8_t>> bwd;
        vector<char> can_be_b;
        vector<char> can_be_notb;
    };

    struct PerBinCoordFlags
    {
        ProofFlag g_up;
        ProofLine g_up_fwd;
        ProofLine g_up_rev;
        ProofFlag g_dn;
        ProofLine g_dn_fwd;
        ProofLine g_dn_rev;
    };

    struct PerBinFlags
    {
        // Per-layer w -> coord flags; covers both DAG and phantom w values
        // (every value referenced by any chain has a flag here).
        vector<unordered_map<long long, PerBinCoordFlags>> coord;
        // Per-layer w -> S flag; same coverage.
        vector<unordered_map<long long, ProofFlag>> s;
    };

    // Backtrack-restored per-bin dead-state cache. dead[b][i] gathers w values
    // for which ~S_{b,i,w} has been emitted at the current search depth (or
    // above); dead_g_dn[b][i] is the same for the variable-load lower-bound
    // ~g_dn lines (only populated at layer n). Pre-populated by the
    // initialiser with the statically dead set, so the per-call propagator
    // never re-emits a line for a node already discharged at Top.
    struct DeadCache
    {
        vector<vector<set<long long>>> dead;
        vector<vector<set<long long>>> dead_g_dn;
    };

    // Per-bin cap on partial sums: sum of all item sizes.
    //
    // We deliberately do NOT intersect with initial upper(loads[b]) or
    // capacities[b] here. Matching Knapsack's design (see
    // dev_docs/knapsack.md "Static reduction"), the static DAG must contain
    // every partial-sum vector that any assignment of items in their initial
    // domains can produce, even ones that already violate the initial cap.
    // The per-call propagator's "eliminated by current bound" path needs a
    // Top-level flag for the over-bound successor to emit its pol step
    // against; dropping the bound filter here guarantees that flag exists,
    // and removes the need to track over-cap phantoms in the scaffolding.
    // The initial cap is then enforced by the same per-call cap-exceeded
    // path that the search will use for tighter current bounds anyway, so
    // nothing is lost in strength.
    auto per_bin_cap(const State & /*state*/, const vector<Integer> & sizes, bool /*have_loads*/, const vector<IntegerVariableID> & /*loads*/,
        const vector<Integer> & /*capacities*/, size_t /*b*/) -> long long
    {
        long long total = 0;
        for (auto & s : sizes)
            total += s.raw_value;
        return total;
    }

    // Forward-only static DAG construction. Walks layer by layer, taking the
    // "exclude" branch when items[i] != b is admissible in the initial
    // domain and the "include" branch when items[i] == b is admissible
    // (subject to the per-bin cap). Phantoms are computed separately below.
    auto build_fwd_dag(const State & state, const vector<IntegerVariableID> & items, const vector<Integer> & sizes, size_t b, long long cap)
        -> PerBinDag
    {
        auto n = items.size();
        auto bin_idx = Integer{static_cast<long long>(b)};

        vector<bool> can_be_b(n), can_be_notb(n);
        for (size_t i = 0; i < n; ++i) {
            can_be_b[i] = state.in_domain(items[i], bin_idx);
            auto v = state.optional_single_value(items[i]);
            can_be_notb[i] = ! (v && *v == bin_idx);
        }

        vector<set<long long>> fwd(n + 1);
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

        PerBinDag dag;
        dag.nodes_at.assign(n + 1, {});
        dag.node_set.assign(n + 1, {});
        for (size_t i = 0; i <= n; ++i) {
            dag.nodes_at[i].assign(fwd[i].begin(), fwd[i].end());
            dag.node_set[i].insert(dag.nodes_at[i].begin(), dag.nodes_at[i].end());
        }

        // Precompute the static successor-position edges used by the per-call
        // sweep. nodes_at is sorted, so a node's position in the next layer is
        // a binary search; -1 marks "successor is not a DAG node".
        auto pos_in = [](const vector<long long> & sorted, long long w) -> int {
            auto it = std::lower_bound(sorted.begin(), sorted.end(), w);
            if (it != sorted.end() && *it == w)
                return static_cast<int>(it - sorted.begin());
            return -1;
        };
        dag.exclude_succ.assign(n, {});
        dag.include_succ.assign(n, {});
        for (size_t i = 0; i < n; ++i) {
            auto sz = sizes[i].raw_value;
            dag.exclude_succ[i].resize(dag.nodes_at[i].size());
            dag.include_succ[i].resize(dag.nodes_at[i].size());
            for (size_t p = 0; p < dag.nodes_at[i].size(); ++p) {
                auto w = dag.nodes_at[i][p];
                dag.exclude_succ[i][p] = pos_in(dag.nodes_at[i + 1], w);
                dag.include_succ[i][p] = pos_in(dag.nodes_at[i + 1], w + sz);
            }
        }
        return dag;
    }

    // Phantoms: non-DAG backward parents that the joint backward chain still
    // needs a flag for. Computed in descending layer order so that
    // phantoms[i] picks up the backward parents of both DAG[i+1] *and*
    // phantoms[i+1] — the chain emitted for a phantom-succ also has a
    // parent flag at its layer (DAG node or recursively-phantom). Mirrors
    // Knapsack's phantom computation, specialised to k=1.
    auto compute_phantoms(PerBinDag & dag, const State & state, const vector<IntegerVariableID> & items, const vector<Integer> & sizes, size_t b)
        -> void
    {
        auto n = items.size();
        auto bin_idx = Integer{static_cast<long long>(b)};

        vector<bool> can_be_b(n), can_be_notb(n);
        for (size_t i = 0; i < n; ++i) {
            can_be_b[i] = state.in_domain(items[i], bin_idx);
            auto v = state.optional_single_value(items[i]);
            can_be_notb[i] = ! (v && *v == bin_idx);
        }

        vector<set<long long>> phantoms(n + 1);
        auto backward_into = [&](size_t i, const auto & succ_w_list) {
            for (auto succ_w : succ_w_list) {
                // exclude branch: parent_w = succ_w
                if (can_be_notb[i] && ! dag.node_set[i].contains(succ_w))
                    phantoms[i].insert(succ_w);
                // include branch: parent_w = succ_w - sizes[i]
                if (can_be_b[i]) {
                    auto parent_w = succ_w - sizes[i].raw_value;
                    if (parent_w >= 0 && ! dag.node_set[i].contains(parent_w))
                        phantoms[i].insert(parent_w);
                }
            }
        };
        for (size_t i = n; i-- > 0;) {
            backward_into(i, dag.nodes_at[i + 1]);
            // phantoms[i+1] is whatever we just populated; iterate it too.
            // Use a snapshot since we don't mutate phantoms[i+1] inside.
            vector<long long> p_at_next(phantoms[i + 1].begin(), phantoms[i + 1].end());
            backward_into(i, p_at_next);
        }

        dag.phantoms_at.assign(n + 1, {});
        dag.phantom_set.assign(n + 1, {});
        for (size_t i = 0; i <= n; ++i) {
            dag.phantoms_at[i].assign(phantoms[i].begin(), phantoms[i].end());
            dag.phantom_set[i].insert(dag.phantoms_at[i].begin(), dag.phantoms_at[i].end());
        }
    }

    // Running sum of (items[j] == b) * sizes[j] over j < i.
    auto running_sum(const vector<IntegerVariableID> & items, const vector<Integer> & sizes, Integer bin_idx, size_t i) -> WPBSum
    {
        WPBSum s;
        for (size_t j = 0; j < i; ++j)
            s += sizes[j] * (items[j] == bin_idx);
        return s;
    }

    auto add_bound_p_term(PolBuilder & b, const State & state, ProofLogger * logger, IntegerVariableID v, bool upper) -> void
    {
        overloaded{[&](const SimpleIntegerVariableID & sv) {
                       b.add_for_literal(logger->names_and_ids_tracker(), upper ? sv <= state.upper_bound(sv) : sv >= state.lower_bound(sv));
                   },
            [&](const ConstantIntegerVariableID &) { throw UnimplementedException{}; },
            [&](const ViewOfIntegerVariableID &) { throw UnimplementedException{}; }}
            .visit(v);
    }

    // Emit one bin's Top-level scaffolding. Mirrors knapsack.cc
    // `emit_scaffolding` specialised to k=1.
    //
    // Order is load-bearing for RUP closure: per-coord forward chains are
    // referenced by joint forward chains, which are referenced by per-state
    // implications and layer ALOs, which are referenced by backward chains,
    // which are referenced by phantom-rule closures, which are referenced by
    // the statically-dead ~S lines. Reordering any of these breaks the proof.
    auto emit_bin_scaffolding(ProofLogger * const logger, size_t b, const vector<IntegerVariableID> & items, const vector<Integer> & sizes,
        bool have_loads, const vector<IntegerVariableID> & loads, const vector<Integer> & capacities, const State & initial_state,
        const PerBinDag & dag, PerBinFlags & flags, const pair<optional<ProofLine>, optional<ProofLine>> & opb_lines, bool full_scaffolding) -> void
    {
        auto n = items.size();
        auto bin_idx = Integer{static_cast<long long>(b)};

        flags.coord.assign(n + 1, {});
        flags.s.assign(n + 1, {});

        vector<WPBSum> running(n + 1);
        for (size_t i = 0; i <= n; ++i)
            running[i] = running_sum(items, sizes, bin_idx, i);

        // 1. Reified flags for DAG nodes.
        for (size_t i = 0; i <= n; ++i) {
            for (auto w : dag.nodes_at[i]) {
                auto wI = Integer{w};
                auto [g_up, gu_fwd, gu_rev] = logger->create_proof_flag_reifying(running[i] >= wI, format("bpup_{}_{}_{}", b, i, w), ProofLevel::Top);
                auto [g_dn, gd_fwd, gd_rev] = logger->create_proof_flag_reifying(running[i] <= wI, format("bpdn_{}_{}_{}", b, i, w), ProofLevel::Top);
                flags.coord[i].emplace(w, PerBinCoordFlags{g_up, gu_fwd, gu_rev, g_dn, gd_fwd, gd_rev});
                auto [s_flag, s_fwd, s_rev] =
                    logger->create_proof_flag_reifying(WPBSum{} + 1_i * g_up + 1_i * g_dn >= 2_i, format("bpat_{}_{}_{}", b, i, w), ProofLevel::Top);
                flags.s[i].emplace(w, s_flag);
                (void)s_fwd;
                (void)s_rev;
            }
        }

        // Per-call (default) strategy: only the reified per-node state
        // flags are defined at Top; the per-call sweep (run_stage3_for_bin)
        // does every aggregation via JustifyUsingRUP, RUP-closing through
        // these flags plus the natural per-bin OPB equations. Skip the
        // upfront phantom flags and forward/backward chain scaffolding.
        if (! full_scaffolding)
            return;

        // 2. Phantom flags. Same shape, just at the phantom's w value.
        for (size_t i = 0; i <= n; ++i) {
            for (auto w : dag.phantoms_at[i]) {
                auto wI = Integer{w};
                auto [g_up, gu_fwd, gu_rev] = logger->create_proof_flag_reifying(running[i] >= wI, format("bpup_{}_{}_{}", b, i, w), ProofLevel::Top);
                auto [g_dn, gd_fwd, gd_rev] = logger->create_proof_flag_reifying(running[i] <= wI, format("bpdn_{}_{}_{}", b, i, w), ProofLevel::Top);
                flags.coord[i].emplace(w, PerBinCoordFlags{g_up, gu_fwd, gu_rev, g_dn, gd_fwd, gd_rev});
                auto [s_flag, s_fwd, s_rev] = logger->create_proof_flag_reifying(
                    WPBSum{} + 1_i * g_up + 1_i * g_dn >= 2_i, format("bpphantom_{}_{}_{}", b, i, w), ProofLevel::Top);
                flags.s[i].emplace(w, s_flag);
                (void)s_fwd;
                (void)s_rev;
            }
        }

        // 3. Per-coord + joint forward chains, for every (parent in DAG[i],
        //    branch, succ in DAG[i+1]).
        //
        //    exclude branch (parent_w = succ_w):
        //      pol succ.g_up.rev + parent.g_up.fwd ; saturate
        //      rup ~parent.g_up + (items[i] == b) + succ.g_up >= 1
        //    include branch (parent_w + sizes[i] = succ_w):
        //      same shape, branch literal = (items[i] != b).
        //    Twin g_dn chains. Then joint chain `~parent.S + branch + succ.S`.
        auto emit_forward_chain = [&](size_t i, long long parent_w, long long succ_w, bool include) {
            const auto & parent_cf = flags.coord[i].at(parent_w);
            const auto & succ_cf = flags.coord[i + 1].at(succ_w);
            auto branch_neg = include ? Literal{items[i] != bin_idx} : Literal{items[i] == bin_idx};

            PolBuilder{}.add(succ_cf.g_up_rev).add(parent_cf.g_up_fwd).saturate().emit(*logger, ProofLevel::Top);
            logger->emit_rup_proof_line(WPBSum{} + 1_i * ! parent_cf.g_up + 1_i * branch_neg + 1_i * succ_cf.g_up >= 1_i, ProofLevel::Top);
            PolBuilder{}.add(succ_cf.g_dn_rev).add(parent_cf.g_dn_fwd).saturate().emit(*logger, ProofLevel::Top);
            logger->emit_rup_proof_line(WPBSum{} + 1_i * ! parent_cf.g_dn + 1_i * branch_neg + 1_i * succ_cf.g_dn >= 1_i, ProofLevel::Top);

            const auto & parent_s = flags.s[i].at(parent_w);
            const auto & succ_s = flags.s[i + 1].at(succ_w);
            logger->emit_rup_proof_line(WPBSum{} + 1_i * ! parent_s + 1_i * branch_neg + 1_i * succ_s >= 1_i, ProofLevel::Top);
        };

        for (size_t i = 0; i < n; ++i) {
            auto sz = sizes[i].raw_value;
            for (auto parent_w : dag.nodes_at[i]) {
                // exclude branch
                if (dag.node_set[i + 1].contains(parent_w))
                    emit_forward_chain(i, parent_w, parent_w, false);
                // include branch
                auto succ_w = parent_w + sz;
                if (dag.node_set[i + 1].contains(succ_w))
                    emit_forward_chain(i, parent_w, succ_w, true);
            }
        }

        // 4. Layer-0 ALO: S_{b,0,0} >= 1. Running sum at i=0 is empty = 0, so
        //    g_up_{b,0,0} (≥ 0) is trivially 1; same for g_dn; conjunction
        //    forces S = 1. RUP from the reverse reifications.
        if (! dag.nodes_at[0].empty()) {
            const auto & root_s = flags.s[0].at(dag.nodes_at[0].front());
            logger->emit_rup_proof_line(WPBSum{} + 1_i * root_s >= 1_i, ProofLevel::Top);
        }

        // 5. Per-state implications and layer ALOs. For each layer 0..n-1:
        //      For each s ∈ DAG[i]: rup ~S_{i,s} + Σ_branch S_{i+1, succ} >= 1
        //          (closes from joint forward chains + var-domain ALO on
        //           items[i]: items[i] == b OR items[i] != b).
        //      Then rup Σ_{w ∈ DAG[i+1]} S_{i+1,w} >= 1.
        for (size_t i = 0; i < n; ++i) {
            auto sz = sizes[i].raw_value;
            for (auto parent_w : dag.nodes_at[i]) {
                const auto & parent_s = flags.s[i].at(parent_w);
                WPBSum impl = WPBSum{} + 1_i * ! parent_s;
                if (dag.node_set[i + 1].contains(parent_w))
                    impl += 1_i * flags.s[i + 1].at(parent_w);
                auto succ_w = parent_w + sz;
                if (succ_w != parent_w && dag.node_set[i + 1].contains(succ_w))
                    impl += 1_i * flags.s[i + 1].at(succ_w);
                logger->emit_rup_proof_line(move(impl) >= 1_i, ProofLevel::Top);
            }

            WPBSum alo;
            for (auto w : dag.nodes_at[i + 1])
                alo += 1_i * flags.s[i + 1].at(w);
            logger->emit_rup_proof_line(move(alo) >= 1_i, ProofLevel::Top);
        }

        // 6. Backward chains for each (succ in DAG[i+1] ∪ phantoms[i+1], branch).
        //    exclude branch: parent_w = succ_w.
        //    include branch: parent_w = succ_w - sizes[i]. If parent_w < 0,
        //      negative-coord case: direct rup ~succ.S + (items[i] != b) >= 1
        //      (RUP-closes from succ.S forcing running_sum_at_{i+1} >= succ_w
        //       and items[i] = b would force running_sum_at_i + sizes[i] = succ_w,
        //       i.e., running_sum_at_i < 0, contradicting the non-negativity
        //       implicit in the integer encoding).
        //    Phantoms-as-succ are included so the joint-only-phantom rule
        //    below can chain through them.
        auto emit_backward_chain = [&](size_t i, long long succ_w) {
            const auto & succ_s = flags.s[i + 1].at(succ_w);
            // exclude branch: parent_w = succ_w (always >= 0)
            {
                bool parent_is_dag = dag.node_set[i].contains(succ_w);
                bool parent_is_phantom = dag.phantom_set[i].contains(succ_w);
                if (parent_is_dag || parent_is_phantom) {
                    const auto & parent_cf = flags.coord[i].at(succ_w);
                    const auto & succ_cf = flags.coord[i + 1].at(succ_w);
                    PolBuilder{}.add(succ_cf.g_up_fwd).add(parent_cf.g_up_rev).saturate().emit(*logger, ProofLevel::Top);
                    logger->emit_rup_proof_line(
                        WPBSum{} + 1_i * ! succ_cf.g_up + 1_i * (items[i] == bin_idx) + 1_i * parent_cf.g_up >= 1_i, ProofLevel::Top);
                    PolBuilder{}.add(succ_cf.g_dn_fwd).add(parent_cf.g_dn_rev).saturate().emit(*logger, ProofLevel::Top);
                    logger->emit_rup_proof_line(
                        WPBSum{} + 1_i * ! succ_cf.g_dn + 1_i * (items[i] == bin_idx) + 1_i * parent_cf.g_dn >= 1_i, ProofLevel::Top);
                    const auto & parent_s = flags.s[i].at(succ_w);
                    logger->emit_rup_proof_line(WPBSum{} + 1_i * ! succ_s + 1_i * (items[i] == bin_idx) + 1_i * parent_s >= 1_i, ProofLevel::Top);
                }
                else {
                    // No flag exists for succ_w at layer i (shouldn't happen
                    // post-phantom-closure; assert via the direct chain).
                    logger->emit_rup_proof_line(WPBSum{} + 1_i * ! succ_s + 1_i * (items[i] == bin_idx) >= 1_i, ProofLevel::Top);
                }
            }
            // include branch: parent_w = succ_w - sizes[i]
            {
                auto parent_w = succ_w - sizes[i].raw_value;
                if (parent_w < 0) {
                    logger->emit_rup_proof_line(WPBSum{} + 1_i * ! succ_s + 1_i * (items[i] != bin_idx) >= 1_i, ProofLevel::Top);
                }
                else {
                    bool parent_is_dag = dag.node_set[i].contains(parent_w);
                    bool parent_is_phantom = dag.phantom_set[i].contains(parent_w);
                    if (parent_is_dag || parent_is_phantom) {
                        const auto & parent_cf = flags.coord[i].at(parent_w);
                        const auto & succ_cf = flags.coord[i + 1].at(succ_w);
                        PolBuilder{}.add(succ_cf.g_up_fwd).add(parent_cf.g_up_rev).saturate().emit(*logger, ProofLevel::Top);
                        logger->emit_rup_proof_line(
                            WPBSum{} + 1_i * ! succ_cf.g_up + 1_i * (items[i] != bin_idx) + 1_i * parent_cf.g_up >= 1_i, ProofLevel::Top);
                        PolBuilder{}.add(succ_cf.g_dn_fwd).add(parent_cf.g_dn_rev).saturate().emit(*logger, ProofLevel::Top);
                        logger->emit_rup_proof_line(
                            WPBSum{} + 1_i * ! succ_cf.g_dn + 1_i * (items[i] != bin_idx) + 1_i * parent_cf.g_dn >= 1_i, ProofLevel::Top);
                        const auto & parent_s = flags.s[i].at(parent_w);
                        logger->emit_rup_proof_line(WPBSum{} + 1_i * ! succ_s + 1_i * (items[i] != bin_idx) + 1_i * parent_s >= 1_i, ProofLevel::Top);
                    }
                    else {
                        logger->emit_rup_proof_line(WPBSum{} + 1_i * ! succ_s + 1_i * (items[i] != bin_idx) >= 1_i, ProofLevel::Top);
                    }
                }
            }
        };

        for (size_t i = 0; i < n; ++i) {
            for (auto succ_w : dag.nodes_at[i + 1])
                emit_backward_chain(i, succ_w);
            for (auto succ_w : dag.phantoms_at[i + 1])
                emit_backward_chain(i, succ_w);
        }

        // 7. Phantom closure. For k=1 every phantom is per-coord-phantom
        //    (the joint and the per-coord projection coincide): for each
        //    u ∈ DAG[i]'s w values, emit a pair-wise pol over (u, phantom_w)
        //    and close with ~S_phantom >= 1 via RUP.
        for (size_t i = 0; i <= n; ++i) {
            for (auto p_w : dag.phantoms_at[i]) {
                const auto & p_cf = flags.coord[i].at(p_w);

                for (auto u : dag.nodes_at[i]) {
                    if (u == p_w)
                        continue;
                    const auto & u_cf = flags.coord[i].at(u);
                    if (u > p_w) {
                        PolBuilder{}.add(u_cf.g_up_fwd).add(p_cf.g_dn_fwd).saturate().emit(*logger, ProofLevel::Top);
                    }
                    else {
                        PolBuilder{}.add(p_cf.g_up_fwd).add(u_cf.g_dn_fwd).saturate().emit(*logger, ProofLevel::Top);
                    }
                }

                const auto & s_flag = flags.s[i].at(p_w);
                logger->emit_rup_proof_line(WPBSum{} + 1_i * ! s_flag >= 1_i, ProofLevel::Top);
            }
        }

        // Note on statically-dead ~S lines: deliberately not emitted at Top.
        // Layer-n static dead requires a pol step combining g_up/g_dn forward
        // axioms with the OPB equation halves and the current load bound;
        // single-valued loads expose tricky cases (`add_for_literal` for
        // `load <= c` when load is already c picks a trivial reverse-reif
        // axiom that doesn't usefully close the pol). The per-call sweep's
        // first invocation handles all these cases via the same pol+RUP
        // machinery it uses for dynamic interior-hole filtering, and the
        // backtrack-restored DeadCache prevents redundant emission within a
        // subtree. Cost: one set of static-dead ~S lines per fresh subtree
        // root rather than once globally. Worth revisiting if a measurement
        // shows the per-subtree cost is significant.
        (void)initial_state;
        (void)have_loads;
        (void)loads;
        (void)capacities;
        (void)opb_lines;
    }

    // Per-call k=1 propagator port of Knapsack's `propagate`. For each bin
    // independently: forward walk under current item domains restricted to
    // the static DAG, emit dead-state ~S lines (cap-exceed via pol +
    // current load upper, then ~S RUP; pure forward-unreachable as ~S RUP
    // alone). Then for variable-load: layer-n filtering by current load
    // bounds and interior holes, terminal bound inferences via per-state
    // pol chains + aggregating RUPs. Backward pass over predecessor map
    // for dead-intermediate ~S and items[i] != b pruning for unsupported
    // bin candidates. Empty layer-n → contradiction.
    auto propagate_bin(const State & state, auto & inference, ProofLogger * const logger, const vector<IntegerVariableID> & items,
        const vector<Integer> & sizes, bool have_loads, const vector<IntegerVariableID> & loads, const vector<Integer> & capacities, size_t b,
        const PerBinDag & dag, const PerBinFlags & flags, const pair<optional<ProofLine>, optional<ProofLine>> & opb_lines, DeadCache & cache,
        const Reason & reason, const ConstraintID & owner) -> void
    {
        auto n = items.size();
        auto bin_idx = Integer{static_cast<long long>(b)};

        vector<bool> can_be_b(n), can_be_notb(n);
        for (size_t i = 0; i < n; ++i) {
            can_be_b[i] = state.in_domain(items[i], bin_idx);
            auto v = state.optional_single_value(items[i]);
            can_be_notb[i] = ! (v && *v == bin_idx);
        }

        const bool emitting = logger && logger->get_assertion_level() == AssertionLevel::Off;

        int temporary_proof_level = 0;
        if (emitting)
            temporary_proof_level = logger->temporary_proof_level();

        // (parent_w, branch_is_include) edges that landed on each live node.
        struct LiveNode
        {
            vector<pair<long long, bool>> predecessors;
        };

        list<map<long long, LiveNode>> completed_layers;
        completed_layers.emplace_back();
        completed_layers.back().emplace(0LL, LiveNode{});

        long long load_upper_b = have_loads ? state.upper_bound(loads[b]).raw_value : capacities[b].raw_value;

        for (size_t i = 0; i < n; ++i) {
            map<long long, LiveNode> growing;
            auto sz = sizes[i].raw_value;

            for (const auto & [parent_w, _] : completed_layers.back()) {
                if (can_be_notb[i]) {
                    auto succ_w = parent_w;
                    if (dag.node_set[i + 1].contains(succ_w)) {
                        auto it = growing.find(succ_w);
                        if (it == growing.end())
                            it = growing.emplace(succ_w, LiveNode{}).first;
                        it->second.predecessors.emplace_back(parent_w, false);
                    }
                }
                if (can_be_b[i]) {
                    auto succ_w = parent_w + sz;
                    if (dag.node_set[i + 1].contains(succ_w)) {
                        auto it = growing.find(succ_w);
                        if (it == growing.end())
                            it = growing.emplace(succ_w, LiveNode{}).first;
                        it->second.predecessors.emplace_back(parent_w, true);
                    }
                }
            }

            // Drop cap-exceeded successors from `growing` so the per-call walk
            // never carries a state we already know is over current upper.
            erase_if(growing, [&](const auto & item) { return item.first > load_upper_b; });

            // For every w in DAG[i+1] not in `growing`, emit ~S at Current,
            // cached. Two flavours:
            //   * cap-exceeded — pol step combining succ.g_up.fwd with the
            //     LE half of the OPB equation. For constant-cap the cap is a
            //     constant inside that line (no extra bound term); for
            //     variable-load we add `load <= current upper` so the pol's
            //     RHS reflects the actual current bound.
            //   * forward-unreachable under current dom — pure ~S RUP. UP
            //     closes via Top backward chains + cached ~S of dead
            //     predecessors + items[i] domain literals.
            if (emitting) {
                for (auto w : dag.nodes_at[i + 1]) {
                    if (growing.contains(w))
                        continue;
                    if (cache.dead[b][i + 1].contains(w))
                        continue;

                    if (w > load_upper_b && opb_lines.first.has_value()) {
                        const auto & cf = flags.coord[i + 1].at(w);
                        PolBuilder bb;
                        bb.add(cf.g_up_fwd).add(*opb_lines.first);
                        if (have_loads)
                            add_bound_p_term(bb, state, logger, loads[b], true);
                        bb.emit(*logger, ProofLevel::Temporary);
                    }

                    auto s_flag = flags.s[i + 1].at(w);
                    logger->emit_rup_proof_line_under_reason(eager_reason(reason, state), WPBSum{} + 1_i * ! s_flag >= 1_i, ProofLevel::Current);
                    cache.dead[b][i + 1].insert(w);
                }
            }

            completed_layers.emplace_back(move(growing));
        }

        // Variable-load only: layer-n filtering by current load bounds and
        // interior holes. The pure ~g_dn / ~S facts hold for the whole subtree
        // below the current search node; promoted to Current and cached.
        if (have_loads) {
            // Lower bound filter.
            for (auto it = completed_layers.back().begin(), end = completed_layers.back().end(); it != end;) {
                if (it->first < state.lower_bound(loads[b]).raw_value) {
                    if (emitting) {
                        bool need_s = ! cache.dead[b][n].contains(it->first);
                        bool need_g_dn = ! cache.dead_g_dn[b][n].contains(it->first);
                        if (need_s || need_g_dn) {
                            const auto & cf = flags.coord[n].at(it->first);
                            if (opb_lines.second.has_value()) {
                                PolBuilder bb;
                                bb.add(cf.g_dn_fwd).add(*opb_lines.second);
                                add_bound_p_term(bb, state, logger, loads[b], false);
                                bb.emit(*logger, ProofLevel::Temporary);
                            }
                            if (need_g_dn) {
                                logger->emit_rup_proof_line_under_reason(
                                    eager_reason(reason, state), WPBSum{} + 1_i * ! cf.g_dn >= 1_i, ProofLevel::Current);
                                cache.dead_g_dn[b][n].insert(it->first);
                            }
                            if (need_s) {
                                logger->emit_rup_proof_line_under_reason(
                                    eager_reason(reason, state), WPBSum{} + 1_i * ! flags.s[n].at(it->first) >= 1_i, ProofLevel::Current);
                                cache.dead[b][n].insert(it->first);
                            }
                        }
                    }
                    completed_layers.back().erase(it++);
                }
                else
                    ++it;
            }

            // Interior holes.
            for (auto it = completed_layers.back().begin(), end = completed_layers.back().end(); it != end;) {
                if (! state.in_domain(loads[b], Integer{it->first})) {
                    if (emitting && ! cache.dead[b][n].contains(it->first)) {
                        const auto & cf = flags.coord[n].at(it->first);
                        if (opb_lines.first.has_value() && opb_lines.second.has_value()) {
                            PolBuilder{}.add(cf.g_dn_fwd).add(*opb_lines.second).emit(*logger, ProofLevel::Temporary);
                            PolBuilder{}.add(cf.g_up_fwd).add(*opb_lines.first).emit(*logger, ProofLevel::Temporary);
                            logger->emit_rup_proof_line_under_reason(eager_reason(reason, state),
                                WPBSum{} + 1_i * ! flags.s[n].at(it->first) + 1_i * (loads[b] == Integer{it->first}) >= 1_i, ProofLevel::Temporary);
                        }
                        logger->emit_rup_proof_line_under_reason(
                            eager_reason(reason, state), WPBSum{} + 1_i * ! flags.s[n].at(it->first) >= 1_i, ProofLevel::Current);
                        cache.dead[b][n].insert(it->first);
                    }
                    completed_layers.back().erase(it++);
                }
                else
                    ++it;
            }
        }

        if (completed_layers.back().empty()) {
            if (emitting)
                logger->emit_rup_proof_line_under_reason(eager_reason(reason, state), WPBSum{} >= 1_i, ProofLevel::Temporary);
            inference.contradiction(logger, JustifyUsingRUP{hints::BinPacking{owner}}, reason);
            if (emitting)
                logger->forget_proof_level(temporary_proof_level);
            return;
        }

        // Variable-load only: terminal bound inferences for loads[b].
        if (have_loads) {
            auto [lo_it, hi_it] = minmax_element(
                completed_layers.back(), [](const pair<long long, LiveNode> & a, const pair<long long, LiveNode> & b) { return a.first < b.first; });
            auto lo = lo_it->first;
            auto hi = hi_it->first;
            vector<Literal> inferences;
            inferences.emplace_back(loads[b] >= Integer{lo});
            inferences.emplace_back(loads[b] < Integer{hi} + 1_i);

            for (auto v : state.each_value_immutable(loads[b])) {
                if (v.raw_value > lo && v.raw_value < hi + 1 &&
                    none_of(completed_layers.back(), [&](const pair<long long, LiveNode> & a) { return a.first == v.raw_value; }))
                    inferences.emplace_back(loads[b] != v);
            }

            if (emitting && opb_lines.first.has_value() && opb_lines.second.has_value()) {
                for (const auto & [w, _] : completed_layers.back()) {
                    const auto & cf = flags.coord[n].at(w);
                    PolBuilder{}.add(*opb_lines.first).add(cf.g_up_fwd).emit(*logger, ProofLevel::Temporary);
                    logger->emit_rup_proof_line_under_reason(
                        eager_reason(reason, state), WPBSum{} + 1_i * ! cf.g_up + 1_i * (loads[b] >= Integer{lo}) >= 1_i, ProofLevel::Temporary);

                    PolBuilder{}.add(*opb_lines.second).add(cf.g_dn_fwd).emit(*logger, ProofLevel::Temporary);
                    logger->emit_rup_proof_line_under_reason(
                        eager_reason(reason, state), WPBSum{} + 1_i * ! cf.g_dn + 1_i * (loads[b] <= Integer{hi}) >= 1_i, ProofLevel::Temporary);
                }
                logger->emit_rup_proof_line_under_reason(
                    eager_reason(reason, state), WPBSum{} + 1_i * (loads[b] >= Integer{lo}) >= 1_i, ProofLevel::Temporary);
                logger->emit_rup_proof_line_under_reason(
                    eager_reason(reason, state), WPBSum{} + 1_i * (loads[b] <= Integer{hi}) >= 1_i, ProofLevel::Temporary);
            }

            inference.infer_all(logger, inferences, JustifyUsingRUP{hints::BinPacking{owner}}, reason);
        }

        // Backward pass: identify states / branches supported by a path to
        // the surviving layer-n set. Emit ~S for dead intermediates; for
        // each item i, if the "items[i] == b" branch is never taken in any
        // surviving path, infer items[i] != b. (Note: we don't infer
        // items[i] == b from this pass — that direction needs a separate
        // argument involving all OTHER bins, which the per-bin sweep can't
        // see. Per-bin GAC is one direction only.)
        int var_number = static_cast<int>(n) - 1;
        for (auto layer = completed_layers.rbegin(); layer != completed_layers.rend() && next(layer) != completed_layers.rend();
            ++layer, --var_number) {
            set<long long> reached_parents;
            bool include_supported = false;
            for (const auto & [_, node] : *layer) {
                for (const auto & [parent_w, is_include] : node.predecessors) {
                    reached_parents.insert(parent_w);
                    if (is_include)
                        include_supported = true;
                }
            }

            for (auto it = next(layer)->begin(), end = next(layer)->end(); it != end;) {
                if (reached_parents.contains(it->first))
                    ++it;
                else {
                    if (emitting && ! cache.dead[b][var_number].contains(it->first)) {
                        auto s_flag = flags.s[var_number].at(it->first);
                        logger->emit_rup_proof_line_under_reason(eager_reason(reason, state), WPBSum{} + 1_i * ! s_flag >= 1_i, ProofLevel::Current);
                        cache.dead[b][var_number].insert(it->first);
                    }
                    next(layer)->erase(it++);
                }
            }

            if (can_be_b[var_number] && ! include_supported)
                inference.infer_not_equal(logger, items[var_number], bin_idx, JustifyUsingRUP{hints::BinPacking{owner}}, reason);
        }

        if (emitting)
            logger->forget_proof_level(temporary_proof_level);
    }

    // Per-call (default) Stage 3 per-bin DAG sweep. For each bin, recompute
    // alive (i, w) nodes under the current item domains (forward + backward
    // reachability restricted to the static DAG), then for each candidate
    // items[i] == b that has no support at any alive (i, w) with
    // (i+1, w + sizes[i]) also alive, prune items[i] != b.
    //
    // Proof: a plain JustifyUsingRUP at the prune site suffices — VeriPB's
    // unit propagation closes the contradiction through the per-node reified
    // state flags (defined at Top by emit_bin_scaffolding with
    // full_scaffolding=false) plus the natural per-bin OPB equation. No
    // explicit chain or dead-node lines are emitted per call; the
    // inequality reifications carry that reach implicitly. This is the
    // strategy that wins on both proof size and verify time (see
    // dev_docs/bin-packing.md); the upfront alternative (propagate_bin) is
    // the opt-in enabled by upfront_proof=true.
    auto run_stage3_for_bin(const State & state, auto & inference, ProofLogger * logger, const vector<IntegerVariableID> & items,
        const PerBinDag & dag, Stage3Scratch & scratch, size_t b, const Reason & reason, const ConstraintID & owner) -> void
    {
        auto n = items.size();
        auto bin_idx = Integer{static_cast<long long>(b)};

        auto & can_be_b = scratch.can_be_b;
        auto & can_be_notb = scratch.can_be_notb;
        for (size_t i = 0; i < n; ++i) {
            can_be_b[i] = static_cast<char>(state.in_domain(items[i], bin_idx));
            auto v = state.optional_single_value(items[i]);
            can_be_notb[i] = static_cast<char>(! (v && *v == bin_idx));
        }

        auto & fwd = scratch.fwd;
        auto & bwd = scratch.bwd;

        // Forward reachability under current domains, restricted to the static
        // DAG, over position-indexed bitmaps. fwd starts all-zero; layer 0 has
        // exactly node 0 (build_fwd_dag seeds it), which is always reachable.
        for (auto & layer : fwd)
            std::fill(layer.begin(), layer.end(), uint8_t{0});
        if (! dag.nodes_at[0].empty())
            fwd[0][0] = 1;
        for (size_t i = 0; i < n; ++i) {
            const auto & excl = dag.exclude_succ[i];
            const auto & incl = dag.include_succ[i];
            auto & next_layer = fwd[i + 1];
            for (size_t p = 0; p < fwd[i].size(); ++p) {
                if (! fwd[i][p])
                    continue;
                if (can_be_notb[i] && excl[p] >= 0)
                    next_layer[excl[p]] = 1;
                if (can_be_b[i] && incl[p] >= 0)
                    next_layer[incl[p]] = 1;
            }
        }

        // Backward reachability. Layer n's accepting terminals are the
        // forward-reachable layer-n nodes (static reduction already encodes
        // acceptance). A node at layer i is backward-reachable if some
        // admissible branch lands on a backward-reachable successor. Every
        // cell is overwritten, so no pre-zeroing is needed.
        for (size_t p = 0; p < bwd[n].size(); ++p)
            bwd[n][p] = fwd[n][p];
        for (long long i = static_cast<long long>(n) - 1; i >= 0; --i) {
            const auto & excl = dag.exclude_succ[i];
            const auto & incl = dag.include_succ[i];
            const auto & next_bwd = bwd[i + 1];
            for (size_t p = 0; p < bwd[i].size(); ++p) {
                uint8_t reachable = 0;
                if (can_be_notb[i] && excl[p] >= 0 && next_bwd[excl[p]])
                    reachable = 1;
                else if (can_be_b[i] && incl[p] >= 0 && next_bwd[incl[p]])
                    reachable = 1;
                bwd[i][p] = reachable;
            }
        }

        // Prune items[i] != b when the "include" branch has no support: no
        // alive node (fwd ∩ bwd) at layer i whose include-successor is also
        // alive at layer i+1.
        for (size_t i = 0; i < n; ++i) {
            if (! can_be_b[i])
                continue;
            const auto & incl = dag.include_succ[i];
            const auto & next_fwd = fwd[i + 1];
            const auto & next_bwd = bwd[i + 1];
            bool supported = false;
            for (size_t p = 0; p < fwd[i].size(); ++p) {
                if (! (fwd[i][p] && bwd[i][p]))
                    continue;
                auto q = incl[p];
                if (q >= 0 && next_fwd[q] && next_bwd[q]) {
                    supported = true;
                    break;
                }
            }
            if (! supported)
                inference.infer_not_equal(logger, items[i], bin_idx, JustifyUsingRUP{hints::BinPacking{owner}}, reason);
        }
    }

    auto run_stage2(const State & state, auto & inference, ProofLogger * logger, const vector<IntegerVariableID> & items,
        const vector<Integer> & sizes, const vector<IntegerVariableID> & loads, const vector<Integer> & capacities, bool have_loads,
        const ConstraintID & owner) -> void
    {
        auto num_bins = have_loads ? loads.size() : capacities.size();
        // The reason literal lists are only consumed by a reason-materialising
        // (proof-logging) tracker; off that path skip building them entirely.
        // still_possible drives the inference logic, so it is always built, but
        // reused across bins to keep the per-wake allocation count down.
        const bool need_reasons = inference.want_reasons();
        ReasonLiterals forced_reason, excluded_reason;
        vector<size_t> still_possible;
        for (size_t b = 0; b < num_bins; ++b) {
            auto bin_idx = Integer(static_cast<long long>(b));

            forced_reason.clear();
            excluded_reason.clear();
            still_possible.clear();
            Integer floor = 0_i, ceiling = 0_i;
            for (size_t i = 0; i < items.size(); ++i) {
                auto v = state.optional_single_value(items[i]);
                if (v && *v == bin_idx) {
                    floor += sizes[i];
                    ceiling += sizes[i];
                    if (need_reasons)
                        forced_reason.emplace_back(items[i] == bin_idx);
                }
                else if (! state.in_domain(items[i], bin_idx)) {
                    if (need_reasons)
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
                    inference.infer_greater_than_or_equal(logger, loads[b], floor, JustifyUsingRUP{hints::BinPacking{owner}}, forced_reason);
                    load_lo = floor;
                }
                if (ceiling < load_hi) {
                    inference.infer_less_than(logger, loads[b], ceiling + 1_i, JustifyUsingRUP{hints::BinPacking{owner}}, excluded_reason);
                    load_hi = ceiling;
                }

                for (auto i : still_possible) {
                    if (floor + sizes[i] > load_hi) {
                        ReasonLiterals r = forced_reason;
                        r.emplace_back(loads[b] < load_hi + 1_i);
                        inference.infer_not_equal(logger, items[i], bin_idx, JustifyUsingRUP{hints::BinPacking{owner}}, move(r));
                    }
                    else if (ceiling - sizes[i] < load_lo) {
                        ReasonLiterals r = excluded_reason;
                        r.emplace_back(loads[b] >= load_lo);
                        inference.infer_equal(logger, items[i], bin_idx, JustifyUsingRUP{hints::BinPacking{owner}}, move(r));
                    }
                }
            }
            else {
                if (floor > capacities[b]) {
                    inference.contradiction(logger, JustifyUsingRUP{hints::BinPacking{owner}}, forced_reason);
                }
                for (auto i : still_possible) {
                    if (floor + sizes[i] > capacities[b]) {
                        inference.infer_not_equal(logger, items[i], bin_idx, JustifyUsingRUP{hints::BinPacking{owner}}, forced_reason);
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
    // Per-bin OPB equation line numbers, stored as (LE-half, GE-half):
    //   variable-load: (sum <= load, sum >= load)
    //   constant-cap:  (sum <= cap,  nullopt)
    vector<pair<optional<ProofLine>, optional<ProofLine>>> opb_lines;
    // Per-bin reusable scratch for the per-call sweep, sized once in prepare()
    // to match each bin's DAG so the hot path never allocates. The bridge is
    // per-constraint-clone, so a search owns its scratch exclusively.
    vector<Stage3Scratch> stage3_scratch;
};

BinPacking::BinPacking(vector<IntegerVariableID> items, vector<Integer> sizes, vector<IntegerVariableID> loads) :
    _items(move(items)), _sizes(move(sizes)), _loads(move(loads)), _capacities(), _have_loads(true)
{
}

BinPacking::BinPacking(vector<IntegerVariableID> items, vector<Integer> sizes, vector<Integer> capacities) :
    _items(move(items)), _sizes(move(sizes)), _loads(), _capacities(move(capacities)), _have_loads(false)
{
}

auto BinPacking::with_consistency(BinPackingConsistency level) -> BinPacking &
{
    _bounds_only = holds_alternative<consistency::BC>(level);
    return *this;
}

auto BinPacking::with_proof_strategy(BinPackingProofStrategy strategy) -> BinPacking &
{
    _upfront_proof = holds_alternative<proof_strategy::Upfront>(strategy);
    return *this;
}

auto BinPacking::clone() const -> unique_ptr<Constraint>
{
    auto cloned = _have_loads ? make_unique<BinPacking>(_items, _sizes, _loads) : make_unique<BinPacking>(_items, _sizes, _capacities);
    cloned->with_consistency(_bounds_only ? BinPackingConsistency{consistency::BC{}} : BinPackingConsistency{consistency::GAC{}});
    cloned->with_proof_strategy(
        _upfront_proof ? BinPackingProofStrategy{proof_strategy::Upfront{}} : BinPackingProofStrategy{proof_strategy::PerCall{}});
    return cloned;
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
        // Build the per-bin static (forward-only) DAGs and compute phantoms.
        // Flag handles are populated by the initialiser (once the logger is
        // available); opb_lines is filled by define_proof_model when proof
        // logging is on. Both are sized here so propagator code can index by
        // bin without checking populated-ness even when proofs are off.
        _bridge = make_shared<DagBridge>();
        _bridge->dags.reserve(num_bins);
        _bridge->flags.assign(num_bins, {});
        _bridge->opb_lines.assign(num_bins, {nullopt, nullopt});
        _bridge->stage3_scratch.assign(num_bins, {});
        for (size_t b = 0; b < num_bins; ++b) {
            auto cap = per_bin_cap(initial_state, _sizes, _have_loads, _loads, _capacities, b);
            auto dag = build_fwd_dag(initial_state, _items, _sizes, b, cap);
            compute_phantoms(dag, initial_state, _items, _sizes, b);

            // Size the per-call scratch to this bin's DAG so the hot path only
            // fills existing buffers, never grows them.
            auto & sc = _bridge->stage3_scratch[b];
            sc.fwd.resize(dag.nodes_at.size());
            sc.bwd.resize(dag.nodes_at.size());
            for (size_t i = 0; i < dag.nodes_at.size(); ++i) {
                sc.fwd[i].assign(dag.nodes_at[i].size(), uint8_t{0});
                sc.bwd[i].assign(dag.nodes_at[i].size(), uint8_t{0});
            }
            sc.can_be_b.assign(_items.size(), char{0});
            sc.can_be_notb.assign(_items.size(), char{0});

            _bridge->dags.push_back(move(dag));
        }

        DeadCache initial_cache{vector<vector<set<long long>>>(num_bins, vector<set<long long>>(_items.size() + 1)),
            vector<vector<set<long long>>>(num_bins, vector<set<long long>>(_items.size() + 1))};
        _dead_cache_idx = initial_state.add_constraint_state(move(initial_cache));
    }

    return true;
}

auto BinPacking::define_proof_model(ProofModel & model) -> void
{
    // Natural definition: for each bin b,
    //   sum_i { sizes[i] * [items[i] == b] } == loads[b]   (variable-load form)
    //   sum_i { sizes[i] * [items[i] == b] } <= cap[b]     (constant-cap form)
    //
    // The Stage 3 DAG-shaped scaffolding lives at ProofLevel::Top via the
    // initialiser; see dev_docs/bin-packing.md. Capture the OPB line numbers
    // into the bridge so per-call pol steps can reference them (variable-load
    // cap-exceed / load-bound filtering). Plain add_constraint returns void
    // now, so the labelled overload is used to obtain the referable line
    // handles; the @c[id][role] labels are internal (BinPacking is not a
    // cake-encoded constraint).
    auto num_bins = _have_loads ? _loads.size() : _capacities.size();
    for (size_t b = 0; b < num_bins; ++b) {
        auto bin_idx = Integer(static_cast<long long>(b));
        WPBSum sum;
        for (const auto & [i, item] : enumerate(_items))
            sum += _sizes[i] * (item == bin_idx);

        if (_have_loads) {
            // The labelled equality overload returns {LE-half, GE-half}. Store
            // first=LE (sum <= load), second=GE (sum >= load) so per-call pol
            // steps don't have to distinguish forms.
            auto [le, ge] =
                model.add_labelled_constraint(constraint_id(), std::to_string(b) + "_le", std::to_string(b) + "_ge", sum == 1_i * _loads[b]);
            if (_bridge)
                _bridge->opb_lines[b] = {le, ge};
        }
        else {
            auto le = model.add_labelled_constraint(constraint_id(), std::to_string(b) + "_le", sum <= _capacities[b]);
            if (_bridge)
                _bridge->opb_lines[b] = {le, nullopt};
        }
    }
}

auto BinPacking::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _items.begin(), _items.end());
    if (_have_loads)
        triggers.on_bounds.insert(triggers.on_bounds.end(), _loads.begin(), _loads.end());

    if (! _bounds_only) {
        // Per-bin Stage 3 Top-level scaffolding. In both strategies the
        // reified g_up/g_dn/S flags for every DAG node are defined at
        // ProofLevel::Top. When upfront_proof is set the initialiser
        // additionally derives the full chain scaffolding (phantom flags;
        // per-coord+joint forward chains; layer-0 ALO; per-state
        // implications and per-layer ALOs; per-(succ, branch) backward
        // chains; phantom closures — the upfront pattern from Knapsack §3,
        // see dev_docs/knapsack.md and dev_docs/bin-packing.md). When it is
        // clear (the default) only the flag definitions are emitted and the
        // per-call sweep does every aggregation via RUP — smaller and faster
        // to verify. In assertion mode the propagator's inferences are
        // asserted under the typed hint instead of RUP-derived, so the
        // scaffolding would be wasted output and is skipped.
        propagators.install_initialiser([items = _items, sizes = _sizes, have_loads = _have_loads, loads = _loads, capacities = _capacities,
                                            bridge = _bridge, upfront = _upfront_proof](State & state, auto &, ProofLogger * const logger) -> void {
            if (! logger || logger->get_assertion_level() != AssertionLevel::Off)
                return;
            for (size_t b = 0; b < bridge->dags.size(); ++b) {
                emit_bin_scaffolding(
                    logger, b, items, sizes, have_loads, loads, capacities, state, bridge->dags[b], bridge->flags[b], bridge->opb_lines[b], upfront);
            }
        });
    }

    // Stage 2 (per-bin bounds) always runs. Stage 3 (per-bin DAG sweep) only
    // runs when ! bounds_only. Both share state through `state`; Stage 3 sees
    // the bounds Stage 2 derived. The Stage 3 proof strategy is chosen by
    // upfront_proof: run_stage3_for_bin (default, bare per-call RUP prunes)
    // or propagate_bin (opt-in, references the upfront chain scaffolding).
    propagators.install(
        constraint_id(),
        [items = _items, sizes = _sizes, loads = _loads, capacities = _capacities, have_loads = _have_loads, bounds_only = _bounds_only,
            bridge = _bridge, dead_cache_handle = _dead_cache_idx, upfront = _upfront_proof,
            owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            run_stage2(state, inference, logger, items, sizes, loads, capacities, have_loads, owner);

            if (! bounds_only && bridge) {
                auto num_bins = have_loads ? loads.size() : capacities.size();
                if (upfront) {
                    // Reason has to include the load variables when variable-load
                    // form is in use, otherwise the cap-exceeded / load-bound /
                    // interior-hole ~S lines aren't sound under their reasons.
                    // For constant-cap, items alone suffice (the cap is static).
                    vector<IntegerVariableID> reason_vars;
                    reason_vars.reserve(items.size() + (have_loads ? loads.size() : 0));
                    reason_vars.insert(reason_vars.end(), items.begin(), items.end());
                    if (have_loads)
                        reason_vars.insert(reason_vars.end(), loads.begin(), loads.end());
                    auto reason = generic_reason(reason_vars);
                    auto & cache = any_cast<DeadCache &>(state.get_constraint_state(*dead_cache_handle));
                    for (size_t b = 0; b < num_bins; ++b)
                        propagate_bin(state, inference, logger, items, sizes, have_loads, loads, capacities, b, bridge->dags[b], bridge->flags[b],
                            bridge->opb_lines[b], cache, reason, owner);
                }
                else {
                    // Default per-call strategy: item-var pruning only; the
                    // load bounds are handled by Stage 2. Reason is the item
                    // variables (the bare RUP prune closes through the Top
                    // flag definitions + the per-bin OPB equation).
                    auto reason = generic_reason(items);
                    for (size_t b = 0; b < num_bins; ++b)
                        run_stage3_for_bin(state, inference, logger, items, bridge->dags[b], bridge->stage3_scratch[b], b, reason, owner);
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto BinPacking::constraint_type() const -> string
{
    return "binpacking";
}

auto BinPacking::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    vector<SExpr> items;
    for (const auto & item : _items)
        items.push_back(tracker.s_expr_term_of(item));

    vector<SExpr> sizes;
    for (const auto & sz : _sizes)
        sizes.push_back(SExpr::atom(sz.to_string()));

    if (_have_loads) {
        vector<SExpr> loads;
        for (const auto & l : _loads)
            loads.push_back(tracker.s_expr_term_of(l));
        return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(move(items)),
            SExpr::list(move(sizes)), SExpr::atom("loads"), SExpr::list(move(loads))});
    }

    vector<SExpr> capacities;
    for (const auto & c : _capacities)
        capacities.push_back(SExpr::atom(c.to_string()));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(move(items)), SExpr::list(move(sizes)),
        SExpr::atom("capacities"), SExpr::list(move(capacities))});
}
