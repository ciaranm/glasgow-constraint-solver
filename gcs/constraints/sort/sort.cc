#include <gcs/constraints/sort/hints.hh>
#include <gcs/constraints/sort/sort.hh>
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

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <bit>
#include <functional>
#include <numeric>
#include <queue>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::cmp_greater;
using std::cmp_greater_equal;
using std::cmp_less;
using std::cmp_less_equal;
using std::function;
using std::greater;
using std::make_unique;
using std::move;
using std::pair;
using std::priority_queue;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

Sort::Sort(vector<IntegerVariableID> x, vector<IntegerVariableID> y) : _x(move(x)), _y(move(y))
{
}

auto Sort::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Sort>(_x, _y);
}

auto Sort::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Sort::prepare(Propagators &, State &, ProofModel * const) -> bool
{
    if (_x.size() != _y.size())
        throw InvalidProblemDefinitionException{"Sort constraint on different sized arrays"};

    return ! _x.empty();
}

auto gcs::innards::define_sortedness_proof_model(ProofModel & model, const ConstraintID & cid, const vector<IntegerVariableID> & x,
    const vector<IntegerVariableID> & y, bool arg_sort_labels) -> SortednessWitness
{
    auto n = x.size();
    SortednessWitness w;

    // ArgSort reuses this inner sortedness encoding under cake's arg_sort label
    // scheme: the non-decreasing chain is @c[id][yle<i>] (not @c[id][<i>]) and the
    // position channel is @c[id][acle/acge<i>_<j>] (not @c[id][cle/cge<i>_<j>]). The
    // before flags and rank equation are shared with standalone sort either way.
    const std::string chain_prefix = arg_sort_labels ? "yle" : "";
    const std::string channel_le = arg_sort_labels ? "acle" : "cle";
    const std::string channel_ge = arg_sort_labels ? "acge" : "cge";

    // OPB encoding matching cake_pb_cp's cencode_sort (cp_to_ilp_sortingScript.sml).
    // y is sorted(x): a non-decreasing chain over y, a proof-only stable rank pos[i]
    // per x[i] -- the number of elements before x[i] in the (value, then original
    // index) order -- and a channel placing x[i] at y[pos[i]]. Crucially pos is a
    // function of x alone, so a full assignment to x pins every pos[i] by unit
    // propagation (and a violated leaf is plain RUP). pos[i] is built as the bit-sum
    // of cake's flag bits v[id][i_b][pos], so the OPB only ever mentions those flags
    // -- no eq/ge ladder. The propagator's pos[i] == j atoms are introduced lazily
    // in the proof when it reasons over them during search; here the channel is
    // instead guarded by the bit-conjunction spelling j, exactly as cake.
    auto width = (n <= 1) ? size_t{0} : static_cast<size_t>(std::bit_width(n - 1));

    // (a) y non-decreasing: y[i] <= y[i+1], labelled @c[id][<i>] (or @c[id][yle<i>]).
    for (size_t i = 0; i + 1 < n; ++i)
        model.add_labelled_constraint(cid, chain_prefix + std::to_string(i), WPBSum{} + 1_i * y[i + 1] + -1_i * y[i] >= 0_i);

    // (b) before[ip][i] : x[ip] precedes x[i] in the (value, then original index)
    // order. The index tie-break is constant per pair, so each flag is a plain
    // comparison: ip < i ties to ip (before iff x[ip] <= x[i]); ip >= i ties to i
    // (before iff x[ip] < x[i]) -- the diagonal ip == i is then always false. Named
    // x[id][ip_i][bf] (halves @x[id][ip_i][bf][r]/[f]); cake also emits the diagonal
    // and counts it in the rank sum, so we do too.
    w.before.assign(n, std::vector<ProofFlag>(n));
    w.before_fwd.assign(n, std::vector<ProofLine>(n));
    w.before_rev.assign(n, std::vector<ProofLine>(n));
    for (size_t i = 0; i < n; ++i)
        for (size_t ip = 0; ip < n; ++ip) {
            auto bound = (ip < i) ? 0_i : -1_i;
            auto flag = model.create_proof_flag(cid, std::vector<long long>{static_cast<long long>(ip), static_cast<long long>(i)}, "bf");
            auto [fwd, rev] = model.add_two_way_reified_constraint(WPBSum{} + 1_i * x[ip] + -1_i * x[i] <= bound, flag);
            w.before[ip][i] = flag;
            w.before_fwd[ip][i] = fwd;
            w.before_rev[ip][i] = rev;
        }

    // (c) pos[i] is the stable rank, a proof-only integer in [0, n-1] whose bits are
    // named as cake's flags v[id][i_b][pos]. Naming them that way means the rank
    // equation and channel render over those flags (no fresh pos variable in the
    // OPB), and pos[i]'s eq/ge atoms are introduced in-proof on first use rather
    // than here.
    for (size_t i = 0; i < n; ++i)
        w.pos.push_back(model.create_proof_only_integer_variable(0_i, Integer(n) - 1_i, "sort_pos_" + std::to_string(i),
            IntegerVariableProofRepresentation::Bits, CakeBitNaming{cid, std::vector<long long>{static_cast<long long>(i)}, "pos", std::nullopt}));

    // (d) pos[i] = sum over ip of before[ip][i] (including the always-false
    // diagonal, as cake does). @c[id][rge<i>] is pos >= rank, @c[id][rle<i>] is
    // pos <= rank; the bound proofs pol against ge, the permutation proof needs both.
    for (size_t i = 0; i < n; ++i) {
        WPBSum rank;
        rank += 1_i * w.pos[i];
        for (size_t ip = 0; ip < n; ++ip)
            rank += -1_i * w.before[ip][i];
        auto [le, ge] = model.add_labelled_constraint(cid, "rle" + std::to_string(i), "rge" + std::to_string(i), move(rank) == 0_i);
        w.rank_ge.push_back(ge);
        w.rank_le.push_back(le);
    }

    // (e) position channel: when pos[i]'s bits spell j, x[i] sits at y[j]. Guarded
    // by the bit-conjunction spelling j (NOT pos[i] == j, so no eq atom enters the
    // OPB), split into @c[id][cle<i>_<j>] (y[j] <= x[i]) and @c[id][cge<i>_<j>]
    // (y[j] >= x[i]), matching cake.
    for (size_t i = 0; i < n; ++i)
        for (size_t j = 0; j < n; ++j) {
            HalfReifyOnConjunctionOf guard;
            for (size_t b = 0; b < width; ++b)
                guard.push_back(ProofBitVariable{w.pos[i], Integer{static_cast<long long>(b)}, ((j >> b) & 1) != 0});
            auto cell = std::to_string(i) + "_" + std::to_string(j);
            model.add_labelled_constraint(cid, channel_le + cell, WPBSum{} + 1_i * y[j] + -1_i * x[i] <= 0_i, guard);
            model.add_labelled_constraint(cid, channel_ge + cell, WPBSum{} + 1_i * y[j] + -1_i * x[i] >= 0_i, guard);
        }

    return w;
}

auto Sort::define_proof_model(ProofModel & model) -> void
{
    _witness = define_sortedness_proof_model(model, _constraint_id, _x, _y);
}

namespace
{
    // Mehlhorn-Thiel bounds-consistency propagation for Sortedness(x; y), i.e.
    // y = sort(x). Achieves bounds(Z) on both x and y (Thiel's thesis, ch. 3;
    // Mehlhorn & Thiel, CP 2000). See dev_docs/sortedness.md.
    //
    // PROOF LOGGING IS FULLY HONEST (see dev_docs/sortedness.md) -- no asserts.
    // Every inference is certified: the y-upper/y-lower bounds (normalization,
    // order-statistic and Hall cases), the x-bounds (intersection and Hall
    // cases), and the no-matching contradiction (pure y-window and matching/Hall
    // cases). The backbone is the root permutation (totality, antisymmetry,
    // transitivity, rank gaps, recover_am1 injectivity, surjectivity) plus a
    // single Hall pigeonhole over the rank line (find_band), applied
    // unconditionally for the contradiction and under the negated-goal
    // assumption for the bounds. find_band is an invariant: whenever the
    // propagator makes an inference there must be a violator, so a missing one
    // throws UnexpectedException (never triggered over the full test suite +
    // a 200-seed random sweep) rather than silently weakening the proof.
    template <typename Inference_>
    auto propagate_sortedness(const vector<IntegerVariableID> & x, const vector<IntegerVariableID> & y, const vector<vector<ProofFlag>> & before,
        const vector<ProofOnlySimpleIntegerVariableID> & pos, const vector<ProofLine> & rank_lines, const vector<ProofLine> & rank_le_lines,
        const vector<ProofLine> & inj_lines, const vector<ProofLine> & al1_lines, const vector<vector<ProofLine>> & anti_lines,
        const ConstraintID & owner, const State & state, Inference_ & inference, ProofLogger * const logger, const Reason & reason) -> void
    {
        auto n = x.size();

        // Snapshot bounds. ox/oy are the originals (to decide what actually
        // tightened); lx/ux/ly/uy are working copies the algorithm narrows.
        vector<long long> lx(n), ux(n), oly(n), ouy(n), ly(n), uy(n), olx(n), oux(n);
        for (size_t i = 0; i < n; ++i) {
            auto [lo, hi] = state.bounds(x[i]);
            lx[i] = olx[i] = lo.raw_value;
            ux[i] = oux[i] = hi.raw_value;
        }
        for (size_t j = 0; j < n; ++j) {
            auto [lo, hi] = state.bounds(y[j]);
            ly[j] = oly[j] = lo.raw_value;
            uy[j] = ouy[j] = hi.raw_value;
        }

        // (1) Normalize the y-ranges: they index the sorted output, so the lower
        // bounds are non-decreasing and the upper bounds non-decreasing.
        for (size_t j = 1; j < n; ++j)
            ly[j] = std::max(ly[j], ly[j - 1]);
        for (size_t j = n - 1; j-- > 0;)
            uy[j] = std::min(uy[j], uy[j + 1]);
        for (size_t j = 0; j < n; ++j)
            if (ly[j] > uy[j]) {
                // The y-windows alone are infeasible: some k1 <= j has
                // oly[k1] = ly[j] and some k2 >= j has ouy[k2] = uy[j], with
                // oly[k1] > ouy[k2]. Then y[k1] >= oly[k1] > ouy[k2] >= y[k2],
                // yet k1 <= k2 forces y[k1] <= y[k2] -- a pure sortedness
                // contradiction (no x, no permutation). Emit the down-chain of
                // monotonicity clauses (y[m] <= V) v (y[m+1] > V) at V = ouy[k2]
                // (each RUP from y[m] <= y[m+1]); the closing RUP walks y[k2] <= V
                // down to y[k1] <= V, contradicting y[k1] >= oly[k1] > V.
                size_t k1 = 0, k2 = j;
                for (size_t k = 0; k <= j; ++k)
                    if (oly[k] == ly[j]) {
                        k1 = k;
                        break;
                    }
                for (size_t k = j; k < n; ++k)
                    if (ouy[k] == uy[j]) {
                        k2 = k;
                        break;
                    }
                inference.contradiction(logger,
                    JustifyExplicitly{//
                        [&y, k1, k2, V = uy[j], logger](const ReasonLiterals &) -> void {
                            for (size_t m = k1; m < k2; ++m)
                                logger->emit(RUPProofRule{}, WPBSum{} + 1_i * (y[m] < Integer{V + 1}) + 1_i * (y[m + 1] >= Integer{V + 1}) >= 1_i,
                                    ProofLevel::Temporary);
                        },
                        ThenRUP::Yes, hints::Sort{owner}},
                    reason);
            }

        // Feasible-rank interval [lo_i, hi_i) of each x_i: ranks whose y-window
        // (after normalization) its value-interval can meet. lo_i = smallest j
        // with uy[j] >= lx[i]; hi_i = smallest j with ly[j] > ux[i] (exclusive).
        // Computed here (not just in step 5) because the no-matching
        // contradiction below needs them.
        vector<size_t> lo_i(n), hi_i(n);
        for (size_t i = 0; i < n; ++i) {
            lo_i[i] = static_cast<size_t>(std::lower_bound(uy.begin(), uy.end(), lx[i]) - uy.begin());
            hi_i[i] = static_cast<size_t>(std::upper_bound(ly.begin(), ly.end(), ux[i]) - ly.begin());
        }

        // No perfect matching => a Hall violator on the rank line: an interval
        // [a,b] of ranks containing > b-a+1 x's whose whole feasible-rank
        // interval [lo_i,hi_i) sits inside [a,b]. By interval convexity such a
        // tight set exists whenever the matching fails. The certificate is the
        // all_different-style pigeonhole, with ranks as the slots: each i in the
        // violator is pinned to a rank in [a,b] (exclude every outside rank k via
        // the channel + a normalized y-bound), and the root injectivity lines
        // cap [a,b] at b-a+1 occupants -- contradiction.
        // Scan for a Hall violator on the rank line given effective feasible-rank
        // intervals [lo[i], hi[i]): a tightest interval [a,b] with > b-a+1 x's
        // wholly contained. Returns (S, a, b); S empty if none.
        auto find_band = [n](const vector<size_t> & lo, const vector<size_t> & hi) -> std::tuple<vector<size_t>, long long, long long> {
            for (long long a = 0; cmp_less_equal(a, n); ++a)
                for (long long b = a - 1; cmp_less(b, n); ++b) {
                    vector<size_t> cand;
                    for (size_t i = 0; i < n; ++i)
                        if (cmp_greater_equal(lo[i], a) && cmp_less_equal(hi[i], b + 1))
                            cand.push_back(i);
                    if (cmp_greater(cand.size(), b - a + 1))
                        return {move(cand), a, b};
                }
            return {{}, 0, -1};
        };

        auto fail_hall = [&]() -> void {
            auto [S, fa, fb] = find_band(lo_i, hi_i);
            if (S.empty())
                throw UnexpectedException{"Sort: no Hall violator for an infeasible matching"};

            inference.contradiction(logger,
                JustifyExplicitly{//
                    [&, S, fa, fb](const ReasonLiterals & reason_lits) -> void {
                        // Normalized y-bound lemmas as RUP chains: NUY[k] : y_k <= uy[k]
                        // (top-down, from y_k <= y_{k+1} <= uy[k+1] and y_k <= ouy[k]);
                        // NLY[k] : y_k >= ly[k] (bottom-up). These let each rank
                        // exclusion be a single-step RUP.
                        for (size_t k = n; k-- > 0;)
                            logger->emit_rup_proof_line_under_reason(reason_lits, WPBSum{} + 1_i * y[k] <= Integer{uy[k]}, ProofLevel::Temporary);
                        for (size_t k = 0; k < n; ++k)
                            logger->emit_rup_proof_line_under_reason(reason_lits, WPBSum{} + 1_i * y[k] >= Integer{ly[k]}, ProofLevel::Temporary);
                        // Per i in S: pin pos[i] into [fa,fb] by excluding every
                        // outside rank k (k < fa <= lo_i: y_k <= uy[k] < lx[i] breaks
                        // the channel; k > fb >= hi_i-1: y_k >= ly[k] > ux[i]). The
                        // restricted at-least-one then follows from the root al1[i].
                        vector<ProofLine> restricted(S.size());
                        for (const auto & [idx, i] : enumerate(S)) {
                            for (long long k = 0; cmp_less(k, n); ++k)
                                if (k < fa || k > fb)
                                    logger->emit_rup_proof_line_under_reason(
                                        reason_lits, WPBSum{} + 1_i * (pos[i] != Integer{k}) >= 1_i, ProofLevel::Temporary);
                            WPBSum in_band;
                            for (long long k = fa; k <= fb; ++k)
                                in_band += 1_i * (pos[i] == Integer{k});
                            restricted[idx] = logger->emit_rup_proof_line_under_reason(reason_lits, move(in_band) >= 1_i, ProofLevel::Temporary);
                        }
                        // Pigeonhole: |S| pins into [fa,fb] but injectivity caps it at
                        // fb-fa+1 < |S|. (For an empty band the restricted lines are
                        // already 0 >= 1 and the closing RUP suffices.)
                        if (fb >= fa) {
                            PolBuilder pol;
                            for (auto l : restricted)
                                pol.add(l);
                            for (long long k = fa; k <= fb; ++k)
                                pol.add(inj_lines[static_cast<size_t>(k)]);
                            pol.emit(*logger, ProofLevel::Temporary);
                        }
                    },
                    ThenRUP::Yes, hints::Sort{owner}},
                reason);
        };

        // (2) Down-sweep: Glover matching of y_j to the available x with the
        // smallest upper bound (gives feasibility and the y upper bounds).
        vector<size_t> by_lx(n);
        std::iota(by_lx.begin(), by_lx.end(), size_t{0});
        std::sort(by_lx.begin(), by_lx.end(), [&](size_t a, size_t b) { return lx[a] < lx[b]; });
        vector<size_t> phi(n);
        {
            priority_queue<pair<long long, size_t>, vector<pair<long long, size_t>>, greater<>> pq;
            size_t s = 0;
            for (size_t j = 0; j < n; ++j) {
                while (s < n && lx[by_lx[s]] <= uy[j]) {
                    pq.push({ux[by_lx[s]], by_lx[s]});
                    ++s;
                }
                if (pq.empty())
                    fail_hall();
                auto [ub_i, i] = pq.top();
                pq.pop();
                if (ub_i < ly[j])
                    fail_hall();
                phi[j] = i;
            }
        }

        // (3) Up-sweep: the mirror image, matching y_j to the available x with
        // the largest lower bound (gives the y lower bounds).
        vector<size_t> by_ux(n);
        std::iota(by_ux.begin(), by_ux.end(), size_t{0});
        std::sort(by_ux.begin(), by_ux.end(), [&](size_t a, size_t b) { return ux[a] > ux[b]; });
        vector<size_t> phi2(n);
        {
            priority_queue<pair<long long, size_t>> pq;
            size_t s = 0;
            for (size_t k = 0; k < n; ++k) {
                size_t j = n - 1 - k;
                while (s < n && ux[by_ux[s]] >= ly[j]) {
                    pq.push({lx[by_ux[s]], by_ux[s]});
                    ++s;
                }
                if (pq.empty())
                    fail_hall();
                auto [lb_i, i] = pq.top();
                pq.pop();
                if (lb_i > uy[j])
                    fail_hall();
                phi2[j] = i;
            }
        }

        // (4) Tightened y-bounds.
        vector<long long> nly(n), nuy(n);
        for (size_t j = 0; j < n; ++j) {
            nuy[j] = std::min(ux[phi[j]], uy[j]);
            nly[j] = std::max(lx[phi2[j]], ly[j]);
        }

        // (5) Tightened x-bounds, via the strongly connected components of the
        // oriented intersection graph (an edge {x_i, y_j} lies in some perfect
        // matching iff x_i and y_j share an SCC; Regin's characterization). Node
        // i = x_i, node n+j = y_j. Edges: x_i -> y_j for every intersecting pair
        // (neighbours of x_i are the contiguous y-index interval [lo_i, hi_i]),
        // and y_j -> x_phi[j] for the matching. Plain recursive Tarjan over the
        // implicit interval adjacency: this computes the correct SCCs (and hence
        // full bounds consistency on x, see step below) in O(n^2), not yet the
        // linear-time Algorithm 3.2 from the thesis. (lo_i / hi_i were computed
        // after normalization, above.)

        auto N = 2 * n;
        vector<long long> index(N, -1), lowlink(N, 0);
        vector<char> on_stack(N, 0);
        vector<long long> comp(N, -1);
        vector<size_t> tarjan_stack;
        long long next_index = 0, next_comp = 0;

        function<void(size_t)> strong_connect = [&](size_t v) {
            index[v] = lowlink[v] = next_index++;
            tarjan_stack.push_back(v);
            on_stack[v] = 1;

            auto visit = [&](size_t w) {
                if (index[w] == -1) {
                    strong_connect(w);
                    lowlink[v] = std::min(lowlink[v], lowlink[w]);
                }
                else if (on_stack[w])
                    lowlink[v] = std::min(lowlink[v], index[w]);
            };

            if (v < n) {
                for (size_t j = lo_i[v]; j < hi_i[v]; ++j)
                    visit(n + j);
            }
            else {
                visit(phi[v - n]);
            }

            if (lowlink[v] == index[v]) {
                while (true) {
                    auto w = tarjan_stack.back();
                    tarjan_stack.pop_back();
                    on_stack[w] = 0;
                    comp[w] = next_comp;
                    if (w == v)
                        break;
                }
                ++next_comp;
            }
        };
        for (size_t v = 0; v < N; ++v)
            if (index[v] == -1)
                strong_connect(v);

        // x-bounds in the *reduced* intersection graph: an edge {x_i, y_j} lies
        // in some perfect matching iff x_i and y_j share an SCC. For x_i, the
        // tightened range is governed by its smallest/largest neighbour *within
        // its own SCC* -- NOT the SCC's whole y-span. (Using the whole span is
        // wrong: a y-node can be in the SCC via other nodes while not being a
        // neighbour of x_i, e.g. x_i = [2,4] and y = [1,1] do not intersect yet
        // both sit in one SCC; counting y would loosen lb(x_i) spuriously.)
        // x_i's neighbours are the contiguous y-index interval [lo_i, hi_i); the
        // matched edge guarantees at least one of them is in x_i's SCC.
        vector<long long> nlx(n), nux(n);
        // jl_in[i] / jh_in[i] are x_i's smallest / largest neighbour within its
        // SCC. The proof of the x-bounds is honest exactly when these coincide
        // with the *intersection* extremes lo_i / hi_i-1 (the bound is then the
        // plain "x_i can't sit below/above this position" fact); when the SCC
        // strictly tightens them, it is a Hall argument, still asserted.
        vector<size_t> jl_in(n), jh_in(n);
        for (size_t i = 0; i < n; ++i) {
            auto c = comp[i];
            size_t jl = n, jh = 0;
            bool found = false;
            for (size_t j = lo_i[i]; j < hi_i[i]; ++j)
                if (comp[n + j] == c) {
                    if (! found) {
                        jl = j;
                        found = true;
                    }
                    jh = j;
                }
            jl_in[i] = jl;
            jh_in[i] = jh;
            nlx[i] = std::max(lx[i], ly[jl]);
            nux[i] = std::min(ux[i], uy[jh]);
        }

        // (6) Emit every bound that actually tightened.
        //
        // y-bounds: STAGE 1 of the proof (see dev_docs/sortedness.md). We assert
        // the count lemma -- "at least j+1 of the y's are <= U" (the Hall /
        // multiset content, P2+P3, still cheated) -- and let the closing RUP
        // discharge y[j] <= U from it honestly via y-sortedness (P1). With the
        // count line in the database, the closing RUP negates the goal
        // (y[j] >= U+1), unit-propagates up the sortedness chain to force every
        // y[k>=j] >= U+1, which zeroes those count terms and leaves <= j terms
        // forced to sum to >= j+1 -- a contradiction. The lower bound is the
        // mirror image.
        for (size_t j = 0; j < n; ++j) {
            if (nly[j] > oly[j]) {
                auto L = nly[j];
                // The mirror image of the ub(y[j]) proof. (a) NORMALIZATION: the
                // bound is the normalised ly[j] (left-to-right max of step 1,
                // >= lx[phi2[j]]), so y[j] >= L is pure y-sortedness from an
                // earlier y's lower bound. (b) ORDER STATISTIC: >= n-j of the x's
                // are forced >= L (lx_i >= L), so the (j+1)-th smallest is >= L.
                // (c) HALL: still asserted (the count line only).
                bool from_normalization = (ly[j] > oly[j]) && (ly[j] >= lx[phi2[j]]);
                size_t forced_above = 0;
                for (size_t i = 0; i < n; ++i)
                    if (olx[i] >= L)
                        ++forced_above;
                if (from_normalization) {
                    // y[j] >= L from an earlier position's lower bound: emit the
                    // monotonicity clauses (y[k] >= L) v (y[k-1] < L), each RUP
                    // from the sortedness constraint y[k-1] <= y[k]; the closing
                    // RUP walks the chain down to the witnessing earlier position.
                    inference.infer_greater_than_or_equal(logger, y[j], Integer{L},
                        JustifyExplicitly{//
                            [&y, j, L, logger](const ReasonLiterals &) -> void {
                                for (size_t k = 1; k <= j; ++k)
                                    logger->emit(RUPProofRule{}, WPBSum{} + 1_i * (y[k] >= Integer{L}) + 1_i * (y[k - 1] < Integer{L}) >= 1_i,
                                        ProofLevel::Temporary);
                            },
                            ThenRUP::Yes, hints::Sort{owner}},
                        reason);
                }
                else if (forced_above >= n - j) {
                    inference.infer_greater_than_or_equal(logger, y[j], Integer{L},
                        JustifyExplicitly{
                            [&x, &y, &before, &pos, &rank_le_lines, &anti_lines, &inj_lines, &al1_lines, n, j, L, logger](
                                const ReasonLiterals & reason_lits) -> void {
                                // PIVOT' (mirror): (x_i >= L) v (x_m < L) v before[i][m],
                                // RUP from before[i][m]'s reverse half and the constant
                                // threshold L (x_i < L <= x_m forces i before m).
                                std::vector<std::vector<ProofLine>> pivot(n, std::vector<ProofLine>(n));
                                for (size_t i = 0; i < n; ++i)
                                    for (size_t m = 0; m < n; ++m) {
                                        if (m == i)
                                            continue;
                                        pivot[i][m] = logger->emit(RUPProofRule{},
                                            WPBSum{} + 1_i * (x[i] >= Integer{L}) + 1_i * (x[m] < Integer{L}) + 1_i * before[i][m] >= 1_i,
                                            ProofLevel::Temporary);
                                    }
                                // BND[i][m] : before[m][i] <= [x_i>=L] + [x_m<L], from
                                // pivot'[i][m] + antisymmetry (flip the "out" flag
                                // before[i][m] to the "in" flag before[m][i]).
                                // RANKUB_i = rank_le[i] + sum_m BND[i][m] :
                                //   pos[i] <= (n-1)[x_i>=L] + sum_{m!=i}[x_m<L].
                                std::vector<ProofLine> rankub(n);
                                for (size_t i = 0; i < n; ++i) {
                                    PolBuilder pol;
                                    pol.add(rank_le_lines[i]);
                                    for (size_t m = 0; m < n; ++m)
                                        if (m != i)
                                            pol.add(PolBuilder{}.add(pivot[i][m]).add(anti_lines[i][m]).emit(*logger, ProofLevel::Temporary));
                                    rankub[i] = pol.emit(*logger, ProofLevel::Temporary);
                                }
                                // count_L : at most j of the x's are < L (i.e. >= n-j
                                // are >= L), RUP under the reason -- the >= n-j indices
                                // with lb(x_k) >= L have (x_k >= L) forced by their
                                // lower bound.
                                WPBSum xcount;
                                for (size_t k = 0; k < n; ++k)
                                    xcount += 1_i * (x[k] < Integer{L});
                                auto xcount_line = logger->emit_rup_proof_line_under_reason(
                                    reason_lits, move(xcount) <= Integer{static_cast<long long>(j)}, ProofLevel::Temporary);
                                // RANKUB2_i : pos[i] <= n[x_i>=L] + j-1 (fold count_L in,
                                // cross-constraint sum so a pol not RUP).
                                for (size_t i = 0; i < n; ++i)
                                    PolBuilder{}.add(rankub[i]).add(xcount_line).emit(*logger, ProofLevel::Temporary);
                                // per i : (pos[i] != j) v (y[j] >= L). RUP under reason
                                // from RANKUB2_i + channel: pos[i]=j forces [x_i>=L]=1,
                                // and the channel gives y[j] = x_i >= L.
                                for (size_t i = 0; i < n; ++i)
                                    logger->emit_rup_proof_line_under_reason(reason_lits,
                                        WPBSum{} + 1_i * (pos[i] != Integer(j)) + 1_i * (y[j] >= Integer{L}) >= 1_i, ProofLevel::Temporary);
                                // surjectivity (same counting pol as the upper bound).
                                PolBuilder surj;
                                for (size_t i = 0; i < n; ++i)
                                    surj.add(al1_lines[i]);
                                for (size_t k = 0; k < n; ++k)
                                    if (k != j)
                                        surj.add(inj_lines[k]);
                                surj.emit(*logger, ProofLevel::Temporary);
                            },
                            ThenRUP::Yes, hints::Sort{owner}},
                        reason);
                }
                else {
                    // HALL (mirror of the ub case): lb(y[j]) = lx[phi2[j]] but
                    // fewer than n-j x's are individually forced >= L. Refute
                    // y[j] <= L-1: every rank <= j then needs value <= L-1, so
                    // each x with lx >= L is confined to ranks > j (lo'[i] =
                    // max(lo_i, j+1)); find_band over (lo', hi_i) yields a Hall
                    // violator. The goal literal (y[j] >= L) is ORed into each
                    // assumption-dependent clause.
                    vector<size_t> lop(n);
                    for (size_t i = 0; i < n; ++i)
                        lop[i] = (lx[i] >= L) ? std::max(lo_i[i], static_cast<size_t>(j) + 1) : lo_i[i];
                    auto [S, fa, fb] = find_band(lop, hi_i);
                    if (S.empty())
                        throw UnexpectedException{"Sort: no Hall band for a valid lb(y) tightening"};
                    else
                        inference.infer_greater_than_or_equal(logger, y[j], Integer{L},
                            JustifyExplicitly{//
                                [&y, &pos, &lo_i, &hi_i, &ly, &uy, &inj_lines, S, fa, fb, n, j, L, logger](
                                    const ReasonLiterals & reason_lits) -> void {
                                    for (size_t k = n; k-- > 0;)
                                        logger->emit_rup_proof_line_under_reason(
                                            reason_lits, WPBSum{} + 1_i * y[k] <= Integer{uy[k]}, ProofLevel::Temporary);
                                    for (size_t k = 0; k < n; ++k)
                                        logger->emit_rup_proof_line_under_reason(
                                            reason_lits, WPBSum{} + 1_i * y[k] >= Integer{ly[k]}, ProofLevel::Temporary);
                                    // BNUY[k], k <= j : (y[j] >= L) v (y[k] <= L-1),
                                    // chain down from j (RUP from sortedness + prev).
                                    for (size_t k = j + 1; k-- > 0;)
                                        logger->emit(RUPProofRule{}, WPBSum{} + 1_i * (y[j] >= Integer{L}) + 1_i * (y[k] < Integer{L}) >= 1_i,
                                            ProofLevel::Temporary);
                                    std::vector<ProofLine> restricted(S.size());
                                    for (const auto & [idx, i] : enumerate(S)) {
                                        for (long long k = 0; cmp_less(k, n); ++k) {
                                            if (k >= fa && k <= fb)
                                                continue;
                                            if (cmp_less(k, lo_i[i]) || cmp_greater_equal(k, hi_i[i]))
                                                logger->emit_rup_proof_line_under_reason(
                                                    reason_lits, WPBSum{} + 1_i * (pos[i] != Integer{k}) >= 1_i, ProofLevel::Temporary);
                                            else
                                                logger->emit_rup_proof_line_under_reason(reason_lits,
                                                    WPBSum{} + 1_i * (y[j] >= Integer{L}) + 1_i * (pos[i] != Integer{k}) >= 1_i,
                                                    ProofLevel::Temporary);
                                        }
                                        WPBSum in_band;
                                        in_band += 1_i * (y[j] >= Integer{L});
                                        for (long long k = fa; k <= fb; ++k)
                                            in_band += 1_i * (pos[i] == Integer{k});
                                        restricted[idx] =
                                            logger->emit_rup_proof_line_under_reason(reason_lits, move(in_band) >= 1_i, ProofLevel::Temporary);
                                    }
                                    PolBuilder pol;
                                    for (auto l : restricted)
                                        pol.add(l);
                                    for (long long k = fa; k <= fb; ++k)
                                        pol.add(inj_lines[static_cast<size_t>(k)]);
                                    pol.emit(*logger, ProofLevel::Temporary);
                                },
                                ThenRUP::Yes, hints::Sort{owner}},
                            reason);
                }
            }
            if (nuy[j] < ouy[j]) {
                auto U = nuy[j];
                // Three reasons can bind ub(y[j]) = U; the honest proof differs.
                // (a) NORMALIZATION: the bound is the normalised y-side value
                //     uy[j] (the right-to-left min of step 1, <= ux[phi[j]]), so
                //     y[j] <= U follows from y-sortedness and a later y's upper
                //     bound alone. (b) ORDER STATISTIC: the bound is the matched
                //     x's upper bound ux[phi[j]], and at least j+1 of the x's are
                //     *unconditionally* forced <= U (their own upper bound is
                //     <= U); then the (j+1)-th smallest value is <= U. (c) HALL:
                //     the bound is ux[phi[j]] but fewer than j+1 x's are forced
                //     <= U -- the tightening is a genuine matching/Hall argument
                //     (some x is committed to a lower position by the y-domains),
                //     not yet certified. (a) and (b) are honest below; (c) is
                //     still asserted (see dev_docs/sortedness.md).
                bool from_normalization = (uy[j] < ouy[j]) && (uy[j] <= ux[phi[j]]);
                size_t forced_below = 0;
                for (size_t i = 0; i < n; ++i)
                    if (oux[i] <= U)
                        ++forced_below;
                if (from_normalization) {
                    // NORMALIZATION: ub(y[j]) = U = uy[j] was forced by a later y's
                    // upper bound through sortedness (the step-1 right-to-left min).
                    // Emit the monotonicity clauses (y[k] <= U) v (y[k+1] > U), each
                    // RUP from the single sortedness constraint y[k] <= y[k+1]. The
                    // closing RUP negates the goal (y[j] > U) and walks the chain up
                    // to the witnessing later position (whose ub <= U is in the
                    // reason), reaching a contradiction.
                    inference.infer_less_than(logger, y[j], Integer{U + 1},
                        JustifyExplicitly{//
                            [&y, n, j, U, logger](const ReasonLiterals &) -> void {
                                for (size_t k = j; k + 1 < n; ++k)
                                    logger->emit(RUPProofRule{}, WPBSum{} + 1_i * (y[k] < Integer{U + 1}) + 1_i * (y[k + 1] >= Integer{U + 1}) >= 1_i,
                                        ProofLevel::Temporary);
                            },
                            ThenRUP::Yes, hints::Sort{owner}},
                        reason);
                }
                else if (forced_below >= j + 1) {
                    // ORDER STATISTIC: ub(y[j]) = ux[phi[j]] and at least j+1 x's
                    // are unconditionally forced <= U. The rank lower bounds, the
                    // per-position extended-reason lines, and (via the root
                    // permutation lines) surjectivity give y[j] <= U; the count
                    // line "count_U >= j+1" is plain RUP under the reason.
                    inference.infer_less_than(logger, y[j], Integer{U + 1},
                        JustifyExplicitly{//
                            [&x, &y, &before, &pos, &rank_lines, &inj_lines, &al1_lines, n, j, U, logger](
                                const ReasonLiterals & reason_lits) -> void {
                                // PIVOT BRIDGE (honest, transitivity-free). For each i, m the
                                // clause (x_m > U) v (x_i <= U) v before[m][i] is RUP from
                                // before[m][i]'s reverse half and the bound on the constant
                                // threshold U -- comparisons go through U, never a middle
                                // variable, so it is O(1) per pair (no transitivity).
                                std::vector<std::vector<ProofLine>> clause_line(n, std::vector<ProofLine>(n));
                                for (size_t i = 0; i < n; ++i)
                                    for (size_t m = 0; m < n; ++m) {
                                        if (m == i)
                                            continue;
                                        clause_line[i][m] = logger->emit(RUPProofRule{},
                                            WPBSum{} + 1_i * before[m][i] + 1_i * (x[m] >= Integer{U + 1}) + 1_i * (x[i] < Integer{U + 1}) >= 1_i,
                                            ProofLevel::Temporary);
                                    }
                                // RANKLB_i : pos[i] + n*[x_i<=U] - count_U >= 0, i.e.
                                // "x_i > U  =>  pos[i] >= count_U" (the rank line folded with
                                // the n-1 clauses).
                                std::vector<ProofLine> ranklb(n);
                                for (size_t i = 0; i < n; ++i) {
                                    PolBuilder pol;
                                    pol.add(rank_lines[i]);
                                    for (size_t m = 0; m < n; ++m)
                                        if (m != i)
                                            pol.add(clause_line[i][m]);
                                    ranklb[i] = pol.emit(*logger, ProofLevel::Temporary);
                                }
                                // count_U >= j+1: at least j+1 of the x's are <= U,
                                // RUP under the reason -- each of the >= j+1 indices
                                // with ub(x_k) <= U has (x_k <= U) forced by its upper
                                // bound (in the reason), so the sum is >= j+1; no
                                // cross-constraint step, single-shot RUP.
                                WPBSum xcount;
                                for (size_t k = 0; k < n; ++k)
                                    xcount += 1_i * (x[k] < Integer{U + 1});
                                auto xcount_line = logger->emit_rup_proof_line_under_reason(
                                    reason_lits, move(xcount) >= Integer{static_cast<long long>(j) + 1}, ProofLevel::Temporary);
                                // RANKLB2_i : pos[i] + n*[x_i<=U] >= j+1, folding count_U away
                                // with the x-count (cross-constraint sum, hence a pol not RUP).
                                // Emitted for their RUP side effect; consumed by the per-i lines
                                // below via the database, never by explicit reference.
                                for (size_t i = 0; i < n; ++i)
                                    PolBuilder{}.add(ranklb[i]).add(xcount_line).emit(*logger, ProofLevel::Temporary);
                                // HONEST (extended reason): per i, (pos[i] != j) v (y[j] <= U).
                                // RUP from RANKLB2_i + channel: negate -> pos[i]=j and
                                // y[j] >= U+1; channel gives x_i = y[j] >= U+1 so [x_i<=U]=0,
                                // and then RANKLB2_i forces pos[i] >= j+1, contradicting
                                // pos[i]=j. Emitted under the reason: RANKLB2_i carries the
                                // reason literals (it was pol'd with the reason-conditional
                                // count line), so the per-i RUP check must assume the reason
                                // true to activate it.
                                for (size_t i = 0; i < n; ++i)
                                    logger->emit_rup_proof_line_under_reason(reason_lits,
                                        WPBSum{} + 1_i * (pos[i] != Integer(j)) + 1_i * (y[j] < Integer{U + 1}) >= 1_i, ProofLevel::Temporary);
                                // HONEST (surjectivity): rank j is occupied,
                                // sum_i [pos[i] = j] >= 1. Counting pol over the
                                // root permutation lines: sum_i al1_i (each pos takes
                                // a rank) minus sum_{k != j} inj_k (each other rank
                                // used at most once) leaves rank j with >= 1 occupant
                                // -- the n(n-1) constants cancel exactly. With the
                                // per-i lines above, the closing RUP then closes:
                                // under y[j] >= U+1 each gives pos[i] != j,
                                // contradicting this.
                                PolBuilder surj;
                                for (size_t i = 0; i < n; ++i)
                                    surj.add(al1_lines[i]);
                                for (size_t k = 0; k < n; ++k)
                                    if (k != j)
                                        surj.add(inj_lines[k]);
                                surj.emit(*logger, ProofLevel::Temporary);
                            },
                            ThenRUP::Yes, hints::Sort{owner}},
                        reason);
                }
                else {
                    // HALL: ub(y[j]) = ux[phi[j]] but fewer than j+1 x's are
                    // individually forced <= U. Refute the negated goal y[j] >=
                    // U+1 with the shared Hall pigeonhole, under that assumption:
                    // bumping every rank >= j to value >= U+1 confines each x
                    // with ux <= U to ranks < j (hi'[i] = min(hi_i, j)), so a
                    // Hall violator [a,b] over the rank line exists. The goal
                    // literal (y[j] <= U) is ORed into each assumption-dependent
                    // clause and discharged by the closing RUP.
                    vector<size_t> hip(n);
                    for (size_t i = 0; i < n; ++i)
                        hip[i] = (ux[i] <= U) ? std::min(hi_i[i], static_cast<size_t>(j)) : hi_i[i];
                    auto [S, fa, fb] = find_band(lo_i, hip);
                    if (S.empty())
                        throw UnexpectedException{"Sort: no Hall band for a valid ub(y) tightening"};
                    else
                        inference.infer_less_than(logger, y[j], Integer{U + 1},
                            JustifyExplicitly{[&y, &pos, &lo_i, &hi_i, &ly, &uy, &inj_lines, S, fa, fb, n, j, U, logger](
                                                  const ReasonLiterals & reason_lits) -> void {
                                                  // Normalized y-bounds for the unconditional rank
                                                  // exclusions (k < lo_i: y_k <= uy[k] < lx_i;
                                                  // k >= hi_i: y_k >= ly[k] > ux_i).
                                                  for (size_t k = n; k-- > 0;)
                                                      logger->emit_rup_proof_line_under_reason(
                                                          reason_lits, WPBSum{} + 1_i * y[k] <= Integer{uy[k]}, ProofLevel::Temporary);
                                                  for (size_t k = 0; k < n; ++k)
                                                      logger->emit_rup_proof_line_under_reason(
                                                          reason_lits, WPBSum{} + 1_i * y[k] >= Integer{ly[k]}, ProofLevel::Temporary);
                                                  // BNLY[k], k >= j : (y[j] <= U) v (y[k] >= U+1),
                                                  // a chain up from j (each RUP from sortedness and
                                                  // the previous). Makes the assumption-dependent
                                                  // exclusions (ranks in [j, hi_i)) one-step RUPs.
                                                  for (size_t k = j; k < n; ++k)
                                                      logger->emit(RUPProofRule{},
                                                          WPBSum{} + 1_i * (y[j] < Integer{U + 1}) + 1_i * (y[k] >= Integer{U + 1}) >= 1_i,
                                                          ProofLevel::Temporary);
                                                  // Per i in S: pin pos[i] into [fa,fb].
                                                  std::vector<ProofLine> restricted(S.size());
                                                  for (const auto & [idx, i] : enumerate(S)) {
                                                      for (long long k = 0; cmp_less(k, n); ++k) {
                                                          if (k >= fa && k <= fb)
                                                              continue;
                                                          if (cmp_less(k, lo_i[i]) || cmp_greater_equal(k, hi_i[i]))
                                                              logger->emit_rup_proof_line_under_reason(
                                                                  reason_lits, WPBSum{} + 1_i * (pos[i] != Integer{k}) >= 1_i, ProofLevel::Temporary);
                                                          else
                                                              logger->emit_rup_proof_line_under_reason(reason_lits,
                                                                  WPBSum{} + 1_i * (y[j] < Integer{U + 1}) + 1_i * (pos[i] != Integer{k}) >= 1_i,
                                                                  ProofLevel::Temporary);
                                                      }
                                                      WPBSum in_band;
                                                      in_band += 1_i * (y[j] < Integer{U + 1});
                                                      for (long long k = fa; k <= fb; ++k)
                                                          in_band += 1_i * (pos[i] == Integer{k});
                                                      restricted[idx] = logger->emit_rup_proof_line_under_reason(
                                                          reason_lits, move(in_band) >= 1_i, ProofLevel::Temporary);
                                                  }
                                                  // Pigeonhole: the |S| restricted-at-least-ones
                                                  // against inj_k for k in [fa,fb] force the goal
                                                  // (the contradiction core conflicts with the
                                                  // negated goal in the closing RUP).
                                                  PolBuilder pol;
                                                  for (auto l : restricted)
                                                      pol.add(l);
                                                  for (long long k = fa; k <= fb; ++k)
                                                      pol.add(inj_lines[static_cast<size_t>(k)]);
                                                  pol.emit(*logger, ProofLevel::Temporary);
                                              },
                                ThenRUP::Yes, hints::Sort{owner}},
                            reason);
                }
            }
        }
        for (size_t i = 0; i < n; ++i) {
            if (nlx[i] > olx[i]) {
                auto L = nlx[i];
                // x[i] >= L. Honest when L is the intersection bound ly[lo_i]
                // (jl_in[i] == lo_i[i]): for every rank k, (pos[i] != k) v
                // (x_i >= L) is RUP under the reason -- k < lo_i is impossible
                // (y_k <= uy[k] < lx[i] <= x_i, so pos[i]=k would force y_k=x_i
                // above its own upper bound), and k >= lo_i gives x_i = y_k >=
                // ly[k] >= ly[lo_i] = L via the channel. The at-least-one line
                // for pos[i] then closes it. HALL (jl_in > lo_i): asserted.
                if (jl_in[i] == lo_i[i])
                    inference.infer_greater_than_or_equal(logger, x[i], Integer{L},
                        JustifyExplicitly{//
                            [&x, &pos, n, i, L, logger](const ReasonLiterals & reason_lits) -> void {
                                for (size_t k = 0; k < n; ++k)
                                    logger->emit_rup_proof_line_under_reason(reason_lits,
                                        WPBSum{} + 1_i * (pos[i] != Integer(k)) + 1_i * (x[i] >= Integer{L}) >= 1_i, ProofLevel::Temporary);
                            },
                            ThenRUP::Yes, hints::Sort{owner}},
                        reason);
                else {
                    // HALL: lb(x[i]) = ly[jl] with jl = jl_in[i] > lo_i (the SCC
                    // pushes x[i]'s rank strictly above the intersection floor).
                    // Refute x[i] <= L-1: then x[i] = y_{pos[i]} < L <= ly[k] for
                    // k >= jl, so x[i] is confined to ranks < jl (hi'[i] = jl).
                    // find_band over (lo_i, hi') gives a Hall violator containing
                    // i; only i's clauses carry the goal literal (x[i] >= L).
                    auto jl = jl_in[i];
                    vector<size_t> hip = hi_i;
                    hip[i] = jl;
                    auto [S, fa, fb] = find_band(lo_i, hip);
                    if (S.empty() || std::find(S.begin(), S.end(), i) == S.end())
                        throw UnexpectedException{"Sort: no Hall band for a valid lb(x) tightening"};
                    else
                        inference.infer_greater_than_or_equal(logger, x[i], Integer{L},
                            JustifyExplicitly{//
                                [&x, &y, &pos, &ly, &uy, &inj_lines, S, fa, fb, i, n, L, logger](const ReasonLiterals & reason_lits) -> void {
                                    for (size_t k = n; k-- > 0;)
                                        logger->emit_rup_proof_line_under_reason(
                                            reason_lits, WPBSum{} + 1_i * y[k] <= Integer{uy[k]}, ProofLevel::Temporary);
                                    for (size_t k = 0; k < n; ++k)
                                        logger->emit_rup_proof_line_under_reason(
                                            reason_lits, WPBSum{} + 1_i * y[k] >= Integer{ly[k]}, ProofLevel::Temporary);
                                    std::vector<ProofLine> restricted(S.size());
                                    for (const auto & [idx, m] : enumerate(S)) {
                                        for (long long k = 0; cmp_less(k, n); ++k) {
                                            if (k >= fa && k <= fb)
                                                continue;
                                            // i excluded from ranks > fb (>= jl) needs the
                                            // assumption (NLY: y_k >= ly[k] >= L); all other
                                            // exclusions are unconditional.
                                            if (m == i && k > fb)
                                                logger->emit_rup_proof_line_under_reason(reason_lits,
                                                    WPBSum{} + 1_i * (x[i] >= Integer{L}) + 1_i * (pos[m] != Integer{k}) >= 1_i,
                                                    ProofLevel::Temporary);
                                            else
                                                logger->emit_rup_proof_line_under_reason(
                                                    reason_lits, WPBSum{} + 1_i * (pos[m] != Integer{k}) >= 1_i, ProofLevel::Temporary);
                                        }
                                        WPBSum in_band;
                                        if (m == i)
                                            in_band += 1_i * (x[i] >= Integer{L});
                                        for (long long k = fa; k <= fb; ++k)
                                            in_band += 1_i * (pos[m] == Integer{k});
                                        restricted[idx] =
                                            logger->emit_rup_proof_line_under_reason(reason_lits, move(in_band) >= 1_i, ProofLevel::Temporary);
                                    }
                                    PolBuilder pol;
                                    for (auto l : restricted)
                                        pol.add(l);
                                    for (long long k = fa; k <= fb; ++k)
                                        pol.add(inj_lines[static_cast<size_t>(k)]);
                                    pol.emit(*logger, ProofLevel::Temporary);
                                },
                                ThenRUP::Yes, hints::Sort{owner}},
                            reason);
                }
            }
            if (nux[i] < oux[i]) {
                auto U = nux[i];
                // Mirror: x[i] <= U, honest when U is the intersection bound
                // uy[hi_i-1] (jh_in[i] == hi_i[i]-1).
                if (jh_in[i] + 1 == hi_i[i])
                    inference.infer_less_than(logger, x[i], Integer{U + 1},
                        JustifyExplicitly{//
                            [&x, &pos, n, i, U, logger](const ReasonLiterals & reason_lits) -> void {
                                for (size_t k = 0; k < n; ++k)
                                    logger->emit_rup_proof_line_under_reason(reason_lits,
                                        WPBSum{} + 1_i * (pos[i] != Integer(k)) + 1_i * (x[i] < Integer{U + 1}) >= 1_i, ProofLevel::Temporary);
                            },
                            ThenRUP::Yes, hints::Sort{owner}},
                        reason);
                else {
                    // HALL mirror: ub(x[i]) = uy[jh] with jh = jh_in[i] < hi_i-1.
                    // Refute x[i] >= U+1: then x[i] = y_{pos[i]} > U >= uy[k] for
                    // k <= jh, so x[i] is confined to ranks > jh (lo'[i] = jh+1).
                    auto jh = jh_in[i];
                    vector<size_t> lop = lo_i;
                    lop[i] = jh + 1;
                    auto [S, fa, fb] = find_band(lop, hi_i);
                    if (S.empty() || std::find(S.begin(), S.end(), i) == S.end())
                        throw UnexpectedException{"Sort: no Hall band for a valid ub(x) tightening"};
                    else
                        inference.infer_less_than(logger, x[i], Integer{U + 1},
                            JustifyExplicitly{//
                                [&x, &y, &pos, &ly, &uy, &inj_lines, S, fa, fb, i, n, U, logger](const ReasonLiterals & reason_lits) -> void {
                                    for (size_t k = n; k-- > 0;)
                                        logger->emit_rup_proof_line_under_reason(
                                            reason_lits, WPBSum{} + 1_i * y[k] <= Integer{uy[k]}, ProofLevel::Temporary);
                                    for (size_t k = 0; k < n; ++k)
                                        logger->emit_rup_proof_line_under_reason(
                                            reason_lits, WPBSum{} + 1_i * y[k] >= Integer{ly[k]}, ProofLevel::Temporary);
                                    std::vector<ProofLine> restricted(S.size());
                                    for (const auto & [idx, m] : enumerate(S)) {
                                        for (long long k = 0; cmp_less(k, n); ++k) {
                                            if (k >= fa && k <= fb)
                                                continue;
                                            // i excluded from ranks < fa (<= jh) needs the
                                            // assumption (NUY: y_k <= uy[k] <= U).
                                            if (m == i && k < fa)
                                                logger->emit_rup_proof_line_under_reason(reason_lits,
                                                    WPBSum{} + 1_i * (x[i] < Integer{U + 1}) + 1_i * (pos[m] != Integer{k}) >= 1_i,
                                                    ProofLevel::Temporary);
                                            else
                                                logger->emit_rup_proof_line_under_reason(
                                                    reason_lits, WPBSum{} + 1_i * (pos[m] != Integer{k}) >= 1_i, ProofLevel::Temporary);
                                        }
                                        WPBSum in_band;
                                        if (m == i)
                                            in_band += 1_i * (x[i] < Integer{U + 1});
                                        for (long long k = fa; k <= fb; ++k)
                                            in_band += 1_i * (pos[m] == Integer{k});
                                        restricted[idx] =
                                            logger->emit_rup_proof_line_under_reason(reason_lits, move(in_band) >= 1_i, ProofLevel::Temporary);
                                    }
                                    PolBuilder pol;
                                    for (auto l : restricted)
                                        pol.add(l);
                                    for (long long k = fa; k <= fb; ++k)
                                        pol.add(inj_lines[static_cast<size_t>(k)]);
                                    pol.emit(*logger, ProofLevel::Temporary);
                                },
                                ThenRUP::Yes, hints::Sort{owner}},
                            reason);
                }
            }
        }
    }
}

auto gcs::innards::install_sortedness_propagator(Propagators & propagators, const ConstraintID & constraint_id, const vector<IntegerVariableID> & x,
    const vector<IntegerVariableID> & y, const SortednessWitness & witness) -> void
{
    auto n = x.size();
    auto inj_lines = std::make_shared<vector<ProofLine>>();
    auto al1_lines = std::make_shared<vector<ProofLine>>();
    auto anti_lines = std::make_shared<vector<vector<ProofLine>>>(n, vector<ProofLine>(n));

    // Derive the permutation facts once at the proof root, at ProofLevel::Top so
    // they persist across the whole search, and reuse them in every bound
    // justification (the Cumulative/Disjunctive bridge pattern). The chain:
    //   totality      before[a][b] + before[b][a] >= 1      (order is total)
    //   antisymmetry  !before[a][b] + !before[b][a] >= 1     (at most one way)
    //   transitivity  before[i][i'] & before[k][i] -> before[k][i']
    //   rank gap      before[i][i']  ->  pos[i'] >= pos[i] + 1
    // The gap lines make the pairwise rank-distinctness clauses RUP, which
    // recover_am1 folds into per-value injectivity (built in the next step).
    propagators.install_initialiser(
        [n, before = witness.before, before_fwd = witness.before_fwd, before_rev = witness.before_rev, rank_ge = witness.rank_ge,
            rank_le = witness.rank_le, pos = witness.pos, inj_lines, al1_lines, anti_lines](State &, auto &, ProofLogger * const logger) -> void {
            if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
                return;

            // Totality + antisymmetry. The reverse (resp. forward) halves of the
            // two directed flags have opposite x-coefficients, so summing them
            // cancels the x terms and leaves a pure two-flag clause; saturate()
            // clamps the (big-M) flag coefficients down to the degree 1.
            std::vector<std::vector<ProofLine>> tot(n, std::vector<ProofLine>(n));
            for (size_t a = 0; a < n; ++a)
                for (size_t b = a + 1; b < n; ++b) {
                    tot[a][b] = tot[b][a] = PolBuilder{}.add(before_rev[a][b]).add(before_rev[b][a]).saturate().emit(*logger, ProofLevel::Top);
                    (*anti_lines)[a][b] = (*anti_lines)[b][a] =
                        PolBuilder{}.add(before_fwd[a][b]).add(before_fwd[b][a]).saturate().emit(*logger, ProofLevel::Top);
                }

            // Rank-gap lines. For each ordered pair (i, i'):
            //   GAP[i][i'] : pos[i'] - pos[i] + n*before[i'][i] >= 1
            // i.e. "before[i][i'] => pos[i'] >= pos[i] + 1". Built as the pol
            //   rank_ge[i'] + rank_le[i] + sum_{k != i,i'} T[k] + (n-1)*TOT[i][i']
            // where T[k] is the (degree-1) transitivity clause
            //   !before[k][i] + !before[i][i'] + before[k][i'] >= 1.
            // The GAP sum is exact -- the before-sum and before[i][i'] terms
            // cancel, leaving exactly n*before[i'][i] with RHS 1 -- so T[k] must
            // be a clean coefficient-1 clause and GAP must NOT be saturated.
            for (size_t i = 0; i < n; ++i)
                for (size_t ip = 0; ip < n; ++ip) {
                    if (ip == i)
                        continue;
                    PolBuilder gap;
                    gap.add(rank_ge[ip]).add(rank_le[i]);
                    for (size_t k = 0; k < n; ++k) {
                        if (k == i || k == ip)
                            continue;
                        // L = fwd(before[k][i]) + fwd(before[i][i']) +
                        // rev(before[k][i']): the x terms cancel, leaving a
                        // flags-only constraint (M..*flags >= s+1, where the
                        // tiebreak slack s = bound_ki' - bound_ki - bound_ii' >= 0
                        // can exceed 0, so the big-M coefficients do NOT saturate
                        // uniformly to 1). The clause T[k] is then RUP from L --
                        // setting before[k][i]=before[i][i']=1, before[k][i']=0
                        // zeroes L's LHS, falsifying L >= s+1 >= 1 -- which gives
                        // a clean coefficient-1 clause regardless of the M's.
                        PolBuilder{}.add(before_fwd[k][i]).add(before_fwd[i][ip]).add(before_rev[k][ip]).emit(*logger, ProofLevel::Top);
                        auto tk = logger->emit_rup_proof_line(
                            WPBSum{} + 1_i * ! before[k][i] + 1_i * ! before[i][ip] + 1_i * before[k][ip] >= 1_i, ProofLevel::Top);
                        gap.add(tk);
                    }
                    gap.add(tot[i][ip], Integer{static_cast<long long>(n) - 1});
                    gap.emit(*logger, ProofLevel::Top);
                }

            // Per-position at-least-one: pos[i] takes some rank in [0, n-1].
            // RUP from pos[i]'s bit encoding (like the framework's own AL1 for
            // real variables, but pos is proof-only so we emit it ourselves).
            al1_lines->clear();
            for (size_t i = 0; i < n; ++i) {
                WPBSum al1;
                for (size_t k = 0; k < n; ++k)
                    al1 += 1_i * (pos[i] == Integer(k));
                al1_lines->push_back(logger->emit_rup_proof_line(move(al1) >= 1_i, ProofLevel::Top));
            }

            // Per-rank injectivity: at most one position has rank k, i.e.
            // sum_i [pos[i] = k] <= 1. This is recover_am1's pairwise->global
            // fold (the layer/multiply/divide pol from all_different's
            // justify.cc), done inline because pos is proof-only and so the
            // shared recover_am1 template isn't instantiated for its condition
            // type. Each pairwise distinctness clause
            //   !(pos[i]=k) + !(pos[i']=k) >= 1
            // is RUP from the two GAP lines and the antisymmetry clause: if both
            // had rank k, the GAPs force both directed before-flags, which
            // antisymmetry forbids.
            inj_lines->clear();
            for (size_t k = 0; n >= 2 && k < n; ++k) {
                PolBuilder am1;
                long long layer = 0;
                for (size_t i = 1; i < n; ++i) {
                    if (++layer >= 2)
                        am1.multiply_by(Integer{layer});
                    for (size_t ip = 0; ip < i; ++ip) {
                        auto ne = logger->emit_rup_proof_line(
                            WPBSum{} + 1_i * (pos[i] != Integer(k)) + 1_i * (pos[ip] != Integer(k)) >= 1_i, ProofLevel::Temporary);
                        am1.add(ne);
                    }
                    am1.divide_by(Integer{layer + 1});
                }
                inj_lines->push_back(am1.emit(*logger, ProofLevel::Top));
            }
        },
        InitialiserPriority::Expensive);

    Triggers triggers;
    triggers.on_bounds.insert(triggers.on_bounds.end(), x.begin(), x.end());
    triggers.on_bounds.insert(triggers.on_bounds.end(), y.begin(), y.end());

    // Whole-scope bounds reason built once and captured, not rebuilt per wake
    // (see dev_docs/propagator-performance.md).
    vector<IntegerVariableID> all_vars = x;
    all_vars.insert(all_vars.end(), y.begin(), y.end());
    auto sort_reason = bounds_reason(all_vars);

    propagators.install(
        constraint_id,
        [x, y, before = witness.before, pos = witness.pos, rank_lines = witness.rank_ge, rank_le_lines = witness.rank_le, inj_lines, al1_lines,
            anti_lines, owner = constraint_id,
            reason = std::move(sort_reason)](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            propagate_sortedness(
                x, y, before, pos, rank_lines, rank_le_lines, *inj_lines, *al1_lines, *anti_lines, owner, state, inference, logger, reason);
            return PropagatorState::Enable;
        },
        triggers);
}

auto Sort::install_propagators(Propagators & propagators) -> void
{
    install_sortedness_propagator(propagators, constraint_id(), _x, _y, _witness);
}

auto Sort::constraint_type() const -> std::string
{
    return "sort";
}

auto Sort::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    vector<SExpr> xs;
    for (const auto & v : _x)
        xs.push_back(tracker.s_expr_term_of(v));

    vector<SExpr> ys;
    for (const auto & v : _y)
        ys.push_back(tracker.s_expr_term_of(v));

    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(move(xs)), SExpr::list(move(ys))});
}
