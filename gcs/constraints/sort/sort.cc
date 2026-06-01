#include <gcs/constraints/sort/sort.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <functional>
#include <numeric>
#include <queue>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

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

Sort::Sort(vector<IntegerVariableID> x, vector<IntegerVariableID> y) :
    _x(move(x)),
    _y(move(y))
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

auto Sort::define_proof_model(ProofModel & model) -> void
{
    auto n = _x.size();

    // Compact, domain-width-independent encoding. The witness is a proof-only
    // permutation pos[i] giving the position x[i] is sent to in y, with the
    // channel y[pos[i]] = x[i]. Crucially pos is defined as the *stable rank*
    // of x[i] -- a function of x alone -- so a full assignment to x (and hence
    // y, via the channel) determines every pos[i] by unit propagation, which
    // is what lets VeriPB verify solutions. It also makes a violated leaf plain
    // RUP: the channel pins y to sorted(x), so any other y is refuted directly.

    // y is sorted into non-decreasing order (the defining property; also
    // implied by the channel once pos is pinned).
    for (size_t i = 0; i + 1 < _y.size(); ++i)
        model.add_constraint("Sort", "y non-decreasing",
            WPBSum{} + 1_i * _y[i] + -1_i * _y[i + 1] <= 0_i);

    // before[ip][i] : x[ip] comes before x[i] under the total order (value,
    // then original index). For a fixed pair the index tie-break is constant,
    // so each flag is a plain comparison of two x values:
    //   ip < i : ties go to ip, so "before" iff x[ip] <= x[i];
    //   ip > i : ties go to i,  so "before" iff x[ip] <  x[i].
    _before.assign(n, std::vector<ProofFlag>(n));
    for (size_t i = 0; i < n; ++i)
        for (size_t ip = 0; ip < n; ++ip) {
            if (ip == i)
                continue;
            auto bound = (ip < i) ? 0_i : -1_i;
            _before[ip][i] = model.create_proof_flag_fully_reifying(
                "sort_before", "Sort", "stable before",
                WPBSum{} + 1_i * _x[ip] + -1_i * _x[i] <= bound);
        }

    // pos[i] is the stable rank of x[i]: the number of elements before it.
    _pos.clear();
    for (size_t i = 0; i < n; ++i)
        _pos.push_back(model.create_proof_only_integer_variable(
            0_i, Integer(n) - 1_i, "sort_pos_" + std::to_string(i),
            IntegerVariableProofRepresentation::Bits));

    // pos[i] = sum of "before" flags. Keep the ">=" half's line number: it is
    // pos[i] - sum >= 0, i.e. pos[i] >= (number of elements before i), which the
    // bound-proofs pol against.
    _rank_lines.clear();
    for (size_t i = 0; i < n; ++i) {
        WPBSum rank;
        rank += 1_i * _pos[i];
        for (size_t ip = 0; ip < n; ++ip)
            if (ip != i)
                rank += -1_i * _before[ip][i];
        auto [le, ge] = model.add_constraint("Sort", "pos is stable rank", move(rank) == 0_i);
        _rank_lines.push_back(ge.value());
    }

    // Channel: x[i] is placed at position pos[i] of y.
    for (size_t i = 0; i < n; ++i)
        for (size_t j = 0; j < n; ++j)
            model.add_constraint("Sort", "position channel",
                WPBSum{} + 1_i * _y[j] + -1_i * _x[i] == 0_i,
                HalfReifyOnConjunctionOf{{_pos[i] == Integer(j)}});
}

namespace
{
    // Mehlhorn-Thiel bounds-consistency propagation for Sortedness(x; y), i.e.
    // y = sort(x). Achieves bounds(Z) on both x and y (Thiel's thesis, ch. 3;
    // Mehlhorn & Thiel, CP 2000). See dev_docs/sortedness.md.
    //
    // PROOF LOGGING IS NOT DONE YET: every inference is emitted with the
    // development-only AssertRatherThanJustifying. Tests verify the algorithm
    // and the OPB encoding "subject to cheating assertions". The honest
    // justifications are to be worked out inference by inference and this file
    // must not be merged while the asserts remain.
    template <typename Inference_>
    auto propagate_sortedness(const vector<IntegerVariableID> & x, const vector<IntegerVariableID> & y,
        const vector<vector<ProofFlag>> & before, const vector<ProofOnlySimpleIntegerVariableID> & pos,
        const vector<ProofLine> & rank_lines,
        const State & state, Inference_ & inference, ProofLogger * const logger) -> void
    {
        auto n = x.size();
        (void) pos;

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

        vector<IntegerVariableID> all_vars = x;
        all_vars.insert(all_vars.end(), y.begin(), y.end());
        auto reason = bounds_reason(state, all_vars);
        auto fail = [&]() { inference.contradiction(logger, AssertRatherThanJustifying{}, reason); };

        // (1) Normalize the y-ranges: they index the sorted output, so the lower
        // bounds are non-decreasing and the upper bounds non-decreasing.
        for (size_t j = 1; j < n; ++j)
            ly[j] = std::max(ly[j], ly[j - 1]);
        for (size_t j = n - 1; j-- > 0;)
            uy[j] = std::min(uy[j], uy[j + 1]);
        for (size_t j = 0; j < n; ++j)
            if (ly[j] > uy[j])
                fail();

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
                    fail();
                auto [ub_i, i] = pq.top();
                pq.pop();
                if (ub_i < ly[j])
                    fail();
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
                    fail();
                auto [lb_i, i] = pq.top();
                pq.pop();
                if (lb_i > uy[j])
                    fail();
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
        // and y_j -> x_phi[j] for the matching. Plain recursive Tarjan; the
        // implicit interval adjacency keeps the first cut simple (not yet the
        // linear-time Algorithm 3.2 from the thesis).
        vector<size_t> lo_i(n), hi_i(n);
        for (size_t i = 0; i < n; ++i) {
            // smallest j with uy[j] >= lx[i]; largest j with ly[j] <= ux[i].
            size_t lo = static_cast<size_t>(std::lower_bound(uy.begin(), uy.end(), lx[i]) - uy.begin());
            size_t hi = static_cast<size_t>(std::upper_bound(ly.begin(), ly.end(), ux[i]) - ly.begin());
            lo_i[i] = lo;
            hi_i[i] = hi; // exclusive upper; neighbours are j in [lo, hi)
        }

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

        // Per-component y-index span.
        vector<size_t> comp_min_y(static_cast<size_t>(next_comp), n), comp_max_y(static_cast<size_t>(next_comp), 0);
        for (size_t j = 0; j < n; ++j) {
            auto c = static_cast<size_t>(comp[n + j]);
            comp_min_y[c] = std::min(comp_min_y[c], j);
            comp_max_y[c] = std::max(comp_max_y[c], j);
        }

        vector<long long> nlx(n), nux(n);
        for (size_t i = 0; i < n; ++i) {
            auto c = static_cast<size_t>(comp[i]);
            auto jl = comp_min_y[c], jh = comp_max_y[c];
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
                inference.infer_greater_than_or_equal(logger, y[j], Integer{L},
                    JustifyExplicitlyThenRUP{[&y, n, j, L, logger](const ReasonFunction &) -> void {
                        // ASSERTED (P2/P3, cheated): at least n-j of the y's are >= L.
                        WPBSum count;
                        for (size_t k = 0; k < n; ++k)
                            count += 1_i * (y[k] >= Integer{L});
                        logger->emit(AssertProofRule{}, move(count) >= Integer{static_cast<long long>(n - j)}, ProofLevel::Temporary);
                        // HONEST (P1): monotonicity (y[k-1] >= L) <- (y[k] >= L),
                        // each RUP from the single sortedness constraint y[k-1] <= y[k].
                        // Lets the closing RUP propagate (y[k] >= L) = 0 down from
                        // the negated goal for all k <= j.
                        for (size_t k = 1; k <= j; ++k)
                            logger->emit(RUPProofRule{},
                                WPBSum{} + 1_i * (y[k] >= Integer{L}) + 1_i * (y[k - 1] < Integer{L}) >= 1_i,
                                ProofLevel::Temporary);
                    }},
                    reason);
            }
            if (nuy[j] < ouy[j]) {
                auto U = nuy[j];
                inference.infer_less_than(logger, y[j], Integer{U + 1},
                    JustifyExplicitlyThenRUP{[&x, &y, &before, &pos, &rank_lines, n, j, U, logger](const ReasonFunction &) -> void {
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
                        // ASSERTED (P3, still cheated): at least j+1 of the x's are <= U.
                        WPBSum xcount;
                        for (size_t k = 0; k < n; ++k)
                            xcount += 1_i * (x[k] < Integer{U + 1});
                        auto xcount_line = logger->emit(AssertProofRule{}, move(xcount) >= Integer{static_cast<long long>(j) + 1}, ProofLevel::Temporary);
                        // RANKLB2_i : pos[i] + n*[x_i<=U] >= j+1, folding count_U away
                        // with the x-count (cross-constraint sum, hence a pol not RUP).
                        std::vector<ProofLine> ranklb2(n);
                        for (size_t i = 0; i < n; ++i) {
                            PolBuilder pol;
                            pol.add(ranklb[i]);
                            pol.add(xcount_line);
                            ranklb2[i] = pol.emit(*logger, ProofLevel::Temporary);
                        }
                        (void) ranklb2;
                        // HONEST (extended reason): per i, (pos[i] != j) v (y[j] <= U).
                        // RUP from RANKLB2_i + channel: negate -> pos[i]=j and
                        // y[j] >= U+1; channel gives x_i = y[j] >= U+1 so [x_i<=U]=0,
                        // and then RANKLB2_i forces pos[i] >= j+1, contradicting
                        // pos[i]=j.
                        for (size_t i = 0; i < n; ++i)
                            logger->emit(RUPProofRule{},
                                WPBSum{} + 1_i * (pos[i] != Integer(j)) + 1_i * (y[j] < Integer{U + 1}) >= 1_i,
                                ProofLevel::Temporary);
                        // ASSERTED (Stage 2b, surjectivity): rank j is occupied. With
                        // the per-i lines above, the closing RUP then closes: under
                        // y[j] >= U+1 each gives pos[i] != j, contradicting this.
                        WPBSum surj;
                        for (size_t i = 0; i < n; ++i)
                            surj += 1_i * (pos[i] == Integer(j));
                        logger->emit(AssertProofRule{}, move(surj) >= 1_i, ProofLevel::Temporary);
                    }},
                    reason);
            }
        }
        for (size_t i = 0; i < n; ++i) {
            if (nlx[i] > olx[i])
                inference.infer_greater_than_or_equal(logger, x[i], Integer{nlx[i]}, AssertRatherThanJustifying{}, reason);
            if (nux[i] < oux[i])
                inference.infer_less_than(logger, x[i], Integer{nux[i] + 1}, AssertRatherThanJustifying{}, reason);
        }
    }
}

auto Sort::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_bounds.insert(triggers.on_bounds.end(), _x.begin(), _x.end());
    triggers.on_bounds.insert(triggers.on_bounds.end(), _y.begin(), _y.end());

    propagators.install([x = _x, y = _y, before = _before, pos = _pos, rank_lines = _rank_lines](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        propagate_sortedness(x, y, before, pos, rank_lines, state, inference, logger);
        return PropagatorState::Enable;
    },
        triggers);
}

auto Sort::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} sort\n          (", _name);
    for (const auto & v : _x)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, ")\n          (");
    for (const auto & v : _y)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, ")");

    return s.str();
}
