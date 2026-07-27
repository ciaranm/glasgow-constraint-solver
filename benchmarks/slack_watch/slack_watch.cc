// Experiment: does the refined per-literal watch API fit slack-based wake-ups for
// a linear inequality Sum(x_i) <= value (unit positive coefficients)?
//
// Coarse mode wakes on every bound change of any variable (on_bounds triggers).
// Watched mode wakes only when a "covering" subset of variables moves: after
// propagating, slack S = value - Sum(lb_i); each variable's potential is
// (ub_i - lb_i) <= S; we watch the largest-potential variables until the
// unwatched potentials sum to within the margin B = S - max_potential, so that
// unwatched variables moving can never (cumulatively) drop the slack far enough
// to propagate. Only a watched variable's lower bound rising can, and we watch
// x_i >= lb_i + 1 to hear about it. This is the pseudo-Boolean "watch enough to
// cover the slack" scheme, expressed through the refined-watch API.
//
// Proofs are off (this is an API-fit experiment): inferences use
// NoJustificationNeeded. Both modes do the identical bounds sweep, so they must
// find the identical search tree; the interesting number is the wake count.

#include <gcs/gcs.hh>

#include <gcs/constraint.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <memory>
#include <numeric>
#include <random>
#include <vector>

#include <version>
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#endif

#include <cxxopts.hpp>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::mt19937;
using std::shared_ptr;
using std::size_t;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

namespace
{
    // The bounds sweep, shared by both modes: Sum(x_i) <= value, so each x_i is at
    // most lb-of-the-rest away from value, i.e. ub_i <= lb_i + slack. Returns false
    // on contradiction (caller must stop).
    template <typename Inference_>
    auto sweep(const vector<IntegerVariableID> & vars, Integer value, const State & state, Inference_ & inference, ProofLogger * const logger) -> bool
    {
        Integer lower_sum{0};
        for (const auto & v : vars)
            lower_sum += state.lower_bound(v);
        auto slack = value - lower_sum;
        if (slack < 0_i) {
            inference.contradiction(logger, JustifyUsingRUP{}, generic_reason(vars));
            return false;
        }
        for (const auto & v : vars) {
            auto cap = state.lower_bound(v) + slack; // ub_i <= lb_i + slack
            if (state.upper_bound(v) > cap)
                inference.infer(logger, v < cap + 1_i, NoJustificationNeeded{}, generic_reason(vars));
        }
        return true;
    }

    class SumLeqWatched : public Constraint
    {
        vector<IntegerVariableID> _vars;
        Integer _value;
        bool _watched;
        shared_ptr<long long> _wakes;

    public:
        SumLeqWatched(vector<IntegerVariableID> vars, Integer value, bool watched, shared_ptr<long long> wakes) :
            _vars(move(vars)), _value(value), _watched(watched), _wakes(move(wakes))
        {
        }

        auto clone() const -> std::unique_ptr<Constraint> override
        {
            return std::make_unique<SumLeqWatched>(_vars, _value, _watched, _wakes);
        }

        auto constraint_type() const -> std::string override
        {
            return "sum_leq_watched";
        }

        auto s_expr(const ProofModel * const) const -> SExpr override
        {
            return SExpr::atom("sum_leq_watched"); // unused: proofs are off
        }

        auto install(Propagators & propagators, State &, ProofModel * const) && -> void override
        {
            if (_watched)
                install_watched(propagators);
            else
                install_coarse(propagators);
        }

    private:
        auto install_coarse(Propagators & propagators) -> void
        {
            Triggers triggers;
            for (const auto & v : _vars)
                triggers.on_bounds.push_back(v);
            propagators.install(
                constraint_id(),
                [vars = _vars, value = _value, wakes = _wakes](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    ++*wakes;
                    sweep(vars, value, state, inference, logger);
                    return PropagatorState::Enable;
                },
                triggers);
        }

        auto install_watched(Propagators & propagators) -> void
        {
            // Declare every variable in scope via scope_only: the propagator is woken
            // only by the refined watches it arms, but its variables must still count
            // for degree/adjacency (so degree-based branchers behave as the coarse
            // version would) and, crucially, clear_watches() searches the declared
            // scope -- so an empty scope would make it a silent no-op.
            Triggers triggers;
            for (const auto & v : _vars)
                triggers.scope_only.push_back(v);
            propagators.install(
                constraint_id(),
                [vars = _vars, value = _value, wakes = _wakes](
                    const State & state, auto & inference, ProofLogger * const logger, const RefinedWatchContext & ctx) -> PropagatorState {
                    ++*wakes;
                    if (! sweep(vars, value, state, inference, logger))
                        return PropagatorState::Enable;

                    // Re-arm the covering watched set. After the sweep, slack and the
                    // per-variable potentials (ub - lb) are known; watch the largest
                    // potentials until the unwatched ones sum to within the margin.
                    Integer lower_sum{0};
                    for (const auto & v : vars)
                        lower_sum += state.lower_bound(v);
                    auto slack = value - lower_sum;

                    vector<Integer> pot(vars.size(), 0_i);
                    for (size_t i = 0; i < vars.size(); ++i)
                        pot[i] = state.upper_bound(vars[i]) - state.lower_bound(vars[i]);
                    vector<size_t> order(vars.size());
                    std::iota(order.begin(), order.end(), size_t{0});
                    std::ranges::sort(order, [&](size_t a, size_t b) { return pot[a] > pot[b]; });

                    Integer max_pot = vars.empty() ? 0_i : pot[order.front()];
                    auto margin = slack - max_pot; // >= 0 at the post-sweep fixpoint
                    Integer unwatched_sum{0};
                    for (auto i : order)
                        unwatched_sum += pot[i];

                    // Recompute the covering set from scratch each wake: drop every
                    // current watch, then walk from the largest potential, arming a
                    // variable until the remaining (smaller) potentials fit inside the
                    // margin. clear_watches() means a variable that leaves the covering
                    // set keeps no stale watch -- under the earlier is_watching
                    // idempotent re-arm it would linger until it happened to fire, a
                    // residual wake this eliminates.
                    ctx.clear_watches();
                    for (auto i : order) {
                        if (unwatched_sum <= margin)
                            break;
                        unwatched_sum -= pot[i];
                        ctx.watch(vars[i] >= state.lower_bound(vars[i]) + 1_i, static_cast<std::uint32_t>(i));
                    }
                    return PropagatorState::Enable;
                },
                std::move(triggers));
        }
    };

    auto build_and_solve(int n, int d, int budget_num, int budget_den, int nsums, int sumlen, unsigned seed, bool watched, long long & wakes_out)
        -> std::pair<unsigned long long, long long>
    {
        mt19937 rng(seed);
        std::uniform_int_distribution<int> pick(0, n - 1);
        auto wakes = make_shared<long long>(0);
        Problem p;
        auto vars = p.create_integer_variable_vector(static_cast<size_t>(n), 0_i, Integer{d});
        for (int c = 0; c < nsums; ++c) {
            vector<IntegerVariableID> scope;
            vector<bool> used(n, false);
            while (static_cast<int>(scope.size()) < sumlen) {
                int j = pick(rng);
                if (! used[j]) {
                    used[j] = true;
                    scope.push_back(vars[j]);
                }
            }
            // A budget that leaves the sum meaningfully constrained.
            Integer value{static_cast<long long>(sumlen) * d * budget_num / budget_den};
            p.post(SumLeqWatched{scope, value, watched, wakes});
        }
        unsigned long long recursions = 0;
        auto stats = solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return false; }, // first solution
                .branch = branch_with(variable_order::in_order(vars), value_order::smallest_first())});
        recursions = stats.recursions;
        wakes_out = *wakes;
        return {recursions, *wakes};
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("slack_watch", "Slack-based refined-watch experiment for Sum(x) <= k");
    options.add_options()                                                                    //
        ("vars", "Number of variables", cxxopts::value<int>()->default_value("60"))          //
        ("domain", "Domain 0..d", cxxopts::value<int>()->default_value("20"))                //
        ("sums", "Number of sum-<= constraints", cxxopts::value<int>()->default_value("40")) //
        ("sumlen", "Variables per sum", cxxopts::value<int>()->default_value("30"))          //
        ("budget-num", "Budget numerator", cxxopts::value<int>()->default_value("6"))        //
        ("budget-den", "Budget denominator", cxxopts::value<int>()->default_value("10"))     //
        ("seeds", "Number of seeds to average", cxxopts::value<int>()->default_value("5"))   //
        ("help", "Display help");
    auto o = options.parse(argc, argv);
    if (o.contains("help")) {
        println("{}", options.help());
        return EXIT_SUCCESS;
    }
    int n = o["vars"].as<int>(), d = o["domain"].as<int>(), nsums = o["sums"].as<int>(), sumlen = o["sumlen"].as<int>();
    int bn = o["budget-num"].as<int>(), bd = o["budget-den"].as<int>(), seeds = o["seeds"].as<int>();
    if (sumlen > n)
        sumlen = n;

    long long coarse_wakes_tot = 0, watched_wakes_tot = 0;
    unsigned long long coarse_rec_tot = 0, watched_rec_tot = 0;
    bool trees_match = true;
    for (int s = 1; s <= seeds; ++s) {
        long long cw = 0, ww = 0;
        auto [cr, c_wakes] = build_and_solve(n, d, bn, bd, nsums, sumlen, static_cast<unsigned>(s), false, cw);
        auto [wr, w_wakes] = build_and_solve(n, d, bn, bd, nsums, sumlen, static_cast<unsigned>(s), true, ww);
        coarse_wakes_tot += c_wakes;
        watched_wakes_tot += w_wakes;
        coarse_rec_tot += cr;
        watched_rec_tot += wr;
        if (cr != wr)
            trees_match = false;
    }
    println("seeds={} n={} domain=0..{} sums={} sumlen={} budget={}/{}", seeds, n, d, nsums, sumlen, bn, bd);
    println("trees identical: {}", trees_match ? "YES" : "NO");
    println("recursions (sum over seeds): coarse={} watched={}", coarse_rec_tot, watched_rec_tot);
    println("propagator wakes (sum over seeds): coarse={} watched={}", coarse_wakes_tot, watched_wakes_tot);
    if (watched_wakes_tot > 0)
        println("wake reduction: {:.2f}x", static_cast<double>(coarse_wakes_tot) / static_cast<double>(watched_wakes_tot));
    return EXIT_SUCCESS;
}
