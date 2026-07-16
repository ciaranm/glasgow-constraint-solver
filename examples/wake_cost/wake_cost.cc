// Micro-benchmark: per-wake cost of the coarse trigger mechanism vs the refined
// per-literal watch mechanism.
//
// A pool of variables is enumerated by in-order / smallest-first branching, giving
// a fixed search tree. On top of that we post M "observer" constraints over all
// the variables that do NO inference -- they only count how often they are woken
// -- either via coarse on_bounds triggers or via refined watches (two per
// variable, re-armed when they fire). Since observers never change a domain, the
// tree is identical in all three modes, so (time_with_observers - baseline_time)
// divided by the wake count is the amortised end-to-end cost of one wake: the
// requeue scan, the firing bookkeeping, the propagator dispatch, and -- for
// refined -- the watch-index edit and its backtrack replay.

#include <gcs/gcs.hh>

#include <gcs/constraint.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <memory>
#include <tuple>
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
    enum class Mode
    {
        None,
        Coarse,
        Refined
    };

    class Observer : public Constraint
    {
        vector<IntegerVariableID> _vars;
        Mode _mode;
        shared_ptr<long long> _wakes;

    public:
        Observer(vector<IntegerVariableID> vars, Mode mode, shared_ptr<long long> wakes) : _vars(move(vars)), _mode(mode), _wakes(move(wakes))
        {
        }

        auto clone() const -> std::unique_ptr<Constraint> override
        {
            return std::make_unique<Observer>(_vars, _mode, _wakes);
        }

        auto constraint_type() const -> std::string override
        {
            return "observer";
        }

        auto s_expr(const ProofModel * const) const -> SExpr override
        {
            return SExpr::atom("observer");
        }

        auto install(Propagators & propagators, State &, ProofModel * const) && -> void override
        {
            auto wakes = _wakes;
            if (_mode == Mode::Coarse) {
                Triggers triggers;
                for (const auto & v : _vars)
                    triggers.on_bounds.push_back(v);
                propagators.install(
                    constraint_id(),
                    [wakes](const State &, auto &, ProofLogger * const) -> PropagatorState {
                        ++*wakes;
                        return PropagatorState::Enable;
                    },
                    triggers);
            }
            else {
                Triggers triggers;
                for (const auto & v : _vars)
                    triggers.scope_only.push_back(v);
                propagators.install(
                    constraint_id(),
                    [vars = _vars, wakes](const State & state, auto &, ProofLogger * const, const RefinedWatchContext & ctx) -> PropagatorState {
                        ++*wakes;
                        auto arm = [&](size_t i) {
                            auto b = state.bounds(vars[i]);
                            if (b.first < b.second) {
                                ctx.watch(vars[i] >= b.first + 1_i, static_cast<std::uint32_t>(2 * i));
                                ctx.watch(vars[i] <= b.second - 1_i, static_cast<std::uint32_t>(2 * i + 1));
                            }
                        };
                        if (ctx.fired_payloads().empty()) {
                            for (size_t i = 0; i < vars.size(); ++i)
                                arm(i);
                        }
                        else {
                            // Re-arm each fired watch at the variable's new bound, so the
                            // observer keeps being woken (the coarse triggers persist for
                            // free; a refined watch is consumed on firing).
                            for (auto pl : ctx.fired_payloads()) {
                                size_t i = pl / 2;
                                auto b = state.bounds(vars[i]);
                                if (b.first >= b.second)
                                    continue;
                                if (pl % 2 == 0)
                                    ctx.watch(vars[i] >= b.first + 1_i, pl);
                                else
                                    ctx.watch(vars[i] <= b.second - 1_i, pl);
                            }
                        }
                        return PropagatorState::Enable;
                    },
                    triggers);
            }
        }
    };

    auto run(int n, int d, int m, long long cap, Mode mode) -> std::tuple<double, unsigned long long, long long>
    {
        auto wakes = make_shared<long long>(0);
        Problem p;
        auto vars = p.create_integer_variable_vector(static_cast<size_t>(n), 0_i, Integer{d});
        if (mode != Mode::None)
            for (int k = 0; k < m; ++k)
                p.post(Observer{vector<IntegerVariableID>(vars.begin(), vars.end()), mode, wakes});
        long long sols = 0;
        auto start = std::chrono::steady_clock::now();
        auto stats = solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return ++sols < cap; },
                .branch = branch_with(variable_order::in_order(vars), value_order::smallest_first())});
        auto elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
        return {elapsed, stats.recursions, *wakes};
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("wake_cost", "Per-wake cost: coarse triggers vs refined watches");
    options.add_options()                                                                               //
        ("vars", "Number of variables", cxxopts::value<int>()->default_value("22"))                     //
        ("domain", "Domain 0..d", cxxopts::value<int>()->default_value("3"))                            //
        ("observers", "Number of observer constraints", cxxopts::value<int>()->default_value("32"))     //
        ("cap", "Stop after this many solutions", cxxopts::value<long long>()->default_value("100000")) //
        ("help", "Display help");
    auto o = options.parse(argc, argv);
    if (o.contains("help")) {
        println("{}", options.help());
        return EXIT_SUCCESS;
    }
    int n = o["vars"].as<int>(), d = o["domain"].as<int>(), m = o["observers"].as<int>();
    long long cap = o["cap"].as<long long>();

    auto [t0, r0, w0] = run(n, d, m, cap, Mode::None);
    auto [tc, rc, wc] = run(n, d, m, cap, Mode::Coarse);
    auto [tr, rr, wr] = run(n, d, m, cap, Mode::Refined);

    println("vars={} domain=0..{} observers={} cap={}", n, d, m, cap);
    println("recursions (must match): none={} coarse={} refined={}", r0, rc, rr);
    println("baseline (no observers):        wall={:.4f}s", t0);
    println("coarse  triggers: wall={:.4f}s wakes={} overhead={:.4f}s per-wake={:.1f}ns", tc, wc, tc - t0,
        wc ? (tc - t0) / static_cast<double>(wc) * 1e9 : 0.0);
    println("refined watches:  wall={:.4f}s wakes={} overhead={:.4f}s per-wake={:.1f}ns", tr, wr, tr - t0,
        wr ? (tr - t0) / static_cast<double>(wr) * 1e9 : 0.0);
    if (wc && wr && (tc - t0) > 0)
        println("refined per-wake / coarse per-wake = {:.2f}x", ((tr - t0) / static_cast<double>(wr)) / ((tc - t0) / static_cast<double>(wc)));
    return EXIT_SUCCESS;
}
