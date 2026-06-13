#include <gcs/innards/propagators.hh>
#include <gcs/search_heuristics.hh>

#include <algorithm>
#include <memory>
#include <random>

using std::generator;
using std::make_shared;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::random_device;
using std::shared_ptr;
using std::tuple;
using std::uint_fast32_t;
using std::uniform_int_distribution;
using std::vector;
using std::ranges::shuffle;

namespace
{
    // Random heuristics share their mt19937 across branching steps via a
    // shared_ptr captured into the closure: the closure is held by-value in
    // a std::function and may be copied, so the shared_ptr is the only way
    // to keep all copies pointing at the same RNG state. The unseeded
    // variants below pull a single seed from random_device once at
    // construction; the seeded variants take the seed from the caller.
    auto make_shared_rng(uint_fast32_t seed) -> shared_ptr<mt19937>
    {
        return make_shared<mt19937>(seed);
    }

    auto make_shared_rng() -> shared_ptr<mt19937>
    {
        random_device rd;
        return make_shared_rng(rd());
    }
}

using namespace gcs;

auto gcs::branch_with(BranchVariableHeuristic var, BranchValueGenerator val) -> BranchHeuristic
{
    return [var = move(var), val = move(val)](const Problem & problem, innards::State & state, innards::Propagators & propagators) -> BranchCallback {
        // Run the variable heuristic's per-search setup once, then reuse the
        // resulting selector at every node.
        auto select_var = var(problem, state, propagators);
        return [select_var = move(select_var), val = val](const CurrentState & s, const innards::Propagators & p) -> generator<IntegerVariableCondition> {
            return [](const CurrentState & s, const innards::Propagators & p,
                       BranchVariableSelector select_var, BranchValueGenerator make_val_gen) -> generator<IntegerVariableCondition> {
                auto branch_var = select_var(s, p);
                if (branch_var)
                    return make_val_gen(s, p, *branch_var);
                else
                    return []() -> generator<IntegerVariableCondition> { co_return; }();
            }(s, p, select_var, val);
        };
    };
}

auto gcs::branch_sequence(BranchHeuristic a, BranchHeuristic b) -> BranchHeuristic
{
    return [a = move(a), b = move(b)](const Problem & problem, innards::State & state, innards::Propagators & propagators) -> BranchCallback {
        auto callback_a = a(problem, state, propagators);
        auto callback_b = b(problem, state, propagators);
        return [callback_a = move(callback_a), callback_b = move(callback_b)](const CurrentState & s, const innards::Propagators & p) -> generator<IntegerVariableCondition> {
            return [](const CurrentState & s, const innards::Propagators & p, BranchCallback a, BranchCallback b) -> generator<IntegerVariableCondition> {
                auto gen_a = a(s, p);
                auto iter_a = gen_a.begin();
                if (iter_a != gen_a.end()) {
                    for (; iter_a != gen_a.end(); ++iter_a)
                        co_yield *iter_a;
                }
                else {
                    auto gen_b = b(s, p);
                    auto iter_b = gen_b.begin();
                    for (; iter_b != gen_b.end(); ++iter_b)
                        co_yield *iter_b;
                }
            }(s, p, callback_a, callback_b);
        };
    };
}

namespace
{
    auto random_variable_selector(vector<IntegerVariableID> vars, shared_ptr<mt19937> rand) -> BranchVariableSelector
    {
        return [vars = move(vars), rand = move(rand)](const CurrentState & state,
                   const innards::Propagators &) -> optional<IntegerVariableID> {
            vector<IntegerVariableID> feasible;
            for (auto & var : vars)
                if (state.domain_size(var) >= 2_i)
                    feasible.push_back(var);
            if (feasible.empty())
                return nullopt;
            else {
                uniform_int_distribution<size_t> dist(0, feasible.size() - 1);
                return feasible[dist(*rand)];
            }
        };
    }

    auto in_order_of_selector(vector<IntegerVariableID> vars, variable_order::VariableComparator comp) -> BranchVariableSelector
    {
        return [vars = move(vars), comp = move(comp)](
                   const CurrentState & state, const innards::Propagators & propagators) -> optional<IntegerVariableID> {
            optional<IntegerVariableID> result;
            for (auto & v : vars) {
                auto size = state.domain_size(v);
                if (size < 2_i)
                    continue;
                if ((! result) || comp(state, propagators, v, *result))
                    result = v;
            }
            return result;
        };
    }

    // Wrap a stateless selector (one needing no per-search setup) as a
    // BranchVariableHeuristic: the setup ignores its arguments and just returns
    // the selector.
    auto as_heuristic(BranchVariableSelector selector) -> BranchVariableHeuristic
    {
        return [selector = move(selector)](const Problem &, innards::State &, innards::Propagators &) -> BranchVariableSelector {
            return selector;
        };
    }
}

auto gcs::variable_order::random(const Problem & problem) -> BranchVariableHeuristic
{
    return variable_order::random(problem.all_normal_variables());
}

auto gcs::variable_order::random(vector<IntegerVariableID> vars) -> BranchVariableHeuristic
{
    return as_heuristic(random_variable_selector(move(vars), make_shared_rng()));
}

auto gcs::variable_order::random(const Problem & problem, uint_fast32_t seed) -> BranchVariableHeuristic
{
    return variable_order::random(problem.all_normal_variables(), seed);
}

auto gcs::variable_order::random(vector<IntegerVariableID> vars, uint_fast32_t seed) -> BranchVariableHeuristic
{
    return as_heuristic(random_variable_selector(move(vars), make_shared_rng(seed)));
}

auto gcs::variable_order::in_order_of(const Problem & problem, VariableComparator comp) -> BranchVariableHeuristic
{
    return variable_order::in_order_of(problem.all_normal_variables(), move(comp));
}

auto gcs::variable_order::in_order_of(vector<IntegerVariableID> vars, VariableComparator comp) -> BranchVariableHeuristic
{
    return as_heuristic(in_order_of_selector(move(vars), move(comp)));
}

auto gcs::variable_order::in_order(vector<IntegerVariableID> vars) -> BranchVariableHeuristic
{
    return as_heuristic([vars = move(vars)](
                            const CurrentState & state, const innards::Propagators &) -> optional<IntegerVariableID> {
        for (auto & v : vars) {
            auto size = state.domain_size(v);
            if (size < 2_i)
                continue;
            return v;
        }
        return nullopt;
    });
}

auto gcs::variable_order::dom(const Problem & problem) -> BranchVariableHeuristic
{
    return dom(problem.all_normal_variables());
}

auto gcs::variable_order::dom(vector<IntegerVariableID> vars) -> BranchVariableHeuristic
{
    return variable_order::in_order_of(vars, [](const CurrentState & state, const innards::Propagators &, const IntegerVariableID & a, const IntegerVariableID & b) {
        return state.domain_size(a) < state.domain_size(b);
    });
}

auto gcs::variable_order::dom_then_deg(const Problem & problem) -> BranchVariableHeuristic
{
    return dom_then_deg(problem.all_normal_variables());
}

auto gcs::variable_order::dom_then_deg(vector<IntegerVariableID> vars) -> BranchVariableHeuristic
{
    return variable_order::in_order_of(vars, [](const CurrentState & state, const innards::Propagators & p, const IntegerVariableID & a, const IntegerVariableID & b) {
        return tuple{state.domain_size(a), -p.degree_of(a)} < tuple{state.domain_size(b), -p.degree_of(b)};
    });
}

auto gcs::variable_order::dom_wdeg(const Problem & problem, optional<WeightingState> initial) -> BranchVariableHeuristic
{
    return dom_wdeg(problem.all_normal_variables(), move(initial));
}

auto gcs::variable_order::dom_wdeg(vector<IntegerVariableID> vars, optional<WeightingState> initial) -> BranchVariableHeuristic
{
    return [vars = move(vars), initial = move(initial)](
               const Problem &, innards::State &, innards::Propagators & propagators) -> BranchVariableSelector {
        auto weighting = make_shared<ClassicDomWDeg>(propagators);
        if (initial)
            weighting->load(*initial, propagators);
        propagators.set_conflict_observer(weighting.get());

        return in_order_of_selector(vars,
            [weighting](const CurrentState & state, const innards::Propagators & p,
                const IntegerVariableID & a, const IntegerVariableID & b) -> bool {
                // Minimise dom(x)/W(x), cross-multiplied to avoid division: a
                // variable with W(x)=0 (in no constraint with two or more
                // unassigned variables) then sorts last for free. Tie-break on
                // highest degree, matching dom_then_deg.
                auto dom_a = static_cast<double>(state.domain_size(a).raw_value);
                auto dom_b = static_cast<double>(state.domain_size(b).raw_value);
                auto w_a = weighting->weighted_degree_of(state, p, a);
                auto w_b = weighting->weighted_degree_of(state, p, b);
                auto lhs = dom_a * w_b;
                auto rhs = dom_b * w_a;
                if (lhs != rhs)
                    return lhs < rhs;
                return p.degree_of(a) > p.degree_of(b);
            });
    };
}

auto gcs::variable_order::with_smallest_value(const Problem & problem) -> BranchVariableHeuristic
{
    return with_smallest_value(problem.all_normal_variables());
}

auto gcs::variable_order::with_smallest_value(vector<IntegerVariableID> vars) -> BranchVariableHeuristic
{
    return variable_order::in_order_of(vars, [](const CurrentState & state, const innards::Propagators &, const IntegerVariableID & a, const IntegerVariableID & b) {
        return state.lower_bound(a) < state.lower_bound(b);
    });
}

namespace
{
    auto random_value_generator(shared_ptr<mt19937> rand) -> BranchValueGenerator
    {
        return [rand = move(rand)](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
            return [](shared_ptr<mt19937> rand, const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
                vector<Integer> values;
                for (auto v : s.each_value(var))
                    values.push_back(v);
                shuffle(values, *rand);
                for (auto v : values)
                    co_yield var == v;
            }(rand, s, var);
        };
    }

    auto random_out_value_generator(shared_ptr<mt19937> rand) -> BranchValueGenerator
    {
        return [rand = move(rand)](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
            return [](shared_ptr<mt19937> rand, const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
                vector<Integer> values;
                for (auto v : s.each_value(var))
                    values.push_back(v);
                uniform_int_distribution<size_t> dist(0, values.size() - 1);
                auto val = values.at(dist(*rand));
                co_yield var != val;
                co_yield var == val;
            }(rand, s, var);
        };
    }
}

auto gcs::value_order::random() -> BranchValueGenerator
{
    return random_value_generator(make_shared_rng());
}

auto gcs::value_order::random(uint_fast32_t seed) -> BranchValueGenerator
{
    return random_value_generator(make_shared_rng(seed));
}

auto gcs::value_order::random_out() -> BranchValueGenerator
{
    return random_out_value_generator(make_shared_rng());
}

auto gcs::value_order::random_out(uint_fast32_t seed) -> BranchValueGenerator
{
    return random_out_value_generator(make_shared_rng(seed));
}

auto gcs::value_order::smallest_in() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            auto value = s.lower_bound(var);
            co_yield var == value;
            co_yield var != value;
        }(s, var);
    };
}

auto gcs::value_order::smallest_out() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            auto value = s.lower_bound(var);
            co_yield var != value;
            co_yield var == value;
        }(s, var);
    };
}

auto gcs::value_order::smallest_first() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            for (auto v : s.each_value(var))
                co_yield var == v;
        }(s, var);
    };
}

auto gcs::value_order::split_smallest_first() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            auto mid = s.domain_size(var) / 2_i;
            auto v = *(s.each_value(var) | std::ranges::views::drop((mid - 1_i).as_index())).begin();
            co_yield var <= v;
            co_yield var > v;
        }(s, var);
    };
}

auto gcs::value_order::split_largest_first() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            auto mid = s.domain_size(var) / 2_i;
            auto v = *(s.each_value(var) | std::ranges::views::drop((mid - 1_i).as_index())).begin();
            co_yield var > v;
            co_yield var <= v;
        }(s, var);
    };
}

namespace
{
    auto split_random_value_generator(shared_ptr<mt19937> rand) -> BranchValueGenerator
    {
        return [rand = move(rand)](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
            return [](shared_ptr<mt19937> rand, const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
                auto mid = s.domain_size(var) / 2_i;
                auto v = *(s.each_value(var) | std::ranges::views::drop((mid - 1_i).as_index())).begin();
                if (uniform_int_distribution(0, 1)(*rand) == 0) {
                    co_yield var > v;
                    co_yield var <= v;
                }
                else {
                    co_yield var > v;
                    co_yield var <= v;
                }
            }(rand, s, var);
        };
    }
}

auto gcs::value_order::split_random() -> BranchValueGenerator
{
    return split_random_value_generator(make_shared_rng());
}

auto gcs::value_order::split_random(uint_fast32_t seed) -> BranchValueGenerator
{
    return split_random_value_generator(make_shared_rng(seed));
}

auto gcs::value_order::largest_in() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            auto value = s.upper_bound(var);
            co_yield var == value;
            co_yield var != value;
        }(s, var);
    };
}

auto gcs::value_order::largest_out() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            auto value = s.upper_bound(var);
            co_yield var != value;
            co_yield var == value;
        }(s, var);
    };
}

auto gcs::value_order::largest_first() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            for (auto v : s.each_value_reversed(var))
                co_yield var == v;
        }(s, var);
    };
}

auto gcs::value_order::median() -> BranchValueGenerator
{
    return [](const CurrentState & s, const innards::Propagators &, const IntegerVariableID & var) -> generator<IntegerVariableCondition> {
        return [](const CurrentState & s, IntegerVariableID var) -> generator<IntegerVariableCondition> {
            vector<Integer> values;
            for (auto v : s.each_value(var))
                values.push_back(v);
            auto v = values.at(values.size() / 2);
            co_yield var == v;
            co_yield var != v;
        }(s, var);
    };
}
