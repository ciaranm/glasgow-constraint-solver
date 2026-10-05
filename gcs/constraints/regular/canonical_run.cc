#include <gcs/constraints/regular/canonical_run.hh>
#include <gcs/innards/proofs/am1_from_pairs.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_scaffolding_scope.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <cstddef>
#include <optional>
#include <set>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::cmp_less;
using std::get;
using std::max;
using std::min;
using std::move;
using std::optional;
using std::pair;
using std::set;
using std::size_t;
using std::tuple;
using std::unordered_map;
using std::vector;
using std::ranges::any_of;

namespace
{
    using Transitions = vector<unordered_map<Integer, set<long>>>;

    auto targets_of(const Transitions & transitions, long q, Integer val) -> const set<long> &
    {
        static const set<long> none;
        if (! cmp_less(q, transitions.size()))
            return none;
        auto it = transitions[q].find(val);
        return it == transitions[q].end() ? none : it->second;
    }

    // The automaton unrolled over the variables' domains. A state is live at a
    // layer if it is reachable there from the start and can still reach a final
    // state; every accepting run stays inside the live states.
    struct Layers
    {
        vector<vector<Integer>> values;
        vector<set<long>> forward;
        vector<set<long>> live;
    };

    auto compute_layers(
        const vector<IntegerVariableID> & vars, const Transitions & transitions, const vector<long> & final_states, const State & state) -> Layers
    {
        auto n = vars.size();
        Layers result{vector<vector<Integer>>(n), vector<set<long>>(n + 1), vector<set<long>>(n + 1)};
        for (size_t i = 0; i < n; ++i)
            for (auto val : state.each_value_immutable(vars[i]))
                result.values[i].push_back(val);

        result.forward[0].insert(0);
        for (size_t i = 0; i < n; ++i)
            for (auto q : result.forward[i])
                for (auto val : result.values[i])
                    for (auto next_q : targets_of(transitions, q, val))
                        result.forward[i + 1].insert(next_q);

        for (auto f : final_states)
            if (result.forward[n].contains(f))
                result.live[n].insert(f);
        for (auto i = n; i-- > 0;)
            for (auto q : result.forward[i])
                if (any_of(result.values[i], [&](Integer val) {
                        return any_of(targets_of(transitions, q, val), [&](long next_q) { return result.live[i + 1].contains(next_q); });
                    }))
                    result.live[i].insert(q);

        return result;
    }

    // The live targets of (q, val) out of layer i, ascending.
    auto live_targets(const Layers & layers, const Transitions & transitions, size_t i, long q, Integer val) -> vector<long>
    {
        vector<long> result;
        for (auto next_q : targets_of(transitions, q, val))
            if (layers.live[i + 1].contains(next_q))
                result.push_back(next_q);
        return result;
    }

    // Statically dead state flags are false. Forward-unreachable states go
    // first, in ascending layer order, each by way of its per-value backward
    // chains, which are working and deleted afterwards; then states that cannot
    // reach a final state, in descending order.
    auto emit_static_dead_states(ProofLogger & logger, const vector<IntegerVariableID> & vars, long num_states, const Transitions & transitions,
        const Layers & layers, const vector<vector<ProofFlag>> & st) -> void
    {
        auto n = vars.size();
        auto rup = [&](WPBSum sum, ProofLevel level) { return logger.emit_rup_proof_line(move(sum) >= 1_i, level); };
        ProofScaffoldingScope scaffolding{logger};

        logger.emit_proof_comment("Regular: static dead states");
        for (size_t i = 0; i < n; ++i)
            for (long next_q = 0; next_q < num_states; ++next_q) {
                if (layers.forward[i + 1].contains(next_q))
                    continue;
                for (auto val : layers.values[i]) {
                    WPBSum chain = WPBSum{} + 1_i * ! st[i + 1][next_q] + 1_i * (vars[i] != val);
                    for (long q = 0; q < num_states; ++q)
                        if (targets_of(transitions, q, val).contains(next_q))
                            chain += 1_i * st[i][q];
                    rup(move(chain), ProofLevel::Temporary);
                }
                rup(WPBSum{} + 1_i * ! st[i + 1][next_q], ProofLevel::Top);
            }
        for (long q = 1; q < num_states; ++q)
            rup(WPBSum{} + 1_i * ! st[0][q], ProofLevel::Top);
        for (auto i = n + 1; i-- > 0;)
            for (auto q : layers.forward[i])
                if (! layers.live[i].contains(q))
                    rup(WPBSum{} + 1_i * ! st[i][q], ProofLevel::Top);
    }

    auto is_constant(const ProofLiteralOrFlag & lit) -> bool
    {
        if (auto proof_lit = std::get_if<ProofLiteral>(&lit))
            if (auto plain = std::get_if<Literal>(proof_lit))
                return std::holds_alternative<TrueLiteral>(*plain) || std::holds_alternative<FalseLiteral>(*plain);
        return false;
    }
}

auto gcs::innards::regular_is_nondeterministic(const Transitions & transitions) -> bool
{
    return any_of(transitions, [](const auto & by_val) { return any_of(by_val, [](const auto & entry) { return entry.second.size() > 1; }); });
}

auto gcs::innards::emit_regular_static_dead_states(ProofLogger & logger, const vector<IntegerVariableID> & vars, long num_states,
    const Transitions & transitions, const vector<long> & final_states, const vector<vector<ProofFlag>> & st, const State & state) -> void
{
    emit_static_dead_states(logger, vars, num_states, transitions, compute_layers(vars, transitions, final_states, state), st);
}

auto gcs::innards::regular_is_ambiguous(
    const vector<IntegerVariableID> & vars, const Transitions & transitions, const vector<long> & final_states, const State & state) -> bool
{
    if (! regular_is_nondeterministic(transitions))
        return false;

    auto layers = compute_layers(vars, transitions, final_states, state);
    if (! layers.live[0].contains(0))
        return false;

    // A pair of runs on one word, as (lower state, higher state, have they
    // diverged). Every live state at the last layer is final, so a diverged
    // pair there is two accepting runs.
    set<tuple<long, long, bool>> pairs{{0, 0, false}};
    for (size_t i = 0; i < vars.size(); ++i) {
        set<tuple<long, long, bool>> next_pairs;
        for (const auto & [p, q, diverged] : pairs)
            for (auto val : layers.values[i])
                for (auto next_p : live_targets(layers, transitions, i, p, val))
                    for (auto next_q : live_targets(layers, transitions, i, q, val))
                        next_pairs.emplace(min(next_p, next_q), max(next_p, next_q), diverged || next_p != next_q);
        pairs = move(next_pairs);
    }

    return any_of(pairs, [](const auto & pair) { return get<2>(pair); });
}

auto gcs::innards::emit_regular_canonical_run(ProofLogger & logger, const vector<IntegerVariableID> & vars, long num_states,
    const Transitions & transitions, const vector<long> & final_states, const vector<vector<ProofFlag>> & st, const State & state) -> void
{
    auto n = vars.size();
    auto layers = compute_layers(vars, transitions, final_states, state);
    const auto & live = layers.live;

    auto x_is = [&](size_t i, Integer val) -> ProofLiteralOrFlag { return ProofLiteral{Literal{vars[i] == val}}; };
    auto rup = [&](WPBSum sum, ProofLevel level) { return logger.emit_rup_proof_line(move(sum) >= 1_i, level); };

    emit_static_dead_states(logger, vars, num_states, transitions, layers, st);

    // Everything below that is only there to discharge the final red's goals
    // goes at Temporary, and is deleted when this scope ends. The definitions
    // and the pinning itself stay, at Top.
    ProofScaffoldingScope scaffolding{logger};

    // b[i][q]: the rest of the word, from x_i on, takes state q to a final
    // state. Defined over live states only, through
    // t[i][q][v] <-> x_i = v /\ some live target of (q, v) has b.
    // At the last layer every live state is final.
    logger.emit_proof_comment("Regular: canonical run, co-reachability");
    vector<vector<optional<ProofLiteralOrFlag>>> b(n + 1, vector<optional<ProofLiteralOrFlag>>(num_states));
    for (auto q : live[n])
        b[n][q] = TrueLiteral{};
    for (auto i = n; i-- > 0;)
        for (auto q : live[i]) {
            WPBSum any_t;
            for (auto val : layers.values[i]) {
                auto targets = live_targets(layers, transitions, i, q, val);
                if (targets.empty())
                    continue;
                if (i + 1 == n) {
                    add_term_to(any_t, 1_i, x_is(i, val));
                    continue;
                }
                auto k = Integer{static_cast<long long>(targets.size())};
                WPBSum t_def;
                add_term_to(t_def, k, x_is(i, val));
                for (auto next_q : targets)
                    add_term_to(t_def, 1_i, *b[i + 1][next_q]);
                add_term_to(any_t, 1_i, get<0>(logger.create_proof_flag_reifying(move(t_def) >= k + 1_i, "regt", ProofLevel::Top)));
            }
            b[i][q] = get<0>(logger.create_proof_flag_reifying(move(any_t) >= 1_i, "regb", ProofLevel::Top));
        }

    // c[i][q]: the canonical run is in state q at layer i. It starts where the
    // state flags do, and from each state steps to the lowest-numbered live
    // target that still has b. Each edge it might take gets a flag d for that
    // choice; c is the disjunction of the edges into it.
    logger.emit_proof_comment("Regular: canonical run, the run");
    vector<vector<optional<ProofLiteralOrFlag>>> c(n + 1, vector<optional<ProofLiteralOrFlag>>(num_states));
    vector<vector<vector<ProofLiteralOrFlag>>> edges_into(n + 1, vector<vector<ProofLiteralOrFlag>>(num_states));
    for (auto q : live[0])
        c[0][q] = st[0][q];
    for (size_t i = 0; i < n; ++i) {
        for (auto q : live[i])
            for (auto val : layers.values[i]) {
                auto targets = live_targets(layers, transitions, i, q, val);
                for (size_t j = 0; j < targets.size(); ++j) {
                    // At the last layer b holds for every live target, so only the
                    // lowest can be chosen.
                    if (i + 1 == n && j > 0)
                        break;
                    WPBSum choice;
                    add_term_to(choice, 1_i, *c[i][q]);
                    add_term_to(choice, 1_i, x_is(i, val));
                    add_term_to(choice, 1_i, *b[i + 1][targets[j]]);
                    for (size_t k = 0; k < j; ++k)
                        add_term_to(choice, 1_i, ! *b[i + 1][targets[k]]);
                    auto size = Integer{static_cast<long long>(j + 3)};
                    edges_into[i + 1][targets[j]].push_back(get<0>(logger.create_proof_flag_reifying(move(choice) >= size, "regd", ProofLevel::Top)));
                }
            }
        for (auto next_q : live[i + 1]) {
            if (edges_into[i + 1][next_q].empty()) {
                c[i + 1][next_q] = FalseLiteral{};
                continue;
            }
            WPBSum any_edge;
            for (const auto & edge : edges_into[i + 1][next_q])
                add_term_to(any_edge, 1_i, edge);
            c[i + 1][next_q] = get<0>(logger.create_proof_flag_reifying(move(any_edge) >= 1_i, "regc", ProofLevel::Top));
        }
    }

    // The state flags' run follows b: st[i][q] -> b[i][q], per value and then
    // over the values, backwards from the last layer.
    logger.emit_proof_comment("Regular: canonical run, the chosen run is co-reachable");
    for (auto i = n; i-- > 0;)
        for (auto q : live[i]) {
            for (auto val : layers.values[i]) {
                WPBSum lemma = WPBSum{} + 1_i * ! st[i][q] + 1_i * (vars[i] != val);
                add_term_to(lemma, 1_i, *b[i][q]);
                rup(move(lemma), ProofLevel::Temporary);
            }
            WPBSum lemma = WPBSum{} + 1_i * ! st[i][q];
            add_term_to(lemma, 1_i, *b[i][q]);
            rup(move(lemma), ProofLevel::Temporary);
        }

    // The OPB's rows hold for c, reading every dead state flag as false.
    logger.emit_proof_comment("Regular: canonical run, the rows hold for it");
    for (size_t i = 1; i < n; ++i)
        for (auto q : live[i])
            if (! is_constant(*c[i][q])) {
                WPBSum lemma;
                add_term_to(lemma, 1_i, ! *c[i][q]);
                add_term_to(lemma, 1_i, *b[i][q]);
                rup(move(lemma), ProofLevel::Temporary);
            }

    for (size_t i = 0; i < n; ++i)
        for (auto q : live[i])
            for (auto val : layers.values[i]) {
                WPBSum row;
                add_term_to(row, 1_i, ! *c[i][q]);
                row += 1_i * (vars[i] != val);
                for (auto next_q : live_targets(layers, transitions, i, q, val))
                    add_term_to(row, 1_i, *c[i + 1][next_q]);
                rup(move(row), ProofLevel::Temporary);
            }

    for (size_t i = 1; i <= n; ++i) {
        WPBSum at_least_one;
        for (auto next_q : live[i])
            add_term_to(at_least_one, 1_i, *c[i][next_q]);
        for (auto q : live[i - 1]) {
            WPBSum step = at_least_one;
            add_term_to(step, 1_i, ! *c[i - 1][q]);
            rup(move(step), ProofLevel::Temporary);
        }
        rup(move(at_least_one), ProofLevel::Temporary);

        // At most one, pairwise and then as a cardinality constraint. Two edges
        // into different states cannot both be chosen: they leave from different
        // states, or on different values, or are the same choice between two
        // targets, which picks only one.
        vector<long> members;
        for (auto next_q : live[i])
            if (! is_constant(*c[i][next_q]))
                members.push_back(next_q);
        if (members.size() < 2)
            continue;
        vector<vector<ProofLine>> at_most_ones(members.size());
        for (size_t hi = 0; hi < members.size(); ++hi)
            for (size_t lo = 0; lo < hi; ++lo) {
                for (const auto & edge : edges_into[i][members[lo]]) {
                    WPBSum exclusion;
                    add_term_to(exclusion, 1_i, ! edge);
                    add_term_to(exclusion, 1_i, ! *c[i][members[hi]]);
                    rup(move(exclusion), ProofLevel::Temporary);
                }
                WPBSum pair_line;
                add_term_to(pair_line, 1_i, ! *c[i][members[lo]]);
                add_term_to(pair_line, 1_i, ! *c[i][members[hi]]);
                at_most_ones[hi].push_back(rup(move(pair_line), ProofLevel::Temporary));
            }
        vector<ProofLiteralOrFlag> member_flags;
        for (auto q : members)
            member_flags.push_back(*c[i][q]);
        static_cast<void>(recover_am1_from_pairs(logger, member_flags, at_most_ones, ProofLevel::Temporary));
    }

    // Pin the state flags to c. One guard per live state flag, with
    // e -> (c -> st), each introduced on its own; then a single red sets every
    // guard, with a witness taking the state flags to c, and dead ones to 0.
    // Its goals are the OPB's rows over c, derived above. The other direction
    // is not needed: once c picks a state, the OPB's at-most-one on the state
    // flags clears the rest.
    logger.emit_proof_comment("Regular: canonical run, pin the state flags to it");
    vector<pair<ProofLiteralOrFlag, ProofLiteralOrFlag>> witness;
    WPBSum all_guards;
    long long guard_count = 0;
    vector<ProofFlag> guards;
    for (size_t i = 1; i <= n; ++i)
        for (long q = 0; q < num_states; ++q) {
            if (! live[i].contains(q) || is_constant(*c[i][q])) {
                witness.emplace_back(st[i][q], FalseLiteral{});
                continue;
            }
            auto guard = logger.create_proof_flag("rege");
            WPBSum pin = WPBSum{} + 1_i * ! guard + 1_i * st[i][q];
            add_term_to(pin, 1_i, ! *c[i][q]);
            logger.emit_red_proof_line(move(pin) >= 1_i, {{guard, FalseLiteral{}}}, ProofLevel::Top);
            witness.emplace_back(st[i][q], *c[i][q]);
            guards.push_back(guard);
            all_guards += 1_i * guard;
            ++guard_count;
        }
    for (const auto & guard : guards)
        witness.emplace_back(guard, TrueLiteral{});
    if (guard_count > 0)
        logger.emit_red_proof_line(move(all_guards) >= Integer{guard_count}, witness, ProofLevel::Top);
}
