#include <gcs/constraints/regular/regular_bacchus.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <any>
#include <memory>
#include <set>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::any_cast;
using std::make_shared;
using std::make_unique;
using std::move;
using std::set;
using std::shared_ptr;
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
    auto find_transition(const unordered_map<Integer, long> & state_transitions, Integer val) -> long
    {
        auto it = state_transitions.find(val);
        if (it == state_transitions.end())
            return -1L;
        return it->second;
    }

    // Per-call support graph: identical layout to Regular's, but we never
    // emit proof lines from here. The graph is only used by the propagator
    // to decide which value-prunings to make; the proof DB already contains
    // the Bacchus encoding from the initialiser, so RUP / NoJustNeeded
    // closes everything via UP without per-call intermediates.
    struct RegularGraph
    {
        vector<unordered_map<Integer, set<long>>> states_supporting;
        vector<vector<unordered_map<long, unordered_set<Integer>>>> out_edges;
        vector<vector<long>> out_deg;
        vector<vector<unordered_map<long, unordered_set<Integer>>>> in_edges;
        vector<vector<long>> in_deg;
        vector<set<long>> nodes;
        bool initialised = false;

        explicit RegularGraph(long num_vars, long num_states) :
            states_supporting(num_vars),
            out_edges(num_vars, vector<unordered_map<long, unordered_set<Integer>>>(num_states)),
            out_deg(num_vars, vector<long>(num_states, 0)),
            in_edges(num_vars + 1, vector<unordered_map<long, unordered_set<Integer>>>(num_states)),
            in_deg(num_vars + 1, vector<long>(num_states, 0)),
            nodes(num_vars + 1)
        {
        }
    };

    auto initialise_graph(RegularGraph & graph, const vector<IntegerVariableID> & vars,
        const long num_states, const vector<unordered_map<Integer, long>> & transitions,
        const vector<long> & final_states, const State & state) -> void
    {
        auto num_vars = vars.size();

        graph.nodes[0].insert(0);
        for (size_t i = 0; i < num_vars; ++i) {
            for (auto val : state.each_value_immutable(vars[i])) {
                for (const auto & q : graph.nodes[i]) {
                    auto next_q = find_transition(transitions[q], val);
                    if (next_q != -1) {
                        graph.states_supporting[i][val].insert(q);
                        graph.nodes[i + 1].insert(next_q);
                    }
                }
            }
        }

        set<long> reachable_final;
        for (auto f : final_states)
            if (graph.nodes[num_vars].contains(f))
                reachable_final.insert(f);
        graph.nodes[num_vars] = reachable_final;

        for (long i = static_cast<long>(num_vars) - 1; i >= 0; --i) {
            vector<char> state_is_support(num_states, 0);
            for (auto val : state.each_value_mutable(vars[i])) {
                set<long> states = graph.states_supporting[i][val];
                for (const auto & q : states) {
                    auto next_q = find_transition(transitions[q], val);
                    if (next_q != -1 && graph.nodes[i + 1].contains(next_q)) {
                        graph.out_edges[i][q][next_q].emplace(val);
                        graph.out_deg[i][q]++;
                        graph.in_edges[i + 1][next_q][q].emplace(val);
                        graph.in_deg[i + 1][next_q]++;
                        state_is_support[q] = 1;
                    }
                    else {
                        graph.states_supporting[i][val].erase(q);
                    }
                }
            }
            set<long> gn = graph.nodes[i];
            for (const auto & q : gn)
                if (! state_is_support[q])
                    graph.nodes[i].erase(q);
        }

        graph.initialised = true;
    }

    auto decrement_outdeg(RegularGraph & graph, const long i, const long k) -> void
    {
        graph.out_deg[i][k]--;
        if (graph.out_deg[i][k] == 0 && i > 0) {
            for (const auto & edge : graph.in_edges[i][k]) {
                auto l = edge.first;
                graph.out_edges[i - 1][l].erase(k);
                for (const auto & val : edge.second) {
                    graph.states_supporting[i - 1][val].erase(l);
                    decrement_outdeg(graph, i - 1, l);
                }
            }
            graph.in_edges[i][k] = {};
        }
    }

    auto decrement_indeg(RegularGraph & graph, const long i, const long k) -> void
    {
        graph.in_deg[i][k]--;
        if (graph.in_deg[i][k] == 0 && std::cmp_less(i, graph.in_deg.size() - 1)) {
            for (const auto & edge : graph.out_edges[i][k]) {
                auto l = edge.first;
                graph.in_edges[i + 1][l].erase(k);
                for (const auto & val : edge.second) {
                    graph.states_supporting[i][val].erase(k);
                    decrement_indeg(graph, i + 1, l);
                }
            }
            graph.out_edges[i][k] = {};
        }
    }

    auto propagate_regular(const vector<IntegerVariableID> & vars,
        const long num_states,
        const vector<unordered_map<Integer, long>> & transitions,
        const vector<long> & final_states,
        const ConstraintStateHandle & graph_handle,
        const State & state, auto & inference) -> void
    {
        auto & graph = any_cast<RegularGraph &>(state.get_constraint_state(graph_handle));

        if (! graph.initialised)
            initialise_graph(graph, vars, num_states, transitions, final_states, state);

        for (size_t i = 0; i < graph.states_supporting.size(); ++i) {
            for (const auto & val_and_states : graph.states_supporting[i]) {
                auto val = val_and_states.first;
                if (! graph.states_supporting[i][val].empty() && ! state.in_domain(vars[i], val)) {
                    for (const auto & q : graph.states_supporting[i][val]) {
                        auto next_q = find_transition(transitions[q], val);
                        if (graph.out_edges[i][q].contains(next_q)) {
                            graph.out_edges[i][q][next_q].erase(val);
                            if (graph.out_edges[i][q][next_q].empty())
                                graph.out_edges[i][q].erase(next_q);
                        }
                        if (graph.in_edges[i + 1][next_q].contains(q)) {
                            graph.in_edges[i + 1][next_q][q].erase(val);
                            if (graph.in_edges[i + 1][next_q][q].empty())
                                graph.in_edges[i + 1][next_q].erase(q);
                        }
                        decrement_outdeg(graph, static_cast<long>(i), q);
                        decrement_indeg(graph, static_cast<long>(i) + 1, next_q);
                    }
                    graph.states_supporting[i][val] = {};
                }
            }
        }

        for (size_t i = 0; i < graph.states_supporting.size(); ++i) {
            for (auto val : state.each_value_mutable(vars[i])) {
                if (graph.states_supporting[i][val].empty())
                    inference.infer_not_equal(nullptr, vars[i], val, NoJustificationNeeded{}, ReasonFunction{});
            }
        }
    }
}

struct RegularBacchus::Bridge
{
    vector<vector<ProofFlag>> state_at_pos_flags;
    // t_flags[i][q] maps val -> the proof flag representing the transition
    // (state[i]=q, vars[i]=v, state[i+1]=delta(q,v)) all holding. Populated
    // by the initialiser; only used to RUP the AL1s in the same initialiser
    // (and so could be dropped after the initialiser runs, but we keep it
    // attached to the bridge for symmetry with the rest of the codebase).
    vector<vector<unordered_map<Integer, ProofFlag>>> t_flags;
    // OPB-time line numbers needed for the initialiser's pol-derivations:
    //   forward_chain_lines[i][q][val] = the line of
    //     `~state[i][q] + (vars[i]!=val) + state[i+1][delta(q,val)] >= 1`
    //   (only present where delta(q,val) is defined).
    vector<vector<unordered_map<Integer, ProofLine>>> forward_chain_lines;
};

RegularBacchus::RegularBacchus(vector<IntegerVariableID> v, long n, vector<unordered_map<Integer, long>> t, vector<long> f, bool sr) :
    _vars(move(v)),
    _num_states(n),
    _transitions(move(t)),
    _final_states(move(f)),
    _short_reasons(sr)
{
    set<Integer> sym_set;
    for (const auto & state_map : _transitions)
        for (const auto & [val, _] : state_map)
            sym_set.insert(val);
    _symbols.assign(sym_set.begin(), sym_set.end());
}

RegularBacchus::RegularBacchus(vector<IntegerVariableID> v, long n, vector<vector<long>> transitions, vector<long> f, bool sr) :
    _vars(move(v)),
    _num_states(n),
    _transitions(vector<unordered_map<Integer, long>>(n, unordered_map<Integer, long>{})),
    _final_states(move(f)),
    _short_reasons(sr)
{
    for (size_t i = 0; i < transitions.size(); ++i)
        for (size_t j = 0; j < transitions[i].size(); ++j)
            if (transitions[i][j] != -1)
                _transitions[i][Integer(j)] = transitions[i][j];
    set<Integer> sym_set;
    for (const auto & state_map : _transitions)
        for (const auto & [val, _] : state_map)
            sym_set.insert(val);
    _symbols.assign(sym_set.begin(), sym_set.end());
}

auto RegularBacchus::symbols() const -> const vector<Integer> &
{
    return _symbols;
}

auto RegularBacchus::clone() const -> unique_ptr<Constraint>
{
    return make_unique<RegularBacchus>(_vars, _num_states, _transitions, _final_states, _short_reasons);
}

auto RegularBacchus::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto RegularBacchus::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _bridge = make_shared<Bridge>();
    _graph_idx = initial_state.add_constraint_state(RegularGraph(static_cast<long>(_vars.size()), _num_states));

    _opb_alphabet.insert(_symbols.begin(), _symbols.end());
    for (const auto & var : _vars)
        for (const auto & val : initial_state.each_value_immutable(var))
            _opb_alphabet.insert(val);

    return true;
}

auto RegularBacchus::define_proof_model(ProofModel & model) -> void
{
    // OPB stays identical to Regular: the human reads DFA semantics, not
    // Bacchus internals. The Bacchus encoding is derived in the initialiser
    // by redundance and RUP.
    auto & flags = _bridge->state_at_pos_flags;
    for (size_t idx = 0; idx <= _vars.size(); ++idx) {
        WPBSum exactly_1_true{};
        flags.emplace_back();
        for (long q = 0; q < _num_states; ++q) {
            flags[idx].emplace_back(model.create_proof_flag(format("state{}is{}", idx, q)));
            exactly_1_true += 1_i * flags[idx][q];
        }
        model.add_constraint(move(exactly_1_true) == 1_i);
    }

    model.add_constraint(WPBSum{} + 1_i * flags[0][0] >= 1_i);

    WPBSum pos_n_states;
    for (const auto & f : _final_states)
        pos_n_states += 1_i * flags[_vars.size()][f];
    model.add_constraint(move(pos_n_states) >= 1_i);

    auto & fwd_lines = _bridge->forward_chain_lines;
    fwd_lines.assign(_vars.size(), vector<unordered_map<Integer, ProofLine>>(_num_states));
    for (size_t idx = 0; idx < _vars.size(); ++idx) {
        for (long q = 0; q < _num_states; ++q) {
            for (const auto & val : _opb_alphabet) {
                auto new_q = find_transition(_transitions[q], val);
                if (new_q == -1) {
                    model.add_constraint(
                        WPBSum{} + 1_i * (_vars[idx] != val) + 1_i * ! flags[idx][q] >= 1_i);
                }
                else {
                    auto line = model.add_constraint(
                        WPBSum{} + 1_i * ! flags[idx][q] + 1_i * (_vars[idx] != val) + 1_i * flags[idx + 1][new_q] >= 1_i);
                    if (line)
                        fwd_lines[idx][q].emplace(val, *line);
                }
            }
        }
    }
}

auto RegularBacchus::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    // One-shot Bacchus scaffolding at search root.
    //   1. t-flags via redundance, fully reifying
    //      t[i][q][v] <=> (vars[i]=v AND state[i]=q AND state[i+1]=delta(q,v)).
    //   2. For each (i, q, v in dom_q): pol(forward_chain + reverse_t_def)
    //      to derive the per-(q,v) intermediate the AL1 RUPs need.
    //   3. Outgoing AL1, incoming AL1, variable-support AL1 via RUP.
    //
    // With those at ProofLevel::Top, every per-call value-pruning the
    // propagator decides becomes RUP-closable purely by UP on the proof DB,
    // so the propagator uses NoJustificationNeeded and writes no proof.
    propagators.install_initialiser(
        [vars = _vars, ns = _num_states, t = _transitions, alphabet = _opb_alphabet, bridge = _bridge](
            State &, auto &, ProofLogger * const logger) -> void {
            if (! logger)
                return;

            auto & ts = bridge->t_flags;
            auto & flags = bridge->state_at_pos_flags;
            const auto & fwd_lines = bridge->forward_chain_lines;
            ts.assign(vars.size(), vector<unordered_map<Integer, ProofFlag>>(ns));

            // Reverse t-def line numbers, indexed by (i, q, val). Used for
            // the per-(q,v) pol steps below.
            vector<vector<unordered_map<Integer, ProofLine>>> rev_tdef_lines(
                vars.size(), vector<unordered_map<Integer, ProofLine>>(ns));

            for (size_t i = 0; i < vars.size(); ++i) {
                for (long q = 0; q < ns; ++q) {
                    for (const auto & val : alphabet) {
                        auto new_q = find_transition(t[q], val);
                        if (new_q == -1)
                            continue;
                        auto [tflag, _f, rev] = logger->create_proof_flag_reifying(
                            WPBSum{} + 1_i * (vars[i] == val) + 1_i * flags[i][q] + 1_i * flags[i + 1][new_q] >= 3_i,
                            format("t{}q{}v{}", i, q, val.raw_value),
                            ProofLevel::Top);
                        ts[i][q].emplace(val, tflag);
                        rev_tdef_lines[i][q].emplace(val, rev);
                    }
                }
            }

            // Per-(i, q, v) pol step: sum the OPB forward chain
            //   ~state[i][q] + ~vars=v + state[i+1][delta(q,v)] >= 1
            // with the t-def reverse line
            //   t[i][q][v] + ~vars=v + ~state[i][q] + ~state[i+1][delta(q,v)] >= 1
            // to derive
            //   2*~state[i][q] + 2*~vars=v + state[i+1][delta(q,v)] + ~state[i+1][delta(q,v)] + t[i][q][v] >= 2.
            // VeriPB's UP cancels the complementary state[i+1][delta]/~state[i+1][delta]
            // pair when checking the AL1 RUPs below, so the per-(q,v) line is
            // what unlocks them.
            for (size_t i = 0; i < vars.size(); ++i) {
                for (long q = 0; q < ns; ++q) {
                    for (const auto & [val, _tflag] : ts[i][q]) {
                        auto fwd_it = fwd_lines[i][q].find(val);
                        auto rev_it = rev_tdef_lines[i][q].find(val);
                        if (fwd_it == fwd_lines[i][q].end() || rev_it == rev_tdef_lines[i][q].end())
                            continue;
                        PolBuilder{}
                            .add(fwd_it->second)
                            .add(rev_it->second)
                            .emit(*logger, ProofLevel::Top);
                    }
                }
            }

            // Outgoing AL1: state[i][q] -> sum_{v: delta(q,v) def} t[i][q][v] >= 1.
            for (size_t i = 0; i < vars.size(); ++i) {
                for (long q = 0; q < ns; ++q) {
                    if (ts[i][q].empty())
                        continue;
                    WPBSum sum;
                    sum += 1_i * ! flags[i][q];
                    for (const auto & [val, tf] : ts[i][q])
                        sum += 1_i * tf;
                    logger->emit_rup_proof_line(move(sum) >= 1_i, ProofLevel::Top);
                }
            }

            // Incoming AL1: state[i+1][q'] -> sum_{(p,v): delta(p,v)=q'} t[i][p][v] >= 1.
            for (size_t i = 0; i < vars.size(); ++i) {
                for (long next_q = 0; next_q < ns; ++next_q) {
                    WPBSum sum;
                    sum += 1_i * ! flags[i + 1][next_q];
                    bool any = false;
                    for (long p = 0; p < ns; ++p) {
                        for (const auto & [val, tf] : ts[i][p]) {
                            if (find_transition(t[p], val) == next_q) {
                                sum += 1_i * tf;
                                any = true;
                            }
                        }
                    }
                    if (any)
                        logger->emit_rup_proof_line(move(sum) >= 1_i, ProofLevel::Top);
                }
            }

            // Variable-support AL1: vars[i]=v -> sum_{q: delta(q,v) def} t[i][q][v] >= 1.
            for (size_t i = 0; i < vars.size(); ++i) {
                for (const auto & val : alphabet) {
                    WPBSum sum;
                    sum += 1_i * (vars[i] != val);
                    bool any = false;
                    for (long q = 0; q < ns; ++q) {
                        auto it = ts[i][q].find(val);
                        if (it != ts[i][q].end()) {
                            sum += 1_i * it->second;
                            any = true;
                        }
                    }
                    if (any)
                        logger->emit_rup_proof_line(move(sum) >= 1_i, ProofLevel::Top);
                }
            }
        });

    propagators.install(
        [v = _vars, ns = _num_states, t = _transitions, fs = _final_states, g = _graph_idx](
            const State & state, auto & inference, ProofLogger * const) -> PropagatorState {
            propagate_regular(v, ns, t, fs, g, state, inference);
            return PropagatorState::Enable;
        },
        triggers);
}

auto RegularBacchus::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} regular_bacchus (", _name);
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") {}\n       (", _num_states);
    for (const auto & sym : symbols())
        print(s, " {}", sym);
    print(s, ")\n       ((");
    for (size_t i = 0; i < _transitions.size(); ++i) {
        print(s, "(");
        for (const auto & tran : _transitions[i]) {
            print(s, " ({} {})", tran.first, tran.second);
        }
        print(s, ")\n        ");
    }
    print(s, "))\n       (");
    for (const auto & f : _final_states)
        print(s, " {}", f);
    print(s, ")");

    return s.str();
}
