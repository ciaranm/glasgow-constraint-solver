#include <gcs/constraints/regular.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>

#include <functional>
#include <list>
#include <optional>
#include <set>
#include <unordered_map>
#include <utility>
#include <variant>

// DEBUG ONLY -- REMOVE
#include <iostream>
using std::cout;
using std::endl;
// --------------------

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::pair;
using std::set;
using std::string;
using std::unique_ptr;
using std::unordered_map;
using std::vector;
using std::visit;

namespace
{
    auto propagate_regular(const vector<IntegerVariableID> & vars,
        const vector<Integer> & symbols,
        const long num_states,
        const vector<vector<long>> & transitions,
        const vector<long> & final_states,
        State & state) -> Inference
    {
        const auto num_vars = vars.size();
        const auto num_symbols = symbols.size();

        // Might be a better way to initialise these ?
        // -- or better data structures.
        vector<unordered_map<Integer, set<long>>> states_supporting(num_vars);

        vector<vector<vector<long>>> out_edges(num_vars, vector<vector<long>>(num_states));
        vector<vector<long>> out_deg(num_vars, vector<long>(num_states, 0));
        vector<vector<vector<long>>> in_edges(num_vars + 1, vector<vector<long>>(num_states));
        vector<vector<long>> in_deg(num_vars + 1, vector<long>(num_states, 0));
        vector<set<long>> graph_nodes(num_vars + 1);

        // Forward phase: accumulate
        graph_nodes[0].insert(0);
        for (unsigned long i = 0; i < num_vars; ++i) {
            state.for_each_value(vars[i], [&](Integer val) -> void {
                for (const auto & q : graph_nodes[i]) {
                    if (transitions[q][val.raw_value] != -1) {
                        states_supporting[i][val].insert(q);
                        graph_nodes[i + 1].insert(transitions[q][val.raw_value]);
                    }
                }
            });
        }
        for (const auto & f : final_states)
            graph_nodes[num_vars].insert(f);

        // Backward phase: validate
        for (long i = num_vars - 1; i >= 0; --i) {
            unordered_map<long, bool> state_is_support;
            for (const auto & q : graph_nodes[i])
                state_is_support[q] = false;

            state.for_each_value(vars[i], [&](Integer val) -> void {
                for (const auto & q : states_supporting[i][val]) {
                    if (graph_nodes[i + 1].contains(transitions[q][val.raw_value])) {
                        out_edges[i][q].emplace_back(transitions[q][val.raw_value]);
                        out_deg[i][q]++;
                        in_edges[i + 1][transitions[q][val.raw_value]].emplace_back(q);
                        in_deg[i][transitions[q][val.raw_value]]++;
                        state_is_support[q] = true;
                    }
                    else {
                        states_supporting[i][val].erase(q);
                    }
                }
            });
        }
        bool changed = false;
        bool contradiction = false;

        // Clean up domains
        for (unsigned long i = 0; i < num_vars; ++i) {
            state.for_each_value(vars[i], [&](Integer val) -> void {
                if (states_supporting[i][val].empty()) {
                    // TODO: Proof logging
                    switch (state.infer_not_equal(vars[i], val, NoJustificationNeeded{})) {
                    case Inference::Contradiction:
                        contradiction = true;
                    case Inference::Change:
                        changed = true;
                        break;
                    case Inference::NoChange:
                        break;
                    }
                }
            });
        }

        if (contradiction) {
            return Inference::Contradiction;
        }
        else if (changed) {
            return Inference::Change;
        }
        return Inference::NoChange;
    }
}
Regular::Regular(vector<IntegerVariableID> v, vector<Integer> s, long n, vector<vector<long>> t, vector<long> f) :
    _vars(move(v)),
    _symbols(move(s)),
    _num_states(n),
    _transitions(t),
    _final_states(f)
{
}

auto Regular::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Regular>(_vars, _symbols, _num_states, _transitions, _final_states);
}

auto Regular::install(Propagators & propagators, State & initial_state) && -> void
{
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    propagators.install([v = _vars,
                            s = _symbols,
                            n = _num_states,
                            t = _transitions,
                            f = _final_states](State & state) -> pair<Inference, PropagatorState> {
        return pair{propagate_regular(v, s, n, t, f, state), PropagatorState::Enable};
    },
        triggers, "regular");
}

auto Regular::describe_for_proof() -> string
{
    return "regular";
}
