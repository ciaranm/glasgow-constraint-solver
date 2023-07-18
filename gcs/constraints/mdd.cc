#include <gcs/constraints/mdd.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>

#include <any>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <list>
#include <optional>
#include <set>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::any_cast;
using std::cmp_less;
using std::cmp_not_equal;
using std::cout;
using std::endl;
using std::fstream;
using std::getline;
using std::ifstream;
using std::ios;
using std::make_pair;
using std::make_unique;
using std::move;
using std::ofstream;
using std::optional;
using std::pair;
using std::rename;
using std::set;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;
using std::visit;
// To make it easier to change this later
using NodeSet = set<long>;

namespace
{
    // Doing this again (c.f. SmartTable) - eventually we'll want to replace this with something more efficient
    // Perhaps not storing every value in the domain explicitly!
    using VariableDomainMap = unordered_map<IntegerVariableID, set<Integer>>;

    auto traverse(long current_node,
        const vector<IntegerVariableID> vars,
        const vector<long> & level,
        const vector<vector<Integer>> & label,
        const vector<long> & from,
        const vector<long> & to,
        NodeSet & reach_final,
        NodeSet & failed,
        VariableDomainMap & unsupported,
        const vector<vector<long>> & out_edges,
        State & state) -> bool
    {
        if (reach_final.contains(current_node)) {
            return true;
        }
        else if (failed.contains(current_node)) {
            return false;
        }
        for (auto edge : out_edges[current_node]) {
            for (auto val : label[edge]) {
                auto var = vars[level[from[edge]]];
                if (state.in_domain(var, val)) {
                    if (traverse(to[edge], vars, level, label,
                            from, to, reach_final, failed, unsupported, out_edges, state)) {
                        unsupported[var].erase(val);
                        reach_final.insert(current_node);

                        // Shortcut if all values below here are unsupported
                        bool should_shortcut = true;
                        for (long i = level[from[edge]]; i < vars.size(); i++) {
                            if (! unsupported[vars[i]].empty()) {
                                should_shortcut = false;
                            }
                        }
                        if (should_shortcut) break;
                    }
                }
            }
        }
        if (! reach_final.contains(current_node)) {
            failed.insert(current_node);
            return false;
        }
        return true;
    }

    // Non-incremental, non-efficient mddc-type algorithm
    auto propagate_mdd(const vector<IntegerVariableID> vars,
        const long & num_nodes,
        const vector<long> & level,
        const vector<vector<Integer>> & label,
        const vector<long> & from,
        const vector<long> & to,
        const ConstraintStateHandle & failed_idx,
        const vector<vector<long>> & out_edges,
        State & state) -> Inference
    {
        // Currently using sets for eliminated nodes and nodes than can reach the final state
        // TODO: use sparse set, or at least something more efficient
        auto & failed = any_cast<NodeSet &>(state.get_constraint_state(failed_idx));
        auto reach_final = NodeSet{static_cast<long>(num_nodes - 1)};

        VariableDomainMap unsupported{};
        // Here's this dodgy bit of code again to painstakingly extract every value from every domain
        // TODO: optimise
        for (const auto & var : vars) {
            state.for_each_value(var, [&](Integer value) {
                unsupported[var].insert(value);
            });
        }
        traverse(0, vars, level, label, from, to, reach_final, failed, unsupported, out_edges, state);

        // Actually make the inferences
        auto result = Inference::NoChange;
        for (const auto & var : vars) {
            for (const auto & value : unsupported[var]) {
                increase_inference_to(result, state.infer_not_equal(var, value, NoJustificationNeeded{}));
            }
        }
        return result;
    }
}

MDD::MDD(vector<IntegerVariableID> v,
    long n,
    vector<long> le,
    long ne,
    vector<long> f,
    vector<vector<Integer>> la,
    vector<long> t) :
    _vars(move(v)),
    _num_nodes(n),
    _level(move(le)),
    _num_edges(ne),
    _from(move(f)),
    _label(move(la)),
    _to(move(t))
{
}

auto MDD::clone() const -> unique_ptr<Constraint>
{
    return make_unique<MDD>(_vars, _num_nodes, _level, _num_edges, _from, _label, _to);
}

auto MDD::install(Propagators & propagators, State & initial_state) && -> void
{
    // TODO: sanity check: has the user given something vaguely sensible for the MDD representation?

    if (propagators.want_definitions()) {
        // TODO: PB encoding
    }

    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    NodeSet failed{};
    auto failed_idx = initial_state.add_constraint_state(failed);
    vector<vector<long>> out_edges(_num_nodes, vector<long>{});
    for (int i = 0; i < _num_edges; i++) {
        out_edges[_from[i]].emplace_back(i);
    }
    propagators.install([v = _vars, n = _num_nodes, le = _level, f = _from, la = _label, t = _to, fi = failed_idx, o = out_edges](State & state)
                            -> pair<Inference, PropagatorState> {
        return pair{propagate_mdd(v, n, le, la, f, t, fi, o, state), PropagatorState::Enable};
    },
        triggers, "MDD");
}

auto MDD::describe_for_proof() -> string
{
    return "MDD";
}
