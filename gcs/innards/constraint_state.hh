#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_STATE_HH
#include <gcs/integer.hh>
#include <set>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <any>

using namespace gcs;
struct RegularGraph
{
    std::vector<std::unordered_map<Integer, std::set<long>>> states_supporting;
    std::vector<std::vector<std::unordered_map<long, std::unordered_set<Integer>>>> out_edges;
    std::vector<std::vector<long>> out_deg;
    std::vector<std::vector<std::unordered_map<long, std::unordered_set<Integer>>>> in_edges;
    std::vector<std::vector<long>> in_deg;
    std::vector<std::set<long>> nodes;
    bool initialised;

    explicit RegularGraph(long num_vars, long num_states) :
        states_supporting(std::vector<std::unordered_map<Integer, std::set<long>>>(num_vars)),
        out_edges(std::vector<std::vector<std::unordered_map<long, std::unordered_set<Integer>>>>(num_vars, std::vector<std::unordered_map<long, std::unordered_set<Integer>>>(num_states))),
        out_deg(std::vector<std::vector<long>>(num_vars, std::vector<long>(num_states, 0))),
        in_edges(std::vector<std::vector<std::unordered_map<long, std::unordered_set<Integer>>>>(num_vars + 1, std::vector<std::unordered_map<long, std::unordered_set<Integer>>>(num_states))),
        in_deg(std::vector<std::vector<long>>(num_vars + 1, std::vector<long>(num_states, 0))),
        nodes(std::vector<std::set<long>>(num_vars + 1)),
        initialised(false)
    {
    }
};

// In case we want to add other kinds of constraint state
using ConstraintState = std::any;

#endif