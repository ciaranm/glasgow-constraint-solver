#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_STATE_HH
#include <gcs/integer.hh>
#include <set>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using std::pair;
using std::set;
using std::unordered_map;
using std::unordered_set;
using std::vector;

using namespace gcs;
struct RegularGraph
{
    vector<unordered_map<Integer, set<long>>> states_supporting;
    vector<vector<unordered_map<long, unordered_set<Integer>>>> out_edges;
    vector<vector<long>> out_deg;
    vector<vector<unordered_map<long, unordered_set<Integer>>>> in_edges;
    vector<vector<long>> in_deg;
    vector<set<long>> nodes;

    explicit RegularGraph(long num_vars, long num_states) :
        states_supporting(vector<unordered_map<Integer, set<long>>>(num_vars)),
        out_edges(vector<vector<unordered_map<long, unordered_set<Integer>>>>(num_vars, vector<unordered_map<long, unordered_set<Integer>>>(num_states))),
        out_deg(vector<vector<long>>(num_vars, vector<long>(num_states, 0))),
        in_edges(vector<vector<unordered_map<long, unordered_set<Integer>>>>(num_vars + 1, vector<unordered_map<long, unordered_set<Integer>>>(num_states))),
        in_deg(vector<vector<long>>(num_vars + 1, vector<long>(num_states, 0))),
        nodes(vector<set<long>>(num_vars + 1))
    {
    }
};

// In case we want to add other kinds of constraint state
using ConstraintState = std::variant<RegularGraph>;

#endif