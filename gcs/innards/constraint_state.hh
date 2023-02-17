#include <vector>
#include <set>
#include <unordered_map>
#include <gcs/integer.hh>

using std::vector;
using std::set;
using std::unordered_map;

using namespace gcs;
struct RegularGraph {
    vector<unordered_map<Integer, set<long>>> states_supporting;
    vector<vector<vector<long>>> out_edges;
    vector<vector<long>> out_deg;
    vector<vector<vector<long>>> in_edges;
    vector<vector<long>> in_deg;
    vector<set<long>> graph_nodes;

    explicit RegularGraph(long num_vars, long num_states) :
            states_supporting(vector<unordered_map<Integer, set<long>>>(num_vars)),
            out_edges(vector<vector<vector<long>>>(num_vars, vector<vector<long>>(num_states))),
            out_deg(vector<vector<long>>(num_vars, vector<long>(num_states, 0))),
            in_edges(vector<vector<vector<long>>>(num_vars + 1, vector<vector<long>>(num_states))),
            in_deg(vector<vector<long>>(num_vars + 1, vector<long>(num_states, 0))),
            graph_nodes(vector<set<long>>(num_vars + 1)) {}
};

// In case we want to add other kinds of constraint state
using ConstraintState = std::variant<RegularGraph>;