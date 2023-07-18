#include <gcs/constraints/mdd.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>

#include <any>
#include <cstdio>
#include <fstream>
#include <functional>
#include <iostream>
#include <list>
#include <optional>
#include <set>
#include <sstream>
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

namespace
{

    auto propagate_mdd(std::vector<IntegerVariableID> vars,
        const long num_nodes,
        const std::vector<long> & level,
        const long num_edges,
        const std::vector<long> & from,
        const std::vector<std::vector<Integer>> & label,
        const std::vector<long> & to,
        State & state) -> Inference
    {
        return Inference::NoChange;
    }
}

MDD::MDD(std::vector<IntegerVariableID> v,
    long n,
    std::vector<long> le,
    long ne,
    std::vector<long> f,
    std::vector<std::vector<Integer>> la,
    std::vector<long> t) :
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
    if (propagators.want_definitions()) {
        // PB encoding
    }

    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    propagators.install([v = _vars, n = _num_nodes, le = _level, ne = _num_edges, f = _from, la = _label, t = _to](State & state) -> pair<Inference, PropagatorState> {
        return pair{propagate_mdd(v, n, le, ne, f, la, t, state), PropagatorState::Enable};
    },
        triggers, "MDD");
}

auto MDD::describe_for_proof() -> string
{
    return "MDD";
}
