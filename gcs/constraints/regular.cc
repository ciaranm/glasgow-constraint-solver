#include <gcs/constraints/regular.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <algorithm>
#include <functional>
#include <list>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <type_traits>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::pair;
using std::string;
using std::unique_ptr;
using std::vector;
using std::visit;

Regular::Regular(vector<IntegerVariableID> v, long n, vector<vector<long>> t, vector<long> f) :
        _vars(move(v)),
        _num_states(n),
        _transitions(t),
        _final_states(f)
{
}

auto Regular::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Regular>(_vars, _num_states, _transitions, _final_states);
}

auto Regular::install(Propagators & propagators, State & initial_state) && -> void
{
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    propagators.install([&](State & state) -> pair<Inference, PropagatorState> {
        //TODO
    }, triggers, "regular");
}

auto Regular::describe_for_proof() -> string
{
    return "regular";
}


