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

    auto propagate_mdd() -> Inference
    {
        return Inference::NoChange;
    }
}

MDD::MDD()
{
    // Constructor
}

auto MDD::clone() const -> unique_ptr<Constraint>
{
    return make_unique<MDD>();
}

auto MDD::install(Propagators & propagators, State & initial_state) && -> void
{
    if (propagators.want_definitions()) {
        // PB encoding
    }

    Triggers triggers;
    triggers.on_change = {};

    propagators.install([](State & state) -> pair<Inference, PropagatorState> {
        return pair{propagate_mdd(), PropagatorState::Enable};
    },
        triggers, "MDD");
}

auto MDD::describe_for_proof() -> string
{
    return "MDD";
}
