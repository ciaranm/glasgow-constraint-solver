#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/innards/propagators.hh>
#include <list>
#include <utility>

using std::pair;
using std::unique_ptr;

using namespace gcs;
using namespace gcs::innards;

namespace
{
}

auto CircuitSCC::clone() const -> unique_ptr<Constraint>
{
    return make_unique<CircuitSCC>(_succ, _gac_all_different);
}

auto CircuitSCC::install(Propagators & propagators, State &) && -> void
{
    // TODO: Placeholder
    Triggers triggers;
    triggers.on_change = {_succ.begin(), _succ.end()};
    propagators.install(
        [](State &) -> pair<Inference, PropagatorState> {
            return pair{Inference::NoChange, PropagatorState::Enable};
        },
        triggers,
        "circuit");
}
