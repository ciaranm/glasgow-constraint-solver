#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>

#include <list>
#include <map>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::pair;
using std::unique_ptr;

auto CircuitPrevent::clone() const -> unique_ptr<Constraint>
{
    return make_unique<CircuitPrevent>(_succ, _gac_all_different);
}

auto CircuitPrevent::install(Propagators & propagators, State &) && -> void
{
    // TODO: Placeholder
    Triggers triggers;
    triggers.on_instantiated = {_succ.begin(), _succ.end()};
    propagators.install(
        [](State &) -> pair<Inference, PropagatorState> {
            return pair{
                Inference::NoChange,
                PropagatorState::Enable};
        },
        triggers,
        "circuit");
}
