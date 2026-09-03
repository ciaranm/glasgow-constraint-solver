#include <gcs/constraint.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>

using namespace gcs;
using namespace gcs::innards;

Constraint::~Constraint() = default;

auto Constraint::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    const auto propagators_before = propagators.number_of_propagators();

    if (prepare(propagators, initial_state, optional_model)) {
        if (optional_model)
            define_proof_model(*optional_model, initial_state);

        install_propagators(propagators);
    }

    // Label whatever got installed with this constraint's type, for the
    // per-constraint-type propagator report. Here rather than at each
    // Propagators::install() call site because this is the one function every
    // install path runs through, and because a child constraint --- installed
    // from inside prepare(), and so already labelled by its own recursion
    // through here --- then keeps its own type rather than inheriting ours.
    // A prepare() that returned false is included: it may have delegated the
    // whole constraint to a child.
    if (propagators.number_of_propagators() != propagators_before)
        propagators.note_propagator_types(propagators_before, constraint_type());
}

auto gcs::as_string(const ConstraintID & constraint_id) -> std::string
{
    return visit([](const auto & n) { return n.as_string(); }, constraint_id);
}
