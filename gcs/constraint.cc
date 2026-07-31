#include <gcs/constraint.hh>
#include <gcs/exception.hh>

using namespace gcs;
using namespace gcs::innards;

Constraint::~Constraint() = default;

auto Constraint::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model, initial_state);

    install_propagators(propagators);
}

auto gcs::as_string(const ConstraintID & constraint_id) -> std::string
{
    return visit([](const auto & n) { return n.as_string(); }, constraint_id);
}
