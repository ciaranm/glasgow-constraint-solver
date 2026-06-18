#include <gcs/constraint.hh>
#include <gcs/exception.hh>

using namespace gcs;

Constraint::~Constraint() = default;

auto gcs::as_string(const ConstraintID & constraint_id) -> std::string
{
    return visit([](const auto & n) { return n.as_string(); }, constraint_id);
}
