#include <gcs/constraint.hh>
#include <gcs/exception.hh>

using std::string;
using std::variant;

using namespace gcs;

Constraint::~Constraint() = default;

namespace gcs {
    auto as_string(const ConstraintID & constraint_id) -> std::string {
        return visit([](const auto & id) { return id.as_string(); }, constraint_id);
    }
}
