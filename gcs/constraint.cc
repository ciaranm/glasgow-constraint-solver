#include <gcs/constraint.hh>
#include <gcs/exception.hh>

using std::string;

using namespace gcs;

Constraint::~Constraint() = default;

namespace gcs {
    auto as_string(const ConstraintName & name) -> std::string {
        return std::visit([](const auto & n) { return n.as_string(); }, name);
    }
}
