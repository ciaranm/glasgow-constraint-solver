#include <gcs/constraints/innards/task_presence.hh>
#include <gcs/exception.hh>

#include <string>

using std::optional;
using std::string;
using std::string_view;

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::task_presence(const optional<IntegerVariableID> & posted, string_view constraint_name) -> TaskPresence
{
    if (! posted)
        return TaskPresence{};

    if (! is_constant_variable(*posted))
        return TaskPresence{*posted, false};

    auto value = constant_value_of(*posted);
    if (value == 1_i)
        return TaskPresence{};
    if (value == 0_i)
        return TaskPresence{*posted, true};
    throw InvalidProblemDefinitionException{string{constraint_name} + ": presences must be within {0, 1}"};
}
