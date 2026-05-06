#include <gcs/constraints/innards/triggers.hh>

#include <util/overloaded.hh>

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::add_trigger_for(Triggers & triggers, const Literal & lit) -> void
{
    overloaded{
        [&](const IntegerVariableCondition & cond) {
            switch (cond.op) {
                using enum VariableConditionOperator;
            case Equal:
            case NotEqual:
                triggers.on_change.push_back(cond.var);
                break;
            case Less:
            case GreaterEqual:
                triggers.on_bounds.push_back(cond.var);
                break;
            }
        },
        [](const TrueLiteral &) {},
        [](const FalseLiteral &) {}}
        .visit(lit);
}
