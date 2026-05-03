#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/exception.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::test_reification_condition(const State & state, const ReificationCondition & cond)
    -> EvaluatedReificationCondition
{
    return overloaded{
        [&](const reif::MustHold &) -> EvaluatedReificationCondition { return evaluated_reif::MustHold{TrueLiteral{}}; },
        [&](const reif::MustNotHold &) -> EvaluatedReificationCondition { return evaluated_reif::MustNotHold{TrueLiteral{}}; },
        [&](const reif::If & cond) -> EvaluatedReificationCondition {
            switch (state.test_literal(cond.cond)) {
            case LiteralIs::DefinitelyTrue: return evaluated_reif::MustHold{cond.cond};
            case LiteralIs::DefinitelyFalse: return evaluated_reif::Deactivated{};
            case LiteralIs::Undecided: return evaluated_reif::Undecided{cond.cond, false, true, false};
            }
            throw NonExhaustiveSwitch{};
        },
        [&](const reif::NotIf & cond) -> EvaluatedReificationCondition {
            switch (state.test_literal(cond.cond)) {
            case LiteralIs::DefinitelyTrue: return evaluated_reif::MustNotHold{cond.cond};
            case LiteralIs::DefinitelyFalse: return evaluated_reif::Deactivated{};
            case LiteralIs::Undecided: return evaluated_reif::Undecided{cond.cond, false, false, true};
            }
            throw NonExhaustiveSwitch{};
        },
        [&](const reif::Iff & cond) -> EvaluatedReificationCondition {
            switch (state.test_literal(cond.cond)) {
            case LiteralIs::DefinitelyTrue: return evaluated_reif::MustHold{cond.cond};
            case LiteralIs::DefinitelyFalse: return evaluated_reif::MustNotHold{! cond.cond};
            case LiteralIs::Undecided: return evaluated_reif::Undecided{cond.cond, true, true, false};
            }
            throw NonExhaustiveSwitch{};
        }}
        .visit(cond);
}
