#include <gcs/constraints/parity.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <optional>

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::pair;
using std::string;
using std::unique_ptr;
using std::vector;

namespace
{
    auto to_lits(const vector<IntegerVariableID> & vars) -> Literals
    {
        Literals result;
        result.reserve(vars.size());
        for (auto & v : vars)
            result.emplace_back(v != 0_i);
        return result;
    }
}

ParityOdd::ParityOdd(const vector<IntegerVariableID> & vars) :
    ParityOdd(to_lits(vars))
{
}

ParityOdd::ParityOdd(Literals l) :
    _lits(move(l))
{
}

auto ParityOdd::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ParityOdd>(_lits);
}

auto ParityOdd::install(Propagators & propagators, State &, ProofModel * const optional_model) && -> void
{
    if (optional_model) {
        PseudoBooleanTerm acc = FalseLiteral{}, not_acc = TrueLiteral{};
        for (const auto & l : _lits) {
            auto new_acc = optional_model->create_proof_flag("xor");

            optional_model->add_constraint("ParityOdd", "xor", WeightedPseudoBooleanSum{} + 1_i * acc + 1_i * l + 1_i * ! new_acc >= 1_i);
            optional_model->add_constraint("ParityOdd", "xor", WeightedPseudoBooleanSum{} + 1_i * not_acc + 1_i * ! l + 1_i * ! new_acc >= 1_i);
            optional_model->add_constraint("ParityOdd", "xor", WeightedPseudoBooleanSum{} + 1_i * not_acc + 1_i * l + 1_i * new_acc >= 1_i);
            optional_model->add_constraint("ParityOdd", "xor", WeightedPseudoBooleanSum{} + 1_i * acc + 1_i * ! l + 1_i * new_acc >= 1_i);

            acc = new_acc;
            not_acc = ! new_acc;
        }
        optional_model->add_constraint("ParityOdd", "result", WeightedPseudoBooleanSum{} + 1_i * acc >= 1_i);
    }

    Triggers triggers;
    for (const auto & l : _lits) {
        overloaded{
            [&](const TrueLiteral &) {},
            [&](const FalseLiteral &) {},
            [&](const IntegerVariableCondition & cond) {
                switch (cond.op) {
                case VariableConditionOperator::NotEqual:
                case VariableConditionOperator::Equal:
                    triggers.on_change.push_back(cond.var);
                    break;
                case VariableConditionOperator::Less:
                case VariableConditionOperator::GreaterEqual:
                    triggers.on_bounds.push_back(cond.var);
                    break;
                }
            }}
            .visit(l);
    }

    propagators.install([lits = _lits](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        long how_many_0 = 0, how_many_1 = 0, how_many_unknown = 0;
        optional<Literal> an_unknown;
        HalfReifyOnConjunctionOf reason;
        for (const auto & l : lits) {
            switch (state.test_literal(l)) {
            case LiteralIs::DefinitelyTrue:
                reason.push_back(l);
                ++how_many_1;
                break;

            case LiteralIs::DefinitelyFalse:
                reason.push_back(! l);
                ++how_many_0;
                break;

            case LiteralIs::Undecided:
                // two or more undecided literals? can't do anything
                if (++how_many_unknown > 1)
                    return PropagatorState::Enable;
                an_unknown = l;
                break;
            }
        }

        if (0 == how_many_unknown) {
            if (how_many_1 % 2 == 1)
                return PropagatorState::DisableUntilBacktrack;
            else
                inference.contradiction(logger, JustifyUsingRUP{}, ReasonFunction{[=]() { return reason; }});
        }
        else {
            if (how_many_1 % 2 == 1) {
                inference.infer(logger, ! *an_unknown, JustifyUsingRUP{}, ReasonFunction{[=]() { return reason; }});
                return PropagatorState::DisableUntilBacktrack;
            }
            else {
                inference.infer(logger, *an_unknown, JustifyUsingRUP{}, ReasonFunction{[=]() { return reason; }});
                return PropagatorState::DisableUntilBacktrack;
            }
        }
    },
        triggers, "parity odd");
}
