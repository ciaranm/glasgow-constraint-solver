#include <gcs/constraints/innards/cake_truthiness.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/parity/hints.hh>
#include <gcs/constraints/parity/parity.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>
#include <util/enumerate.hh>

#include <optional>
#include <sstream>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::move;
using std::nullopt;
using std::optional;
using std::string;
using std::stringstream;
using std::to_string;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

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

ParityOdd::ParityOdd(const vector<IntegerVariableID> & vars) : ParityOdd(to_lits(vars))
{
}

ParityOdd::ParityOdd(Literals l) : _lits(move(l))
{
}

auto ParityOdd::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ParityOdd>(_lits);
}

auto ParityOdd::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto ParityOdd::define_proof_model(ProofModel & model) -> void
{
    // cake_pb_cp's accumulator scheme, over the literals as cake reads them
    // (each operand tuple maps to the same ge / eq atom our proof uses):
    // x[id][0] channels the parity bit (always the constant 1 here, which cake
    // carries as its pinned-true n[1][ge1] atom; our rows fold it), x[id][k] =
    // x[id][k-1] XOR the k'th literal via four labelled clauses, and the acc
    // row pins the final accumulator to 0, i.e. 1 XOR (parity of the literals)
    // = 0.
    PseudoBooleanTerm acc = FalseLiteral{}, not_acc = TrueLiteral{};
    auto x0 = model.create_proof_flag(_constraint_id, vector<long long>{0}, nullopt);
    model.add_labelled_constraint(_constraint_id, "0ge", WPBSum{} + 1_i * TrueLiteral{} + -1_i * x0 >= 0_i);
    model.add_labelled_constraint(_constraint_id, "0le", WPBSum{} + 1_i * x0 + -1_i * TrueLiteral{} >= 0_i);
    acc = x0;
    not_acc = ! x0;
    for (const auto & [k, l] : enumerate(_lits)) {
        auto new_acc = model.create_proof_flag(_constraint_id, vector<long long>{static_cast<long long>(k) + 1}, nullopt);
        auto stem = to_string(k + 1);
        model.add_labelled_constraint(_constraint_id, stem + "_0_0", WPBSum{} + 1_i * acc + 1_i * l + 1_i * ! new_acc >= 1_i);
        model.add_labelled_constraint(_constraint_id, stem + "_1_1", WPBSum{} + 1_i * not_acc + 1_i * ! l + 1_i * ! new_acc >= 1_i);
        model.add_labelled_constraint(_constraint_id, stem + "_1_0", WPBSum{} + 1_i * not_acc + 1_i * l + 1_i * new_acc >= 1_i);
        model.add_labelled_constraint(_constraint_id, stem + "_0_1", WPBSum{} + 1_i * acc + 1_i * ! l + 1_i * new_acc >= 1_i);
        acc = new_acc;
        not_acc = ! new_acc;
    }
    model.add_labelled_constraint(_constraint_id, "acc", WPBSum{} + -1_i * acc >= 0_i);
}

auto ParityOdd::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (const auto & l : _lits)
        add_trigger_for(triggers, l);

    propagators.install(
        constraint_id(),
        [lits = _lits, owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            long how_many_1 = 0, how_many_unknown = 0;
            optional<Literal> an_unknown;
            ReasonLiterals reason;
            for (const auto & l : lits) {
                switch (state.test_literal(l)) {
                    using enum LiteralIs;
                case DefinitelyTrue:
                    reason.push_back(l);
                    ++how_many_1;
                    break;

                case DefinitelyFalse: reason.push_back(! l); break;

                case Undecided:
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
                    inference.contradiction(logger, JustifyUsingRUP{hints::Parity{owner}}, ExplicitReason{reason});
            }
            else {
                if (how_many_1 % 2 == 1) {
                    inference.infer(logger, ! *an_unknown, JustifyUsingRUP{hints::Parity{owner}}, ExplicitReason{reason});
                    return PropagatorState::DisableUntilBacktrack;
                }
                else {
                    inference.infer(logger, *an_unknown, JustifyUsingRUP{hints::Parity{owner}}, ExplicitReason{reason});
                    return PropagatorState::DisableUntilBacktrack;
                }
            }
        },
        triggers);
}
auto ParityOdd::constraint_type() const -> std::string
{
    return "parity";
}

auto ParityOdd::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    // cake_pb_cp encodes parity as `parity ((Z op v) ...) (Y op v)` meaning
    // Y = XOR(operands). ParityOdd is the bare odd-parity assertion, so the
    // output is the statically-true tuple (1 >= 1).
    std::vector<SExpr> lits;
    for (const auto & lit : _lits)
        lits.push_back(reify_tuple_term(lit, tracker));
    return SExpr::list(
        {SExpr::atom(as_string(_constraint_id)), SExpr::atom("parity"), SExpr::list(std::move(lits)), reify_tuple_term(TrueLiteral{}, tracker)});
}
