#include <gcs/constraints/innards/cake_truthiness.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/parity/hints.hh>
#include <gcs/constraints/parity/parity.hh>
#include <gcs/constraints/parity/parity_chain.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

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

auto ParityOdd::define_proof_model(ProofModel & model, const State &) -> void
{
    static_cast<void>(define_parity_chain(model, _constraint_id, ConstraintProofModelData<ParityOdd>::chain_naming(), _lits));
}

auto ConstraintProofModelData<ParityOdd>::primary_row_role(const ParityOdd &) -> optional<string>
{
    return nullopt;
}

auto ConstraintProofModelData<ParityOdd>::chain_naming() -> ParityChainNaming
{
    return ParityChainNaming{nullopt};
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
