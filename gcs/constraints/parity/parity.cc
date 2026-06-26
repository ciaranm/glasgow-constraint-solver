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
    PseudoBooleanTerm acc = FalseLiteral{}, not_acc = TrueLiteral{};
    for (const auto & l : _lits) {
        auto new_acc = model.create_proof_flag("xor");

        model.add_constraint("ParityOdd", "xor", WPBSum{} + 1_i * acc + 1_i * l + 1_i * ! new_acc >= 1_i);
        model.add_constraint("ParityOdd", "xor", WPBSum{} + 1_i * not_acc + 1_i * ! l + 1_i * ! new_acc >= 1_i);
        model.add_constraint("ParityOdd", "xor", WPBSum{} + 1_i * not_acc + 1_i * l + 1_i * new_acc >= 1_i);
        model.add_constraint("ParityOdd", "xor", WPBSum{} + 1_i * acc + 1_i * ! l + 1_i * new_acc >= 1_i);

        acc = new_acc;
        not_acc = ! new_acc;
    }
    model.add_constraint("ParityOdd", "result", WPBSum{} + 1_i * acc >= 1_i);
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
auto ParityOdd::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    // cake_pb_cp encodes parity as `parity (X1 ... Xn) Y` meaning Y = XOR(Xi).
    // ParityOdd is the bare odd-parity assertion XOR(Xi) = 1, so we write the
    // constant Y = 1 (1 = XOR(Xi) <-> XOR(Xi) = 1). The scp_reader requires Y = 1.
    std::vector<SExpr> lits;
    for (const auto & lit : _lits)
        lits.push_back(tracker.s_expr_term_of(lit));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("parity"), SExpr::list(std::move(lits)), SExpr::atom("1")});
}
