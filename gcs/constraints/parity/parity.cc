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

auto ParityOdd::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    // If every literal has a cake positive form, work in those terms from here
    // on (they are state-equivalent), so the encoding, the propagator's
    // inferences, and the written scp all line up with cake_pb_cp's reading.
    Literals cake_lits;
    for (const auto & l : _lits) {
        auto form = cake_positive_form(l, [&](const SimpleIntegerVariableID & v) { return initial_state.bounds(v); });
        if (! form)
            return true;
        cake_lits.push_back(cake_positive_literal(*form));
    }
    _cake_lits = move(cake_lits);
    return true;
}

auto ParityOdd::define_proof_model(ProofModel & model) -> void
{
    if (! _cake_lits.empty()) {
        // cake_pb_cp's accumulator scheme: x[id][0] channels the parity bit
        // (always the constant 1 here, which cake carries as its pinned-true
        // n[1][ge1] atom; our rows fold it), x[id][k] = x[id][k-1] XOR the k'th
        // literal via four labelled clauses, and the acc row pins the final
        // accumulator to 0, i.e. 1 XOR (parity of the literals) = 0.
        PseudoBooleanTerm acc = FalseLiteral{}, not_acc = TrueLiteral{};
        auto x0 = model.create_proof_flag(_constraint_id, vector<long long>{0}, nullopt);
        model.add_labelled_constraint(_constraint_id, "0ge", WPBSum{} + 1_i * TrueLiteral{} + -1_i * x0 >= 0_i);
        model.add_labelled_constraint(_constraint_id, "0le", WPBSum{} + 1_i * x0 + -1_i * TrueLiteral{} >= 0_i);
        acc = x0;
        not_acc = ! x0;
        for (const auto & [k, l] : enumerate(_cake_lits)) {
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
        return;
    }

    PseudoBooleanTerm acc = FalseLiteral{}, not_acc = TrueLiteral{};
    for (const auto & l : _lits) {
        auto new_acc = model.create_proof_flag("xor");

        model.add_constraint(WPBSum{} + 1_i * acc + 1_i * l + 1_i * ! new_acc >= 1_i);
        model.add_constraint(WPBSum{} + 1_i * not_acc + 1_i * ! l + 1_i * ! new_acc >= 1_i);
        model.add_constraint(WPBSum{} + 1_i * not_acc + 1_i * l + 1_i * new_acc >= 1_i);
        model.add_constraint(WPBSum{} + 1_i * acc + 1_i * ! l + 1_i * new_acc >= 1_i);

        acc = new_acc;
        not_acc = ! new_acc;
    }
    model.add_constraint(WPBSum{} + 1_i * acc >= 1_i);
}

auto ParityOdd::install_propagators(Propagators & propagators) -> void
{
    // In cake terms when prepare() found positive forms, so the inferences'
    // literals are the atoms the (cake-conform) encoding constrains.
    const Literals & effective_lits = _cake_lits.empty() ? _lits : _cake_lits;

    Triggers triggers;
    for (const auto & l : effective_lits)
        add_trigger_for(triggers, l);

    propagators.install(
        constraint_id(),
        [lits = effective_lits, owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
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

    // cake_pb_cp encodes parity as `parity (X1 ... Xn) Y` meaning Y = XOR(Xi > 0).
    // ParityOdd is the bare odd-parity assertion, so we write the constant
    // Y = 1. That bare-operand form is only faithful when every literal has a
    // cake positive form (this runs on the stored constraint, which never sees
    // prepare(), so recompute from the tracker's recorded bounds); otherwise
    // record the literals' real shapes under parity_lits, which cake skips and
    // read_scp round-trips.
    std::vector<SExpr> lits;
    bool conformable = true;
    for (const auto & lit : _lits) {
        auto form = cake_positive_form(lit, [&](const SimpleIntegerVariableID & v) { return tracker.tracked_bounds(v); });
        if (! form) {
            conformable = false;
            break;
        }
        lits.push_back(tracker.s_expr_term_of(*form));
    }
    if (conformable)
        return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("parity"), SExpr::list(std::move(lits)), SExpr::atom("1")});

    lits.clear();
    for (const auto & lit : _lits)
        lits.push_back(faithful_literal_term(lit, tracker));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("parity_lits"), SExpr::list(std::move(lits)), SExpr::atom("1")});
}
