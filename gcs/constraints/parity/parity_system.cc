#include <gcs/constraints/innards/cake_truthiness.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/parity/hints.hh>
#include <gcs/constraints/parity/parity_chain.hh>
#include <gcs/constraints/parity/parity_system.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>
#include <util/enumerate.hh>

#include <optional>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::nullopt;
using std::unique_ptr;
using std::vector;

namespace
{
    auto to_lit_rows(const vector<vector<IntegerVariableID>> & rows) -> vector<Literals>
    {
        vector<Literals> result;
        result.reserve(rows.size());
        for (const auto & row : rows) {
            Literals lits;
            lits.reserve(row.size());
            for (const auto & v : row)
                lits.emplace_back(v != 0_i);
            result.push_back(move(lits));
        }
        return result;
    }
}

ParitySystem::ParitySystem(const vector<vector<IntegerVariableID>> & rows) : ParitySystem(to_lit_rows(rows))
{
}

ParitySystem::ParitySystem(vector<Literals> rows) : _rows(move(rows))
{
}

auto ParitySystem::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ParitySystem>(_rows);
}

auto ParitySystem::define_proof_model(ProofModel & model, const State &) -> void
{
    // One accumulator chain per row, exactly what a row posted as its own
    // ParityOdd would have emitted, only with the row index threaded through
    // the flag values and the role names so that the chains stay apart. Sharing
    // the emitter with ParityOdd is the whole point: the slack-form derivation
    // reads these rows back the same way whether they were posted here or
    // gathered from individual constraints.
    for (const auto & [r, row] : enumerate(_rows))
        define_parity_chain(model, _constraint_id, static_cast<long long>(r), row);
}

auto ParitySystem::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (const auto & row : _rows)
        for (const auto & l : row)
            add_trigger_for(triggers, l);

    propagators.install(
        constraint_id(),
        [rows = _rows, owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Stage 1 of dev_docs/parity-system.md: check only, no pruning at
            // all, so that the encoding can be settled before any system
            // reasoning exists to be blamed for a failure. Every inference here
            // is over a fully assigned row, which is exactly the case unit
            // propagation closes on its own.
            auto everything_decided = true;
            for (const auto & row : rows) {
                long how_many_true = 0;
                auto row_decided = true;
                ReasonLiterals reason;
                for (const auto & l : row) {
                    switch (state.test_literal(l)) {
                        using enum LiteralIs;
                    case DefinitelyTrue:
                        reason.push_back(l);
                        ++how_many_true;
                        break;
                    case DefinitelyFalse: reason.push_back(! l); break;
                    case Undecided: row_decided = false; break;
                    }
                }

                if (! row_decided)
                    everything_decided = false;
                else if (how_many_true % 2 == 0)
                    inference.contradiction(logger, JustifyUsingRUP{hints::Parity{owner}}, ExplicitReason{reason});
            }

            return everything_decided ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
        },
        triggers);
}

auto ParitySystem::constraint_type() const -> std::string
{
    return "parity_system";
}

auto ParitySystem::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    vector<SExpr> row_terms;
    for (const auto & row : _rows) {
        vector<SExpr> lits;
        for (const auto & lit : row)
            lits.push_back(reify_tuple_term(lit, tracker));
        row_terms.push_back(SExpr::list(move(lits)));
    }
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(move(row_terms))});
}
