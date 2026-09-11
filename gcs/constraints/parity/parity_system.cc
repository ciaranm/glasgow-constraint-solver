#include <gcs/constraints/innards/cake_truthiness.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/parity/gf2_system.hh>
#include <gcs/constraints/parity/hints.hh>
#include <gcs/constraints/parity/parity_chain.hh>
#include <gcs/constraints/parity/parity_system.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>
#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::make_shared;
using std::make_unique;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::size_t;
using std::to_string;
using std::unique_ptr;
using std::vector;
using std::ranges::any_of;

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

ParitySystem::ParitySystem(const vector<vector<IntegerVariableID>> & rows, ParitySystemPropagation propagation) :
    ParitySystem(to_lit_rows(rows), propagation)
{
}

ParitySystem::ParitySystem(vector<Literals> rows, ParitySystemPropagation propagation) : _rows(move(rows)), _propagation(propagation)
{
}

auto ParitySystem::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ParitySystem>(_rows, _propagation);
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
        _chains.push_back(define_parity_chain(model, _constraint_id, static_cast<long long>(r), row));
}

namespace
{
    // The trivially-true axiom `lit >= 0`, spelled the way the row that
    // mentions the literal spells it: through simplify_literal, so that a view
    // or a lazily-named atom resolves to the same XLiteral the OPB row carries
    // and the pol arithmetic actually cancels. See
    // dev_docs/view-proof-logging.md.
    auto push_literal_axiom(PolBuilder & pol, NamesAndIDsTracker & tracker, const Literal & lit) -> void
    {
        overloaded{//
            [&](const TrueLiteral &) {}, [&](const FalseLiteral &) {},
            [&]<typename T_>(const VariableConditionFrom<T_> & cond) { pol.add(tracker.xliteral_for_ensuring(cond), tracker); }}
            .visit(simplify_literal(tracker, lit));
    }

    auto triggers_for(const vector<Literals> & rows) -> Triggers
    {
        Triggers triggers;
        for (const auto & row : rows)
            for (const auto & l : row)
                add_trigger_for(triggers, l);
        return triggers;
    }
}

auto ParitySystem::install_propagators(Propagators & propagators) -> void
{
    switch (_propagation) {
        using enum ParitySystemPropagation;
    case CheckOnly: install_check_only_propagator(propagators); return;
    case GaussJordan: install_gauss_jordan_propagator(propagators); return;
    }
    throw NonExhaustiveSwitch{};
}

auto ParitySystem::install_check_only_propagator(Propagators & propagators) -> void
{
    propagators.install(
        constraint_id(),
        [rows = _rows, owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // No pruning at all: wait for a row to be fully assigned, check it,
            // and contradict if the parity is wrong. Every inference is over a
            // complete assignment, which is exactly the case unit propagation
            // closes on its own.
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
        triggers_for(_rows));
}

auto ParitySystem::install_gauss_jordan_propagator(Propagators & propagators) -> void
{
    // A row over no literals says that zero is odd. It has no step to
    // telescope and so no slack row, and there is nothing for elimination to do
    // with it either --- but its own three chain rows pin a_0 both to one and
    // to zero, so refuting it here is a plain RUP and leaves the rest of the
    // system with a system it can actually reason about.
    if (any_of(_rows, [](const auto & row) { return row.empty(); })) {
        propagators.install_initial_contradiction(constraint_id(), constraint_type(),
            "a parity row has no literals in it, so nothing can make it odd", JustifyUsingRUP{hints::Parity{constraint_id()}});
        return;
    }

    // The two slack rows per posted row, derived once at Top by the initialiser
    // below and cited by every justification afterwards. Shared rather than
    // copied because the propagator's closure is built here, before the
    // initialiser has run. Empty for a row over no literals, which needs none.
    auto slack_rows = make_shared<vector<optional<pair<ProofLine, ProofLine>>>>();

    propagators.install_initialiser(
        [rows = _rows, chains = _chains, slack_rows, owner = constraint_id()](State &, auto &, ProofLogger * const logger) -> void {
            if (! logger)
                return;

            for (const auto & [r, row] : enumerate(rows))
                slack_rows->push_back(derive_parity_slack_rows(*logger, chains[r], row, "psys" + as_string(owner) + "r" + to_string(r) + "_"));
        },
        InitialiserPriority::SimpleDefinition);

    propagators.install(
        constraint_id(),
        [system = build_gf2_system(_rows), slack_rows, owner = constraint_id()](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            auto n_atoms = system.atoms.size();

            // Read the trail once. An atom fixed at the root is no different
            // from one a guess decided: either way it leaves the columns and
            // flips the right-hand sides it appeared in.
            vector<LiteralIs> assignment;
            assignment.reserve(n_atoms);
            auto any_undecided = false;
            for (const auto & atom : system.atoms) {
                assignment.push_back(state.test_literal(atom));
                if (LiteralIs::Undecided == assignment.back())
                    any_undecided = true;
            }

            // Substitute, then eliminate. From scratch every time: maintaining
            // the reduced row echelon form incrementally is the interesting
            // engineering and it does not belong in the first version, because
            // XORing rows *creates* non-zero cells and so does not trail
            // cleanly. See dev_docs/parity-system.md.
            auto working = system.rows;
            for (auto & row : working)
                for (const auto & a : row.atoms.set_indices())
                    switch (assignment[a]) {
                        using enum LiteralIs;
                    case DefinitelyTrue:
                        row.atoms.reset(a);
                        row.rhs = ! row.rhs;
                        break;
                    case DefinitelyFalse: row.atoms.reset(a); break;
                    case Undecided: break;
                    }

            gauss_jordan(working, n_atoms);

            // A row's support is the atoms of the rows it is the sum of, before
            // substitution, and the assignment to those is the rho of Gocht and
            // Nordstrom's section 4.3 --- so it is both the reason and what the
            // justification has to walk.
            auto support_of = [&](const GF2Row & row) {
                GF2Bits support{n_atoms};
                for (const auto & o : row.origin.set_indices())
                    support ^= system.rows[o].atoms;
                return support;
            };

            auto reason_for = [&](const GF2Bits & support) {
                ReasonLiterals reason;
                for (const auto & a : support.set_indices())
                    switch (assignment[a]) {
                        using enum LiteralIs;
                    case DefinitelyTrue: reason.push_back(system.atoms[a]); break;
                    case DefinitelyFalse: reason.push_back(! system.atoms[a]); break;
                    case Undecided: break;
                    }
                return reason;
            };

            // Gocht and Nordstrom's section 4.3, as one pol: sum the slack rows
            // of everything that went into this row, add a literal axiom for
            // each atom of its support --- the atom itself where rho makes it
            // false, its negation where rho makes it true --- then divide by two
            // and multiply back, which is the step that gains one because the
            // right-hand side is odd exactly when rho falsifies the row's
            // parity. Adding the other direction turns what is left into a
            // clause falsified by rho, and the framework's wrapping RUP closes
            // on it. Atoms outside the support have even coefficients already
            // and need nothing.
            // `pretend` is how a propagation is justified rather than a
            // conflict: the one unassigned atom is given the value that would
            // violate the row, and the clause that comes out then has that
            // atom's literal as its only term rho does not falsify, so it
            // propagates. A conflict passes nullopt, rho being complete already.
            auto justify_from = [&](const GF2Bits & origin, const GF2Bits & support, const optional<pair<size_t, bool>> & pretend) {
                return [&, origin, support, pretend](const ReasonLiterals &) {
                    PolBuilder pol;
                    for (const auto & o : origin.set_indices())
                        pol.add((*slack_rows)[o]->first);

                    for (const auto & a : support.set_indices()) {
                        auto rho_says_true = pretend && pretend->first == a ? pretend->second : LiteralIs::DefinitelyTrue == assignment[a];
                        push_literal_axiom(
                            pol, logger->names_and_ids_tracker(), rho_says_true ? Literal{! system.atoms[a]} : Literal{system.atoms[a]});
                    }

                    pol.divide_by(2_i).multiply_by(2_i);
                    for (const auto & o : origin.set_indices())
                        pol.add((*slack_rows)[o]->second);
                    pol.emit(*logger, ProofLevel::Temporary);
                };
            };

            for (const auto & row : working) {
                auto how_many = row.atoms.count();
                if (0 != how_many && 1 != how_many)
                    continue;
                if (0 == how_many && ! row.rhs)
                    continue;

                auto support = support_of(row);
                auto reason = reason_for(support);

                if (0 == how_many)
                    inference.contradiction(logger, JustifyExplicitly{justify_from(row.origin, support, nullopt), ThenRUP::Yes, hints::Parity{owner}},
                        ExplicitReason{reason});
                else {
                    auto a = *row.atoms.first_set();
                    inference.infer(logger, row.rhs ? Literal{system.atoms[a]} : Literal{! system.atoms[a]},
                        JustifyExplicitly{justify_from(row.origin, support, make_optional(pair{a, ! row.rhs})), ThenRUP::Yes, hints::Parity{owner}},
                        ExplicitReason{reason});
                }
            }

            return any_undecided ? PropagatorState::Enable : PropagatorState::DisableUntilBacktrack;
        },
        triggers_for(_rows));
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
