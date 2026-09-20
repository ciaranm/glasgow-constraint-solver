#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/parity/gf2_system.hh>
#include <gcs/constraints/parity/hints.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <bit>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::countr_zero;
using std::get;
using std::holds_alternative;
using std::make_optional;
using std::make_shared;
using std::map;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::popcount;
using std::size_t;
using std::string;
using std::swap;
using std::vector;
using std::ranges::all_of;
using std::ranges::any_of;

auto GF2Bits::none() const -> bool
{
    return all_of(_words, [](const auto & w) { return 0 == w; });
}

auto GF2Bits::count() const -> size_t
{
    size_t result = 0;
    for (const auto & w : _words)
        result += static_cast<size_t>(popcount(w));
    return result;
}

auto GF2Bits::first_set() const -> optional<size_t>
{
    for (size_t w = 0; w != _words.size(); ++w)
        if (0 != _words[w])
            return w * 64 + static_cast<size_t>(countr_zero(_words[w]));
    return nullopt;
}

auto GF2Bits::set_indices() const -> vector<size_t>
{
    vector<size_t> result;
    for (size_t w = 0; w != _words.size(); ++w) {
        auto bits = _words[w];
        while (0 != bits) {
            result.push_back(w * 64 + static_cast<size_t>(countr_zero(bits)));
            bits &= bits - 1;
        }
    }
    return result;
}

auto gcs::innards::canonical_atom(const IntegerVariableCondition & lit) -> pair<IntegerVariableCondition, bool>
{
    switch (lit.op) {
        using enum VariableConditionOperator;
    case Equal:
    case GreaterEqual:
    case InRange: return {lit, false};
    case NotEqual: return {IntegerVariableCondition{lit.var, Equal, lit.value, lit.upper_value}, true};
    case Less: return {IntegerVariableCondition{lit.var, GreaterEqual, lit.value, lit.upper_value}, true};
    case NotInRange: return {IntegerVariableCondition{lit.var, InRange, lit.value, lit.upper_value}, true};
    }
    throw NonExhaustiveSwitch{};
}

auto gcs::innards::build_gf2_system(const vector<Literals> & posted_rows) -> GF2System
{
    // Two passes: the first finds the columns, because a row cannot be built
    // until the width is known.
    map<IntegerVariableCondition, size_t> column_of;
    GF2System result;
    for (const auto & row : posted_rows)
        for (const auto & lit : row)
            if (holds_alternative<IntegerVariableCondition>(lit)) {
                auto atom = canonical_atom(get<IntegerVariableCondition>(lit)).first;
                if (column_of.emplace(atom, result.atoms.size()).second)
                    result.atoms.push_back(atom);
            }

    for (const auto & [r, posted] : enumerate(posted_rows)) {
        GF2Row row{GF2Bits{result.atoms.size()}, GF2Bits{posted_rows.size()}, true};
        row.origin.set(r);
        for (const auto & lit : posted)
            overloaded{//
                [&](const IntegerVariableCondition & cond) {
                    auto [atom, negated] = canonical_atom(cond);
                    // XOR rather than set: a repeated atom cancels, which is
                    // exactly what `x XOR x = 0` says, and a negated literal is
                    // its atom plus a flip of the right-hand side.
                    row.atoms.flip(column_of.at(atom));
                    if (negated)
                        row.rhs = ! row.rhs;
                },
                [&](const TrueLiteral &) { row.rhs = ! row.rhs; }, [&](const FalseLiteral &) {}}
                .visit(lit);
        result.rows.push_back(move(row));
    }

    return result;
}

auto gcs::innards::gauss_jordan(vector<GF2Row> & rows, size_t n_atoms) -> size_t
{
    size_t rank = 0;
    for (size_t col = 0; col != n_atoms && rank != rows.size(); ++col) {
        auto pivot = rows.size();
        for (size_t r = rank; r != rows.size(); ++r)
            if (rows[r].atoms.test(col)) {
                pivot = r;
                break;
            }
        if (pivot == rows.size())
            continue;

        swap(rows[rank], rows[pivot]);
        for (size_t r = 0; r != rows.size(); ++r)
            if (r != rank && rows[r].atoms.test(col)) {
                rows[r].atoms ^= rows[rank].atoms;
                rows[r].origin ^= rows[rank].origin;
                rows[r].rhs = rows[r].rhs != rows[rank].rhs;
            }
        ++rank;
    }
    return rank;
}

namespace
{
    // The trivially-true axiom `lit >= 0`, spelled the way the row that mentions
    // the literal spells it: through simplify_literal, so that a view or a
    // lazily-named atom resolves to the same XLiteral the OPB row carries and
    // the pol arithmetic actually cancels. See dev_docs/view-proof-logging.md.
    auto push_literal_axiom(PolBuilder & pol, NamesAndIDsTracker & tracker, const Literal & lit) -> void
    {
        overloaded{//
            [&](const TrueLiteral &) {}, [&](const FalseLiteral &) {},
            [&]<typename T_>(const VariableConditionFrom<T_> & cond) { pol.add(tracker.xliteral_for_ensuring(cond), tracker); }}
            .visit(simplify_literal(tracker, lit));
    }

    auto literals_of(const vector<ParitySystemRow> & rows) -> vector<Literals>
    {
        vector<Literals> result;
        result.reserve(rows.size());
        for (const auto & row : rows)
            result.push_back(row.literals);
        return result;
    }

    auto triggers_for(const vector<ParitySystemRow> & rows) -> Triggers
    {
        Triggers triggers;
        for (const auto & row : rows)
            for (const auto & l : row.literals)
                add_trigger_for(triggers, l);
        return triggers;
    }
}

auto gcs::innards::install_parity_system_propagator(
    Propagators & propagators, const ConstraintID & id, const string & constraint_type, vector<ParitySystemRow> rows) -> void
{
    // A row over no literals says that zero is odd. It has no step to
    // telescope and so no slack row, and there is nothing for elimination to do
    // with it either --- but its own three chain rows pin a_0 both to one and
    // to zero, so refuting it here is a plain RUP and leaves the rest of the
    // system with a system it can actually reason about.
    if (any_of(rows, [](const auto & row) { return row.literals.empty(); })) {
        propagators.install_initial_contradiction(
            id, constraint_type, "a parity row has no literals in it, so nothing can make it odd", JustifyUsingRUP{hints::Parity{id}});
        return;
    }

    // The two slack rows per posted row, derived once at Top by the initialiser
    // below and cited by every justification afterwards. Shared rather than
    // copied because the propagator's closure is built here, before the
    // initialiser has run. Empty for a row over no literals, which needs none.
    auto slack_rows = make_shared<vector<optional<pair<ProofLine, ProofLine>>>>();

    propagators.install_initialiser(
        [rows, slack_rows](State &, auto &, ProofLogger * const logger) -> void {
            if (! logger)
                return;

            for (const auto & row : rows)
                slack_rows->push_back(derive_parity_slack_rows(*logger, *row.slack_source, row.literals, row.flag_stem));
        },
        InitialiserPriority::SimpleDefinition);

    propagators.install(
        id,
        [system = build_gf2_system(literals_of(rows)), slack_rows, owner = id](
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
        triggers_for(rows));
}
