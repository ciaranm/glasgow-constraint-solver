#include <gcs/constraints/nogoods.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <cstddef>
#include <limits>
#include <memory>
#include <optional>
#include <sstream>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::make_unique;
using std::nullopt;
using std::optional;
using std::pair;
using std::size_t;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

Nogoods::Nogoods(vector<Nogood> nogoods) :
    _nogoods(move(nogoods))
{
}

auto Nogoods::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Nogoods>(_nogoods);
}

auto Nogoods::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Nogoods::define_proof_model(ProofModel & model) -> void
{
    // A nogood forbids a conjunction of literals, so its definition is the clause
    // of their negations: at least one negated literal must hold.
    for (const auto & nogood : _nogoods) {
        Literals lits;
        for (const auto & lit : nogood)
            lits.emplace_back(! lit);
        model.add_constraint("Nogoods", "nogood", move(lits));
    }
}

namespace
{
    constexpr size_t no_watch = std::numeric_limits<size_t>::max();
}

auto Nogoods::install_propagators(Propagators & propagators) -> void
{
    // The distinct variables each nogood mentions (for its reason), and their
    // union (what to wake on). Nogoods are short, so a linear dedup is fine.
    auto nogood_vars = make_shared<vector<vector<IntegerVariableID>>>();
    nogood_vars->reserve(_nogoods.size());
    vector<IntegerVariableID> all_vars;
    auto add_distinct = [](vector<IntegerVariableID> & vs, const IntegerVariableID & v) {
        if (std::find(vs.begin(), vs.end(), v) == vs.end())
            vs.push_back(v);
    };
    for (const auto & nogood : _nogoods) {
        vector<IntegerVariableID> vs;
        for (const auto & lit : nogood) {
            add_distinct(vs, lit.var);
            add_distinct(all_vars, lit.var);
        }
        nogood_vars->push_back(move(vs));
    }

    Triggers triggers;
    for (auto & v : all_vars)
        triggers.on_change.emplace_back(v);

    // Watches are non-backtrackable: when a watch moves during search, leaving it
    // moved after backtrack is sound (its literal can only become "more not-held"
    // as the state relaxes) and avoids restoration overhead. The shared_ptr lets
    // the initialiser and the main propagator share one watch store and one copy
    // of the (moved-out) nogood data.
    auto watches = make_shared<vector<pair<size_t, size_t>>>();
    auto nogoods = make_shared<const vector<Nogood>>(move(_nogoods));

    // Init: find two watch positions per nogood, propagating units and raising
    // contradictions. A position is unusable as a watch iff its literal is
    // currently DefinitelyTrue (entailed) --- then it cannot be the disjunct that
    // saves the clause.
    propagators.install_initialiser(
        [nogoods, nogood_vars, watches](const State & state, auto & inference, ProofLogger * const logger) -> void {
            watches->reserve(nogoods->size());

            for (size_t ni = 0; ni < nogoods->size(); ++ni) {
                const auto & nogood = (*nogoods)[ni];
                const auto & vars = (*nogood_vars)[ni];

                auto find_unbroken = [&](size_t skip) -> optional<size_t> {
                    for (size_t p = 0; p < nogood.size(); ++p) {
                        if (p == skip)
                            continue;
                        if (state.test_literal(nogood[p]) != LiteralIs::DefinitelyTrue)
                            return p;
                    }
                    return nullopt;
                };

                auto w1 = find_unbroken(no_watch);
                if (! w1)
                    inference.contradiction(logger, JustifyUsingRUP{}, generic_reason(state, vars));

                auto w2 = find_unbroken(*w1);
                if (! w2) {
                    // Unit clause: the only not-yet-held literal must be falsified.
                    inference.infer(logger, ! nogood[*w1], JustifyUsingRUP{}, generic_reason(state, vars));
                    // Mark as handled: both watches at one position read as broken
                    // on every later fire, and any rescue finds the unit redundant.
                    watches->emplace_back(*w1, *w1);
                }
                else
                    watches->emplace_back(*w1, *w2);
            }
        });

    propagators.install(
        constraint_id(),
        [nogoods, nogood_vars, watches](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            auto is_broken = [&](const Nogood & nogood, size_t p) -> bool {
                return state.test_literal(nogood[p]) == LiteralIs::DefinitelyTrue;
            };

            auto find_unbroken = [&](const Nogood & nogood, size_t skip1, size_t skip2) -> optional<size_t> {
                for (size_t p = 0; p < nogood.size(); ++p) {
                    if (p == skip1 || p == skip2)
                        continue;
                    if (state.test_literal(nogood[p]) != LiteralIs::DefinitelyTrue)
                        return p;
                }
                return nullopt;
            };

            for (size_t ni = 0; ni < nogoods->size(); ++ni) {
                auto & w = (*watches)[ni];
                const auto & nogood = (*nogoods)[ni];
                const auto & vars = (*nogood_vars)[ni];

                bool b1 = is_broken(nogood, w.first);
                bool b2 = is_broken(nogood, w.second);

                if (! b1 && ! b2)
                    continue;

                if (b1 && b2) {
                    auto new1 = find_unbroken(nogood, no_watch, no_watch);
                    if (! new1)
                        inference.contradiction(logger, JustifyUsingRUP{}, generic_reason(state, vars));
                    auto new2 = find_unbroken(nogood, *new1, no_watch);
                    if (! new2)
                        inference.infer(logger, ! nogood[*new1], JustifyUsingRUP{}, generic_reason(state, vars));
                    else {
                        w.first = *new1;
                        w.second = *new2;
                    }
                }
                else if (b1) {
                    auto new1 = find_unbroken(nogood, w.second, no_watch);
                    if (! new1)
                        inference.infer(logger, ! nogood[w.second], JustifyUsingRUP{}, generic_reason(state, vars));
                    else
                        w.first = *new1;
                }
                else {
                    auto new2 = find_unbroken(nogood, w.first, no_watch);
                    if (! new2)
                        inference.infer(logger, ! nogood[w.first], JustifyUsingRUP{}, generic_reason(state, vars));
                    else
                        w.second = *new2;
                }
            }
            return PropagatorState::Enable;
        },
        triggers);
}

auto Nogoods::s_exprify(const innards::ProofModel * const model) const -> string
{
    // Each nogood is a list of (variable op value) condition terms. This is not
    // part of the CakePB workflow (which has no `nogoods` rule), but s_exprify is
    // still invoked whenever a .scp is written, so it must produce valid output.
    stringstream s;
    print(s, "{} nogoods (", _constraint_id);
    for (const auto & nogood : _nogoods) {
        print(s, " (");
        for (const auto & lit : nogood)
            print(s, " ({} {} {})",
                model->names_and_ids_tracker().s_expr_name_of(lit.var),
                model->names_and_ids_tracker().s_expr_name_of(lit.op),
                lit.value.to_string());
        print(s, " )");
    }
    print(s, " )");
    return s.str();
}
