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
using std::shared_ptr;
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

namespace
{
    auto add_distinct(vector<IntegerVariableID> & vs, const IntegerVariableID & v) -> void
    {
        if (std::find(vs.begin(), vs.end(), v) == vs.end())
            vs.push_back(v);
    }
}

auto NogoodStore::add(Nogood nogood) -> void
{
    vector<IntegerVariableID> vs;
    for (const auto & lit : nogood)
        add_distinct(vs, lit.var);
    _vars->push_back(move(vs));
    _nogoods->push_back(move(nogood));
}

auto NogoodStore::size() const -> size_t
{
    return _nogoods->size();
}

Nogoods::Nogoods(vector<Nogood> nogoods) :
    _store(make_shared<NogoodStore>())
{
    for (auto & nogood : nogoods) {
        for (const auto & lit : nogood)
            add_distinct(_trigger_vars, lit.var);
        _store->add(move(nogood));
    }
}

Nogoods::Nogoods(shared_ptr<NogoodStore> store, vector<IntegerVariableID> trigger_vars) :
    _store(move(store)),
    _trigger_vars(move(trigger_vars))
{
}

auto Nogoods::clone() const -> unique_ptr<Constraint>
{
    // Share the live store; copy the trigger list.
    return make_unique<Nogoods>(_store, _trigger_vars);
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
    // of their negations. Only the nogoods present at install are declared here;
    // ones learned later are derived in the proof as they are recorded.
    for (const auto & nogood : *_store->_nogoods) {
        Literals lits;
        for (const auto & lit : nogood)
            lits.emplace_back(! lit);
        model.add_constraint("Nogoods", "nogood", move(lits));
    }
}

namespace
{
    constexpr size_t no_watch = std::numeric_limits<size_t>::max();

    // Initialise the two watches for nogood `ni`, propagating a unit or raising a
    // contradiction if it is already so. Appends to `watches`, so it must be
    // called with `watches.size() == ni`. Shared between the one-off initialiser
    // and the propagator's lazy catch-up for nogoods learned during search.
    template <typename Inference_>
    auto init_watches_for(size_t ni, const vector<Nogood> & nogoods,
        const vector<vector<IntegerVariableID>> & nogood_vars, vector<pair<size_t, size_t>> & watches,
        const State & state, Inference_ & inference, ProofLogger * const logger) -> void
    {
        const auto & nogood = nogoods[ni];
        const auto & vars = nogood_vars[ni];

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
            inference.infer(logger, ! nogood[*w1], JustifyUsingRUP{}, generic_reason(state, vars));
            watches.emplace_back(*w1, *w1);
        }
        else
            watches.emplace_back(*w1, *w2);
    }
}

auto Nogoods::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (auto & v : _trigger_vars)
        triggers.on_change.emplace_back(v);

    // The nogood data is shared with the store (so additions are visible here);
    // the watches are this propagator's own, non-backtrackable, and grown lazily
    // to keep pace with the nogoods.
    auto nogoods = _store->_nogoods;
    auto nogood_vars = _store->_vars;
    auto watches = make_shared<vector<pair<size_t, size_t>>>();

    // Init: set up watches for the nogoods present up front (none, for a store
    // that the restart loop will grow during search).
    propagators.install_initialiser(
        [nogoods, nogood_vars, watches](const State & state, auto & inference, ProofLogger * const logger) -> void {
            watches->reserve(nogoods->size());
            for (size_t ni = 0; ni < nogoods->size(); ++ni)
                init_watches_for(ni, *nogoods, *nogood_vars, *watches, state, inference, logger);
        });

    propagators.install(
        constraint_id(),
        [nogoods, nogood_vars, watches](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Catch up: initialise watches for any nogoods learned since the last
            // fire. (A unit/contradiction is propagated here, on first sight.)
            for (size_t ni = watches->size(); ni < nogoods->size(); ++ni)
                init_watches_for(ni, *nogoods, *nogood_vars, *watches, state, inference, logger);

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
    for (const auto & nogood : *_store->_nogoods) {
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
