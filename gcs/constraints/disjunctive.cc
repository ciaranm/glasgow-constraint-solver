#include <gcs/constraints/disjunctive.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <sstream>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
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

Disjunctive::Disjunctive(vector<IntegerVariableID> starts, vector<Integer> lengths, bool strict) :
    _starts(move(starts)),
    _lengths(move(lengths)),
    _strict(strict)
{
    if (_starts.size() != _lengths.size())
        throw UnexpectedException{"Disjunctive: starts and lengths must have the same size"};
    for (auto & l : _lengths)
        if (l < 0_i)
            throw UnexpectedException{"Disjunctive: lengths must be non-negative"};
}

auto Disjunctive::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Disjunctive>(_starts, _lengths, _strict);
}

auto Disjunctive::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Disjunctive::prepare(Propagators &, State &, ProofModel * const) -> bool
{
    // In non-strict mode, zero-length tasks are dropped: they cannot constrain
    // any other task. In strict mode, every task participates (a zero-length
    // task at time t is forbidden from sitting strictly inside any other
    // task's active interval). Because lengths are constant, the distinction
    // is fully resolved here.
    auto n = _starts.size();
    _active_tasks.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        if (! _strict && _lengths[i] == 0_i)
            continue;
        _active_tasks.push_back(i);
    }

    // With fewer than two participating tasks there is no pair, hence nothing
    // to encode and nothing to check.
    return _active_tasks.size() >= 2;
}

auto Disjunctive::define_proof_model(ProofModel & model) -> void
{
    // Declarative pairwise OPB encoding:
    //   for each unordered pair (i, j) of participating tasks:
    //     before_{i,j} ⇔  starts[i] + lengths[i] ≤ starts[j]
    //     before_{j,i} ⇔  starts[j] + lengths[j] ≤ starts[i]
    //   then one clause per pair:
    //     before_{i,j} ∨ before_{j,i}
    //
    // This reflects the constraint's declarative meaning rather than the
    // time-table reasoning a stronger propagator would do. The bridge to
    // active/before/after-at-time flags is introduced lazily inside the
    // propagator's justifications (see follow-up stages on issue 146).
    auto emit_before = [&](size_t i, size_t j) -> ProofFlag {
        return model.create_proof_flag_fully_reifying(
            "disjbefore", "Disjunctive", "first task finishes before second starts",
            WPBSum{} + 1_i * _starts[i] + -1_i * _starts[j] <= -_lengths[i]);
    };
    for (size_t a = 0; a < _active_tasks.size(); ++a) {
        auto i = _active_tasks[a];
        for (size_t b = a + 1; b < _active_tasks.size(); ++b) {
            auto j = _active_tasks[b];
            auto before_ij = emit_before(i, j);
            auto before_ji = emit_before(j, i);
            model.add_constraint("Disjunctive", "one task must finish first",
                WPBSum{} + 1_i * before_ij + 1_i * before_ji >= 1_i);
        }
    }
}

auto Disjunctive::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (auto i : _active_tasks)
        triggers.on_instantiated.emplace_back(_starts[i]);

    propagators.install(
        [starts = move(_starts), lengths = move(_lengths),
            active_tasks = move(_active_tasks)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Pure checker: only fire once every participating task is fixed,
            // then verify pairwise non-overlap. The contradiction RUPs from
            // the declarative OPB encoding (the reified before flags UP from
            // the unit start values, and the pairwise clause then unit-fails).
            for (auto i : active_tasks)
                if (! state.has_single_value(starts[i]))
                    return PropagatorState::Enable;

            for (size_t a = 0; a + 1 < active_tasks.size(); ++a) {
                auto i = active_tasks[a];
                auto si = state.lower_bound(starts[i]);
                for (size_t b = a + 1; b < active_tasks.size(); ++b) {
                    auto j = active_tasks[b];
                    auto sj = state.lower_bound(starts[j]);
                    if (si + lengths[i] > sj && sj + lengths[j] > si) {
                        inference.contradiction(logger, JustifyUsingRUP{},
                            generic_reason(state, starts));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
            }

            return PropagatorState::DisableUntilBacktrack;
        },
        triggers);
}

auto Disjunctive::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;
    print(s, "{} disjunctive{} (", _name, _strict ? "_strict" : "");
    for (const auto & v : _starts)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, " ) ( ");
    for (const auto & l : _lengths)
        print(s, " {}", l);
    print(s, " )");
    return s.str();
}
