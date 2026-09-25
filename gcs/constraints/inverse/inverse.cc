#include <gcs/constraints/all_different/gac_all_different.hh>
#include <gcs/constraints/all_different/justify.hh>
#include <gcs/constraints/innards/recover_am1.hh>
#include <gcs/constraints/inverse/hints.hh>
#include <gcs/constraints/inverse/inverse.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>
#include <gcs/stats.hh>

#include <gcs/proof.hh>
#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <cstdint>
#include <optional>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::map;
using std::nullopt;
using std::optional;
using std::shared_ptr;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

Inverse::Inverse(vector<IntegerVariableID> x, vector<IntegerVariableID> y, Integer x_start, Integer y_start) :
    _x(move(x)), _y(move(y)), _x_start(x_start), _y_start(y_start)

{
    // x's values are y's indices and are all different, so a longer x could never
    // be satisfied. XCSP3 does not define that shape either, so it is taken to be
    // the arrays passed the wrong way round rather than a model to answer.
    if (_x.size() > _y.size())
        throw InvalidProblemDefinitionException{"Inverse: first array is longer than the second"};

    // The same variable in two entries of x takes one value j, which asks y[j] to
    // name both entries. In the bijection form every entry of y is named by some
    // entry of x, so the same holds the other way round; in the injection form two
    // entries of y can share a variable, provided at most one of them is named.
    // Either unsatisfiable shape is a legal post, not a misuse: MiniZinc gives two
    // entries one variable whenever a model equates them (#1047). So it is answered
    // with a contradiction at the root rather than rejected. Cross-array aliasing
    // (e.g. inverse(x, x) for involutions) is legitimate. Repeated constants are
    // left to the propagator: they aren't a single variable, they're two slots
    // pinned to the same value, which is a meaningful (and possibly infeasible)
    // model --- see the #171 regression case in inverse_test.
    auto has_duplicate = [](const vector<IntegerVariableID> & arr) {
        for (size_t i = 0; i < arr.size(); ++i) {
            if (is_constant_variable(arr[i]))
                continue;
            for (size_t j = i + 1; j < arr.size(); ++j)
                if (arr[i] == arr[j])
                    return true;
        }
        return false;
    };
    _has_duplicate_vars = has_duplicate(_x) || (! is_injection() && has_duplicate(_y));
}

auto Inverse::is_injection() const -> bool
{
    return _x.size() < _y.size();
}

auto Inverse::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Inverse>(_x, _y, _x_start, _y_start);
}

auto Inverse::prepare(Propagators & propagators, State & initial_state, ProofModel * const optional_model) -> bool
{
    for (const auto & [idx, v] : enumerate(_x)) {
        propagators.define_bound(initial_state, optional_model, v, Bound::Lower, 0_i + _y_start);
        propagators.define_bound(initial_state, optional_model, v, Bound::Upper, Integer(_y.size()) + _y_start - 1_i);
    }

    // In the injection form, an entry of y that no entry of x names can take any
    // value at all, so only the bijection form confines y to x's indices.
    if (! is_injection())
        for (const auto & [idx, v] : enumerate(_y)) {
            propagators.define_bound(initial_state, optional_model, v, Bound::Lower, 0_i + _x_start);
            propagators.define_bound(initial_state, optional_model, v, Bound::Upper, Integer(_x.size()) + _x_start - 1_i);
        }

    return true;
}

auto Inverse::define_proof_model(ProofModel & model, const State &) -> void
{
    for (const auto & [i, x_i] : enumerate(_x))
        for (const auto & [j, y_j] : enumerate(_y)) {
            // x[i] = j -> y[j] = i
            model.add_constraint(WPBSum{} + 1_i * (x_i != Integer(j) + _y_start) + 1_i * (y_j == Integer(i) + _x_start) >= 1_i);
            // y[j] = i -> x[i] = j, which the injection form does not say
            if (! is_injection())
                model.add_constraint(WPBSum{} + 1_i * (y_j != Integer(i) + _x_start) + 1_i * (x_i == Integer(j) + _y_start) >= 1_i);
        }

    // Set up the AM1 map only when proof logging is on; the propagator captures it
    // by value, so it must always be non-null but stays empty when define_proof_model
    // wasn't called.
    _x_value_am1s = make_shared<map<Integer, ProofLine>>();
}

namespace
{
    // Two entries of one array hold the same variable, and every value it could
    // take asks the other array's entry at that value to name both of them. So
    // each value is ruled out by RUP from the two rows that say so, and once every
    // value in the bounds prepare() gave the variable is gone, so is the variable.
    // The rows run from x to y, and also from y to x in the bijection form, which
    // is the only form in which a repeat in y is a contradiction.
    auto install_duplicate_contradiction(Propagators & propagators, const ConstraintID & owner, const string & constraint_type,
        const vector<IntegerVariableID> & x, const vector<IntegerVariableID> & y, Integer x_start, Integer y_start, bool injection) -> void
    {
        auto first_repeated = [](const vector<IntegerVariableID> & arr) -> optional<IntegerVariableID> {
            for (size_t i = 0; i < arr.size(); ++i)
                if (! is_constant_variable(arr[i]))
                    for (size_t j = i + 1; j < arr.size(); ++j)
                        if (arr[i] == arr[j])
                            return arr[i];
            return nullopt;
        };

        // x's values are y's indices and the other way round, so a repeat in x
        // has y's indices to rule out, and a repeat in y has x's.
        optional<IntegerVariableID> var;
        Integer lowest = 0_i;
        size_t count = 0;
        if (auto in_x = first_repeated(x)) {
            var = in_x;
            lowest = y_start;
            count = y.size();
        }
        else if (auto in_y = first_repeated(y); in_y && ! injection) {
            var = in_y;
            lowest = x_start;
            count = x.size();
        }
        else
            throw UnexpectedException{"Inverse has no repeated variable to justify its contradiction with"};

        propagators.report(StatsNote{.level = StatsLevel::Important,
            .component = constraint_type,
            .constraint = owner,
            .text = "An Inverse constraint was posted with the same variable more than once, so the model is unsatisfiable before search starts"});

        propagators.install_initialiser([var = *var, lowest, count, owner](const State &, auto & inference, ProofLogger * const logger) -> void {
            inference.contradiction(logger,
                JustifyExplicitly{[&](const ReasonLiterals &) {
                                      for (auto v = lowest; v < lowest + Integer(count); ++v)
                                          logger->emit_rup_proof_line(WPBSum{} + 1_i * (var != v) >= 1_i, ProofLevel::Temporary);
                                  },
                    ThenRUP::Yes, hints::Inverse{owner}},
                NoReason{});
        });
    }

    // The injection form's rule for y. A value j of y's index set that every
    // matching of x takes is taken by some entry of x in every solution, and
    // then y[j] names it, so y[j] can only name an entry of x that can still
    // take j. After all-different GAC, the entries of x split into those whose
    // domains lie within the values every matching takes, as many of them as
    // there are such values, and those whose domains miss those values entirely.
    // The first lot, and each connected component of it (entries linked by the
    // values they share), is a Hall set that has to take all of its values.
    // That is what justifies the pruning: j's component is summed without j's
    // at-most-one, which says that one of its entries takes j, and assuming y[j]
    // names anything else, the rows from x to y say that none of them does.
    template <typename Inference_>
    auto propagate_needed_values(const ConstraintID & owner, const vector<IntegerVariableID> & x, const vector<IntegerVariableID> & y,
        Integer x_start, Integer y_start, const vector<Integer> & x_values, const vector<uint8_t> & in_every_matching,
        map<Integer, ProofLine> & x_value_am1s, const State & state, Inference_ & inf, ProofLogger * const logger) -> void
    {
        // The values every matching takes, and the entries of x that take them.
        // After GAC, an entry's domain is inside that set or disjoint from it, so
        // any one of its values says which. Constants are left out of the Hall
        // sets, as all-different's own Hall sets leave them out: a constant's
        // term in its value's at-most-one does the same job as its at-least-one.
        // (A constant's value is only ever its own component, anyway.)
        vector<size_t> needed_offsets;
        for (const auto & [v_idx, needed] : enumerate(in_every_matching))
            if (needed)
                needed_offsets.push_back(v_idx);
        if (needed_offsets.empty())
            return;
        auto offset_of = [&](Integer v) { return (v - y_start).as_index(); };
        vector<IntegerVariableID> hall_vars;
        for (const auto & x_i : x)
            if (! is_constant_variable(x_i) && in_every_matching.at(offset_of(state.lower_bound(x_i))))
                hall_vars.push_back(x_i);

        // Components, as a union-find over the needed values: an entry joins every
        // value it can take.
        vector<size_t> parent(x_values.size());
        for (size_t v = 0; v < parent.size(); ++v)
            parent[v] = v;
        auto find = [&](size_t v) {
            while (parent[v] != v)
                v = parent[v] = parent[parent[v]];
            return v;
        };
        for (const auto & x_i : hall_vars) {
            auto first = offset_of(state.lower_bound(x_i));
            for (auto v : needed_offsets)
                if (v != first && state.in_domain(x_i, x_values[v]))
                    parent[find(v)] = find(first);
        }

        vector<Literal> deletions;
        vector<IntegerVariableID> component_vars;
        vector<Integer> component_vals;
        for (auto j_offset : needed_offsets) {
            auto j = x_values[j_offset];
            const auto & y_j = y.at(j_offset);

            // The entries of x that can take j, as y[j]'s values would name them.
            vector<Integer> can_take;
            for (const auto & [i, x_i] : enumerate(x))
                if (state.in_domain(x_i, j))
                    can_take.push_back(Integer(i) + x_start);

            // After GAC something can take a value every matching takes. Two views
            // of one variable can delete the last of them behind GAC's back, and
            // then there is no matching at all, which the next pass reports.
            if (can_take.empty())
                continue;

            // Only one entry can take j, so after GAC it has usually taken j, and
            // then the one row that says so names it. (Two views of one variable
            // in x can leave GAC short of that, and then the Hall set below does
            // it instead.)
            if (can_take.size() == 1) {
                const auto & x_i = x.at((can_take.front() - x_start).as_index());
                if (state.has_single_value(x_i)) {
                    inf.infer(logger, y_j == can_take.front(), JustifyUsingRUP{hints::Inverse{owner}},
                        inf.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{x_i == j}}} : Reason{});
                    continue;
                }
            }

            // Otherwise y[j] loses everything outside [first, last] of can_take,
            // and the gaps between. The gaps lie within x's indices, so walking
            // them costs no more than the entries of x.
            deletions.clear();
            if (state.lower_bound(y_j) < can_take.front())
                deletions.push_back(y_j >= can_take.front());
            if (state.upper_bound(y_j) > can_take.back())
                deletions.push_back(y_j < can_take.back() + 1_i);
            for (size_t k = 0; k + 1 < can_take.size(); ++k)
                for (auto v = can_take[k] + 1_i; v < can_take[k + 1]; ++v)
                    if (state.in_domain(y_j, v))
                        deletions.push_back(y_j != v);
            if (deletions.empty())
                continue;

            if (! logger && ! inf.want_reasons()) {
                inf.infer_all(logger, deletions, NoJustificationNeeded{}, NoReason{});
                continue;
            }

            component_vars.clear();
            component_vals.clear();
            auto root = find(j_offset);
            for (auto v : needed_offsets)
                if (find(v) == root)
                    component_vals.push_back(x_values[v]);
            for (const auto & x_i : hall_vars)
                if (find(offset_of(state.lower_bound(x_i))) == root)
                    component_vars.push_back(x_i);
            // A component of a GAC graph is as big on each side. Two views of one
            // variable can delete a matched edge behind GAC's back, and split one
            // unevenly; the whole Hall set is still as big on each side, since an
            // entry never moves between the two lots, so fall back to that.
            if (component_vars.size() < component_vals.size()) {
                component_vars = hall_vars;
                component_vals.clear();
                for (auto v : needed_offsets)
                    component_vals.push_back(x_values[v]);
            }

            // The reason is the Hall entries' domains, as for all-different's own
            // Hall sets: the other entries' terms in the at-most-ones are slack
            // the sum can spare, and need not be falsified.
            inf.infer_all(logger, deletions,
                JustifyExplicitly{[&, vars = component_vars, vals = component_vals](const ReasonLiterals &) {
                                      justify_all_different_hall_set_needs_value(*logger, state, x, vars, vals, j, x_value_am1s);
                                  },
                    ThenRUP::Yes, hints::InverseNeededValue{{owner}}},
                generic_reason(component_vars));
        }
    }
}

auto Inverse::install_propagators(Propagators & propagators) -> void
{
    if (_has_duplicate_vars) {
        install_duplicate_contradiction(propagators, constraint_id(), constraint_type(), _x, _y, _x_start, _y_start, is_injection());
        return;
    }

    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _x.begin(), _x.end());
    triggers.on_change.insert(triggers.on_change.end(), _y.begin(), _y.end());

    if (_x_value_am1s) {
        // x's values are y's indices, so there is an at-most-one for each of y's
        // entries, which is more than one per entry of x in the injection form.
        auto build_am1s = [](const vector<IntegerVariableID> & x, Integer y_start, size_t y_size, const State &, auto &, ProofLogger * const logger,
                              const auto & map) {
            // recover_am1 requires at least two atoms; with one variable
            // the at-most-one is trivially true and the map is never read
            // (gac_all_different's hall-set/scc paths do not fire on a
            // single variable).
            if (x.size() < 2)
                return;
            for (Integer v = y_start; v < y_start + Integer(y_size); ++v) {
                // make an am1 for x[i] = v
                vector<IntegerVariableCondition> xieqvs;
                for (const auto & var : x)
                    xieqvs.push_back(var != v);
                map->emplace(v,
                    recover_am1<IntegerVariableCondition>(
                        *logger, ProofLevel::Top, xieqvs, [&](const IntegerVariableCondition & c1, const IntegerVariableCondition & c2) -> ProofLine {
                            return logger->emit(RUPProofRule{}, WPBSum{} + 1_i * c1 + 1_i * c2 >= 1_i, ProofLevel::Temporary);
                        }));
            }
        };

        propagators.install_initialiser([x = _x, y_start = _y_start, y_size = _y.size(), x_value_am1s = _x_value_am1s, build_am1s = build_am1s](
                                            const State & state, auto & inference, ProofLogger * const logger) -> void {
            if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
                return;
            build_am1s(x, y_start, y_size, state, inference, logger, x_value_am1s);
        });
    }
    else {
        // No proof model: propagator still captures this map (must be non-null), but it stays empty.
        _x_value_am1s = make_shared<map<Integer, ProofLine>>();
    }

    // The values x takes are y's indices, so they start at y_start, not
    // x_start; the two only coincide when both arrays start at the same index.
    vector<Integer> x_values;
    for (const auto & [i, _] : enumerate(_y))
        x_values.push_back(Integer(i) + _y_start);

    propagators.install(
        constraint_id(),
        [x = _x, y = _y, x_start = _x_start, y_start = _y_start, x_values = move(x_values), x_value_am1s = _x_value_am1s,
            scratch = make_gac_all_different_scratch(), in_every_matching = make_shared<vector<uint8_t>>(), injection = is_injection(),
            constraint_id = constraint_id(),
            owner = constraint_id()](const State & state, auto & inf, ProofLogger * const logger) -> PropagatorState {
            // Channel x<->y and GAC-alldifferent on x feed each other: a GAC
            // removal on x can leave a y value with no back-support (more
            // channelling), which can force more x removals (more GAC), so a
            // single pass is not the fixpoint. Alternate to quiescence so the run
            // reaches its own fixpoint in one call and can claim idempotence (the
            // arithmetic-core pattern). A contradicting infer throws straight out.
            do {
                for (const auto & [i, x_i] : enumerate(x)) {
                    for (auto x_i_value : state.each_value_mutable(x_i))
                        if (! state.in_domain(y.at((x_i_value - y_start).as_index()), Integer(i) + x_start))
                            inf.infer(logger, x_i != x_i_value, JustifyUsingRUP{hints::Inverse{owner}},
                                ExplicitReason{ReasonLiterals{y.at((x_i_value - y_start).as_index()) != Integer(i) + x_start}});
                }

                // In the bijection form, y[i] = v needs x[v] = i, by the rows
                // from y to x. The injection form has no such rows: y[i] = v is
                // fine as long as nothing names i, which is the rule below.
                if (! injection)
                    for (const auto & [i, y_i] : enumerate(y)) {
                        for (auto y_i_value : state.each_value_mutable(y_i))
                            if (! state.in_domain(x.at((y_i_value - x_start).as_index()), Integer(i) + y_start))
                                inf.infer(logger, y_i != y_i_value, JustifyUsingRUP{hints::Inverse{owner}},
                                    ExplicitReason{ReasonLiterals{x.at((y_i_value - x_start).as_index()) != Integer(i) + y_start}});
                    }

                propagate_gac_all_different(constraint_id, x, x_values, vector<Integer>{}, *x_value_am1s.get(), *scratch, state, inf, logger,
                    injection ? in_every_matching.get() : nullptr);

                if (injection)
                    propagate_needed_values(owner, x, y, x_start, y_start, x_values, *in_every_matching, *x_value_am1s.get(), state, inf, logger);
            } while (inf.made_progress_since_last_check());

            return PropagatorState::EnableButIdempotent;
        },
        triggers);
}

auto Inverse::constraint_type() const -> std::string
{
    // cake_pb_cp's inverse is the bijection, and it rejects lists of different
    // lengths, so the injection form is named for itself.
    return is_injection() ? "inverse_injective" : "inverse";
}

auto Inverse::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    // cake_pb_cp wants each side grouped with its offset: a (list offset) pair,
    // i.e. `inverse ((X...) offx) ((Y...) offy)`. The outer list wrapping the
    // whole term is the SExpr::list returned here.
    std::vector<SExpr> xs;
    for (const auto & x : _x)
        xs.push_back(tracker.s_expr_term_of(x));
    std::vector<SExpr> ys;
    for (const auto & y : _y)
        ys.push_back(tracker.s_expr_term_of(y));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()),
        SExpr::list({SExpr::list(std::move(xs)), SExpr::atom(_x_start.to_string())}),
        SExpr::list({SExpr::list(std::move(ys)), SExpr::atom(_y_start.to_string())})});
}
