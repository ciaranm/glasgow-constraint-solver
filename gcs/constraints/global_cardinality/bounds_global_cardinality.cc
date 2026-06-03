#include <gcs/constraints/global_cardinality/bounds_global_cardinality.hh>
#include <gcs/constraints/in.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <set>
#include <sstream>
#include <string>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

BoundsGlobalCardinality::BoundsGlobalCardinality(vector<IntegerVariableID> vars, vector<Integer> values,
    vector<IntegerVariableID> counts, bool closed) :
    _vars(move(vars)),
    _values(move(values)),
    _counts(move(counts)),
    _closed(closed)
{
}

auto BoundsGlobalCardinality::clone() const -> unique_ptr<Constraint>
{
    return make_unique<BoundsGlobalCardinality>(_vars, _values, _counts, _closed);
}

auto BoundsGlobalCardinality::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);

    // The closed restriction (every variable takes a cover value) is delegated
    // to a certified In constraint per variable.
    if (_closed)
        for (const auto & var : _vars)
            In{var, _values}.install(propagators, initial_state, optional_model);
}

auto BoundsGlobalCardinality::define_proof_model(ProofModel & model) -> void
{
    for (const auto & [j, value] : enumerate(_values)) {
        WPBSum sum;
        for (const auto & var : _vars)
            sum += 1_i * (var == value);
        _count_lines.push_back(model.add_constraint("GCC", "count for value", sum == 1_i * _counts[j]));
    }
}

auto BoundsGlobalCardinality::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());
    triggers.on_bounds.insert(triggers.on_bounds.end(), _counts.begin(), _counts.end());

    vector<IntegerVariableID> all_vars = _vars;
    all_vars.insert(all_vars.end(), _counts.begin(), _counts.end());

    propagators.install(
        [vars = _vars, values = _values, counts = _counts, count_lines = _count_lines, all_vars = move(all_vars)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            auto m = values.size();

            // Part 1: per-value (singleton Hall) reasoning, with real RUP
            // justifications. For each cover value this gives the count variable
            // its must-occur lower bound and can-occur upper bound, removes a
            // value whose upper capacity is saturated by the variables fixed to
            // it, and forces the variables into a value whose lower demand can
            // only just be met.
            for (const auto & [j, value] : enumerate(values)) {
                Reason fixed_eq;  // var == value, for variables fixed to value
                Reason absent_ne; // var != value, for variables without value
                Integer must = 0_i, can = 0_i;
                for (const auto & var : vars) {
                    if (state.in_domain(var, value)) {
                        ++can;
                        if (state.has_single_value(var)) {
                            ++must;
                            fixed_eq.emplace_back(var == value);
                        }
                    }
                    else
                        absent_ne.emplace_back(var != value);
                }

                auto [lb_j, ub_j] = state.bounds(counts[j]);

                // c_j >= must: the fixed variables alone force the count up.
                if (must > lb_j)
                    inference.infer(logger, counts[j] >= must, JustifyUsingRUP{},
                        ReasonFunction{[fixed_eq]() -> Reason { return fixed_eq; }});

                // c_j <= can: only the variables that can still take value may
                // contribute to the count.
                if (can < ub_j)
                    inference.infer(logger, counts[j] <= can, JustifyUsingRUP{},
                        ReasonFunction{[absent_ne]() -> Reason { return absent_ne; }});

                // Saturated capacity: if as many variables are already fixed to
                // value as the count's upper bound allows, no other variable may
                // take it.
                if (must == ub_j) {
                    Reason sat = fixed_eq;
                    sat.emplace_back(counts[j] <= ub_j);
                    for (const auto & var : vars)
                        if (state.in_domain(var, value) && ! state.has_single_value(var))
                            inference.infer(logger, var != value, JustifyUsingRUP{},
                                ReasonFunction{[sat]() -> Reason { return sat; }});
                }

                // Just-met demand: if only `can` variables can take value and the
                // count's lower bound needs all of them, each is forced to value.
                if (can == lb_j && can > 0_i) {
                    Reason force = absent_ne;
                    force.emplace_back(counts[j] >= lb_j);
                    for (const auto & var : vars)
                        if (state.in_domain(var, value) && ! state.has_single_value(var))
                            for (const auto & w : state.each_value_mutable(var))
                                if (w != value)
                                    inference.infer(logger, var != w, JustifyUsingRUP{},
                                        ReasonFunction{[force]() -> Reason { return force; }});
                }
            }

            // Part 2: multi-value Hall intervals over contiguous runs of the
            // (sorted, distinct) cover values. This is the genuine cross-value
            // strengthening beyond per-value reasoning; its justifications are
            // still asserted placeholders.
            for (std::size_t a = 0; a < m; ++a) {
                set<Integer> hall;
                Integer cap = 0_i, demand = 0_i;
                hall.insert(values[a]);
                {
                    auto [c_lo, c_hi] = state.bounds(counts[a]);
                    cap += c_hi;
                    demand += c_lo;
                }
                for (std::size_t b = a + 1; b < m; ++b) {
                    hall.insert(values[b]);
                    auto [c_lo, c_hi] = state.bounds(counts[b]);
                    cap += c_hi;
                    demand += c_lo;

                    auto domain_subset_of_hall = [&](const IntegerVariableID & var) -> bool {
                        for (const auto & val : state.each_value_immutable(var))
                            if (! hall.contains(val))
                                return false;
                        return true;
                    };
                    auto domain_meets_hall = [&](const IntegerVariableID & var) -> bool {
                        for (const auto & val : hall)
                            if (state.in_domain(var, val))
                                return true;
                        return false;
                    };

                    Integer confined_count = 0_i, potential_count = 0_i;
                    for (const auto & var : vars) {
                        if (domain_subset_of_hall(var))
                            ++confined_count;
                        if (domain_meets_hall(var))
                            ++potential_count;
                    }

                    for (std::size_t j = a; j <= b; ++j) {
                        auto [lb_j, ub_j] = state.bounds(counts[j]);
                        auto lower = confined_count - (cap - ub_j);
                        if (lower > lb_j)
                            inference.infer(logger, counts[j] >= lower, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
                        auto upper = potential_count - (demand - lb_j);
                        if (upper < ub_j)
                            inference.infer(logger, counts[j] <= upper, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
                    }

                    if (confined_count > cap) {
                        inference.contradiction(logger, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
                    }
                    else if (confined_count == cap) {
                        for (const auto & var : vars) {
                            if (domain_subset_of_hall(var))
                                continue;
                            for (const auto & val : hall)
                                if (state.in_domain(var, val))
                                    inference.infer(logger, var != val, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
                        }
                    }

                    if (potential_count < demand) {
                        inference.contradiction(logger, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
                    }
                    else if (potential_count == demand) {
                        for (const auto & var : vars)
                            if (domain_meets_hall(var))
                                for (const auto & val : state.each_value_mutable(var))
                                    if (! hall.contains(val))
                                        inference.infer(logger, var != val, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
                    }
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto BoundsGlobalCardinality::prepare(Propagators &, State &, ProofModel * const) -> bool
{
    return true;
}

auto BoundsGlobalCardinality::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} boundsglobalcardinality{} (", _name, _closed ? "closed" : "");
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") (");
    for (const auto & val : _values)
        print(s, " {}", val);
    print(s, ") (");
    for (const auto & c : _counts)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(c));
    print(s, ")");

    return s.str();
}
