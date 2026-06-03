#include <gcs/constraints/global_cardinality/bounds_global_cardinality.hh>
#include <gcs/constraints/in.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
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

            // Hall reasoning over contiguous runs of the (sorted, distinct)
            // cover values. The singleton intervals reproduce the per-value
            // must-occur/can-occur count bounds.
            for (std::size_t a = 0; a < m; ++a) {
                set<Integer> hall;
                Integer cap = 0_i, demand = 0_i;
                for (std::size_t b = a; b < m; ++b) {
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

                    vector<IntegerVariableID> confined;
                    for (const auto & var : vars)
                        if (domain_subset_of_hall(var))
                            confined.push_back(var);
                    auto confined_count = Integer(confined.size());

                    vector<IntegerVariableID> potential;
                    for (const auto & var : vars)
                        if (domain_meets_hall(var))
                            potential.push_back(var);
                    auto potential_count = Integer(potential.size());

                    // Tighten the count variables. At least `confined_count`
                    // variables take a hall value, so for each hall value j the
                    // others can absorb at most (cap - ub_j), forcing c_j up; and
                    // at most `potential_count` variables can take a hall value,
                    // with the others demanding at least (demand - lb_j), capping
                    // c_j from above.
                    for (std::size_t j = a; j <= b; ++j) {
                        auto [lb_j, ub_j] = state.bounds(counts[j]);
                        auto lower = confined_count - (cap - ub_j);
                        if (lower > lb_j)
                            inference.infer(logger, counts[j] >= lower, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
                        auto upper = potential_count - (demand - lb_j);
                        if (upper < ub_j)
                            inference.infer(logger, counts[j] <= upper, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
                    }

                    // Upper-capacity: a saturated hall set forbids its values
                    // elsewhere.
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

                    // Lower-demand: if only `demand` variables can supply the
                    // hall set's demand, they all must.
                    if (potential_count < demand) {
                        inference.contradiction(logger, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
                    }
                    else if (potential_count == demand) {
                        for (const auto & var : potential)
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
