#include <gcs/constraint.hh>
#include <gcs/constraints/global_cardinality/global_cardinality.hh>
#include <gcs/constraints/global_cardinality/hints.hh>
#include <gcs/expression.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <cstddef>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::holds_alternative;
using std::make_unique;
using std::move;
using std::pair;
using std::unique_ptr;
using std::vector;
using std::ranges::binary_search;
using std::ranges::sort;

GlobalCardinality::GlobalCardinality(vector<IntegerVariableID> vars, vector<Integer> values, vector<IntegerVariableID> counts) :
    _vars(move(vars)), _values(move(values)), _counts(move(counts))
{
}

auto GlobalCardinality::with_consistency(GlobalCardinalityConsistency level) -> GlobalCardinality &
{
    _level = level;
    return *this;
}

auto GlobalCardinality::with_closed(std::optional<bool> closed) -> GlobalCardinality &
{
    _closed = closed.value_or(true);
    return *this;
}

auto GlobalCardinality::sort_cover_values() -> void
{
    vector<std::size_t> order(_values.size());
    for (std::size_t i = 0; i < order.size(); ++i)
        order[i] = i;
    sort(order, [&](std::size_t a, std::size_t b) { return _values[a] < _values[b]; });
    vector<Integer> sorted_values;
    vector<IntegerVariableID> sorted_counts;
    sorted_values.reserve(_values.size());
    sorted_counts.reserve(_counts.size());
    for (auto i : order) {
        sorted_values.push_back(_values[i]);
        sorted_counts.push_back(_counts[i]);
    }
    _values = move(sorted_values);
    _counts = move(sorted_counts);
}

auto GlobalCardinality::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<GlobalCardinality>(_vars, _values, _counts);
    cloned->with_consistency(_level).with_closed(_closed);
    if (holds_alternative<consistency::BC>(_level))
        cloned->sort_cover_values();
    return cloned;
}

auto GlobalCardinality::define_proof_model(ProofModel & model, const State &) -> void
{
    // The closed restriction: every variable takes one of the cover values.
    // `<i>_al1` is cake_pb_cp's own label for this row
    // (cencode_global_cardinality_aux's cat_least_one, prefixed by the variable
    // index), matching the `<j>_le`/`<j>_ge` convention the count rows use.
    //
    // An empty sum here means the variable's domain and the cover are disjoint,
    // so `0 >= 1` is the right row: the constraint is unsatisfiable, and saying
    // so definitionally is better than needing a propagator to discover it.
    if (_closed)
        for (const auto & [i, var] : enumerate(_vars)) {
            WPBSum sum;
            for (const auto & value : _values)
                if (! is_literally_false(var == value))
                    sum += 1_i * (var == value);
            model.add_labelled_constraint(constraint_id(), std::to_string(i) + "_al1", sum >= 1_i);
        }

    for (const auto & [j, value] : enumerate(_values)) {
        WPBSum sum;
        for (const auto & var : _vars)
            sum += 1_i * (var == value);
        // cake_pb_cp labels the per-value count equality @c[<id>][<j>_le]/[<j>_ge]:
        // the value index lives in the annotation tag, not the constraint name (a
        // name-embedded index could collide with a sibling constraint's name).
        _count_lines.push_back(
            model.add_labelled_constraint(constraint_id(), std::to_string(j) + "_le", std::to_string(j) + "_ge", sum == 1_i * _counts[j]));
    }
}

auto GlobalCardinality::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());
    triggers.on_bounds.insert(triggers.on_bounds.end(), _counts.begin(), _counts.end());

    // Closed: restrict every variable to the cover values. One propagator over
    // all of them, and idempotent -- once a domain is inside the cover it stays
    // there, since domains only shrink -- so this fires once and then finds
    // nothing. Each contiguous run of uncovered values is one interval
    // conclusion, RUP against that variable's `<i>_al1` row: asserting the
    // variable is in [lo, hi] walks the order chain past every cover value into
    // the disjunction. This is also what lets the GAC propagator hand it the
    // no-cover-value-left case rather than raising an unjustified contradiction.
    if (_closed) {
        // sort_cover_values() only runs on the BC path, so sort a copy rather
        // than assume _values is ordered.
        auto sorted_cover = _values;
        sort(sorted_cover);

        Triggers closed_triggers;
        closed_triggers.on_change.insert(closed_triggers.on_change.end(), _vars.begin(), _vars.end());
        propagators.install(
            constraint_id(),
            [vars = _vars, cover = sorted_cover, owner = constraint_id()](
                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                for (const auto & var : vars) {
                    vector<pair<Integer, Integer>> runs;
                    for (auto v : state.each_value_immutable(var)) {
                        if (binary_search(cover, v))
                            continue;
                        if (! runs.empty() && runs.back().second + 1_i == v)
                            runs.back().second = v;
                        else
                            runs.emplace_back(v, v);
                    }
                    for (const auto & [lo, hi] : runs)
                        inference.infer_not_in_range(logger, var, lo, hi, JustifyUsingRUP{hints::GlobalCardinality{owner}}, NoReason{});
                }
                return PropagatorState::Enable;
            },
            closed_triggers);
    }

    overloaded{[&](const consistency::BC &) {
                   propagators.install(
                       constraint_id(),
                       [vars = _vars, owner = constraint_id(), values = _values, counts = _counts, count_lines = _count_lines](
                           const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                           return propagate_bounds_global_cardinality(vars, owner, values, counts, count_lines, state, inference, logger);
                       },
                       triggers);
               },
        [&](const consistency::GAC &) {
            propagators.install(
                constraint_id(),
                [vars = _vars, owner = constraint_id(), values = _values, counts = _counts, closed = _closed, count_lines = _count_lines,
                    scratch = make_gac_global_cardinality_scratch()](
                    const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    return propagate_gac_global_cardinality(vars, owner, values, counts, closed, count_lines, *scratch, state, inference, logger);
                },
                triggers);
        }}
        .visit(_level);
}

// The name records which propagator ran, matching what cake_pb_cp's parser
// and the .scp reader expect (the OPB encoding itself is level-independent).
auto GlobalCardinality::constraint_type() const -> std::string
{
    return holds_alternative<consistency::GAC>(_level) ? (_closed ? "gacglobalcardinalityclosed" : "gacglobalcardinality")
                                                       : (_closed ? "boundsglobalcardinalityclosed" : "boundsglobalcardinality");
}

auto GlobalCardinality::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> vars, values, counts;
    for (const auto & var : _vars)
        vars.push_back(tracker.s_expr_term_of(var));
    for (const auto & val : _values)
        values.push_back(SExpr::atom(val.to_string()));
    for (const auto & c : _counts)
        counts.push_back(tracker.s_expr_term_of(c));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(move(vars)), SExpr::list(move(values)),
        SExpr::list(move(counts))});
}
