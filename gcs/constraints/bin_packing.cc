#include <gcs/constraints/bin_packing.hh>
#include <gcs/exception.hh>
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

#include <sstream>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
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

BinPacking::BinPacking(vector<IntegerVariableID> items, vector<Integer> sizes,
    vector<IntegerVariableID> loads, bool bounds_only) :
    _items(move(items)),
    _sizes(move(sizes)),
    _loads(move(loads)),
    _capacities(),
    _have_loads(true),
    _bounds_only(bounds_only)
{
}

BinPacking::BinPacking(vector<IntegerVariableID> items, vector<Integer> sizes,
    vector<Integer> capacities, bool bounds_only) :
    _items(move(items)),
    _sizes(move(sizes)),
    _loads(),
    _capacities(move(capacities)),
    _have_loads(false),
    _bounds_only(bounds_only)
{
}

auto BinPacking::clone() const -> unique_ptr<Constraint>
{
    if (_have_loads)
        return make_unique<BinPacking>(_items, _sizes, _loads, _bounds_only);
    return make_unique<BinPacking>(_items, _sizes, _capacities, _bounds_only);
}

auto BinPacking::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto BinPacking::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    if (_items.size() != _sizes.size())
        throw InvalidProblemDefinitionException{"BinPacking: items and sizes must have the same size"};

    for (auto & s : _sizes)
        if (s < 0_i)
            throw InvalidProblemDefinitionException{"BinPacking: item sizes must be non-negative"};

    auto num_bins = _have_loads ? _loads.size() : _capacities.size();
    if (num_bins == 0)
        throw InvalidProblemDefinitionException{"BinPacking: at least one bin is required"};

    auto max_bin = Integer(static_cast<long long>(num_bins) - 1);
    for (auto & item : _items) {
        auto [lo, hi] = initial_state.bounds(item);
        if (lo < 0_i || hi > max_bin)
            throw InvalidProblemDefinitionException{"BinPacking: item variable domain must lie within 0..num_bins-1"};
    }

    if (_have_loads) {
        for (auto & l : _loads)
            if (initial_state.lower_bound(l) < 0_i)
                throw InvalidProblemDefinitionException{"BinPacking: load variables must be non-negative"};
    }
    else {
        for (auto & c : _capacities)
            if (c < 0_i)
                throw InvalidProblemDefinitionException{"BinPacking: capacities must be non-negative"};
    }

    return true;
}

auto BinPacking::define_proof_model(ProofModel & model) -> void
{
    // Natural definition: for each bin b,
    //   sum_i { sizes[i] * [items[i] == b] } == loads[b]   (variable-load form)
    //   sum_i { sizes[i] * [items[i] == b] } <= cap[b]     (constant-cap form)
    //
    // The DAG-shaped scaffolding used by the eventual GAC propagator is
    // not part of this encoding; it will be derived inside the proof body
    // once, on first propagation, from these per-bin equations. See
    // dev_docs/bin-packing.md.
    auto num_bins = _have_loads ? _loads.size() : _capacities.size();
    for (size_t b = 0; b < num_bins; ++b) {
        auto bin_idx = Integer(static_cast<long long>(b));
        WPBSum sum;
        for (const auto & [i, item] : enumerate(_items))
            sum += _sizes[i] * (item == bin_idx);

        if (_have_loads)
            model.add_constraint(sum == 1_i * _loads[b]);
        else
            model.add_constraint(sum <= _capacities[b]);
    }
}

auto BinPacking::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _items.begin(), _items.end());
    if (_have_loads)
        triggers.on_bounds.insert(triggers.on_bounds.end(), _loads.begin(), _loads.end());

    // Stage 1 checker: fire only once every item is assigned. Pin each bin's
    // load (variable-load form) or assert the capacity (constant-cap form)
    // via RUP against the per-bin OPB equations. Stronger reasoning is
    // deferred to later stages — see dev_docs/bin-packing.md.
    propagators.install(
        [items = _items, sizes = _sizes, loads = _loads, capacities = _capacities, have_loads = _have_loads](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            vector<Integer> single_values;
            single_values.reserve(items.size());
            for (auto & item : items) {
                auto v = state.optional_single_value(item);
                if (! v)
                    return PropagatorState::Enable;
                single_values.push_back(*v);
            }

            auto num_bins = have_loads ? loads.size() : capacities.size();
            vector<Integer> bin_sums(num_bins, 0_i);
            for (size_t i = 0; i < items.size(); ++i)
                bin_sums[single_values[i].raw_value] += sizes[i];

            auto reason = generic_reason(state, items);

            for (size_t b = 0; b < num_bins; ++b) {
                if (have_loads) {
                    inference.infer_equal(logger, loads[b], bin_sums[b], JustifyUsingRUP{}, reason);
                }
                else if (bin_sums[b] > capacities[b]) {
                    inference.contradiction(logger, JustifyUsingRUP{}, reason);
                    return PropagatorState::DisableUntilBacktrack;
                }
            }

            return PropagatorState::DisableUntilBacktrack;
        },
        triggers);
}

auto BinPacking::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} binpacking (", _name);
    for (const auto & item : _items)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(item));
    print(s, " ) ( ");
    for (const auto & sz : _sizes)
        print(s, " {}", sz);
    print(s, " ) ");
    if (_have_loads) {
        print(s, "loads (");
        for (const auto & l : _loads)
            print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(l));
        print(s, " )");
    }
    else {
        print(s, "capacities (");
        for (const auto & c : _capacities)
            print(s, " {}", c);
        print(s, " )");
    }

    return s.str();
}
