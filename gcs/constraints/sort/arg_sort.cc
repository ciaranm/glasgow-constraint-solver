#include <gcs/constraints/sort/arg_sort.hh>
#include <gcs/exception.hh>
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
#include <format>
#include <print>
using std::format;
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
using fmt::format;
#endif

#include <algorithm>
#include <sstream>
#include <string>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

ArgSort::ArgSort(vector<IntegerVariableID> x, vector<IntegerVariableID> p, Integer offset) :
    _x(move(x)),
    _p(move(p)),
    _offset(offset)
{
}

auto ArgSort::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ArgSort>(_x, _p, _offset);
}

auto ArgSort::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto ArgSort::prepare(Propagators & propagators, State & initial_state, ProofModel * const optional_model) -> bool
{
    if (_x.size() != _p.size())
        throw InvalidProblemDefinitionException{"ArgSort constraint on different sized arrays"};

    if (_x.empty())
        return false;

    // The permutation values live in [offset, offset + n - 1]; pin those bounds
    // so the index arithmetic (and the OPB index range) is sound.
    for (const auto & v : _p) {
        propagators.define_bound(initial_state, optional_model, v, Bound::Lower, _offset, "ArgSort", "permutation range");
        propagators.define_bound(initial_state, optional_model, v, Bound::Upper, _offset + Integer(_x.size()) - 1_i, "ArgSort", "permutation range");
    }

    // Record the value range of x, for the proof-only "sorted value" variables.
    bool first = true;
    for (const auto & v : _x) {
        auto [lo, hi] = initial_state.bounds(v);
        if (first) {
            _lowest_x = lo;
            _highest_x = hi;
            first = false;
        }
        else {
            _lowest_x = std::min(_lowest_x, lo);
            _highest_x = std::max(_highest_x, hi);
        }
    }

    return true;
}

auto ArgSort::define_proof_model(ProofModel & model) -> void
{
    auto n = _x.size();

    // p is a permutation of {offset, ..., offset + n - 1}: at most one position
    // can take each value (with the range bounds above, this forces a bijection).
    for (Integer v = _offset; v < _offset + Integer(n); ++v) {
        WPBSum at_most_one;
        for (const auto & p_j : _p)
            at_most_one += 1_i * (p_j == v);
        model.add_constraint("ArgSort", "permutation", move(at_most_one) <= 1_i);
    }

    // xp[j] is the value at sorted position j, i.e. xp[j] = x[p[j] - offset].
    // Channel it in via the permutation literals.
    vector<ProofOnlySimpleIntegerVariableID> xp;
    for (size_t j = 0; j < n; ++j)
        xp.push_back(model.create_proof_only_integer_variable(
            _lowest_x, _highest_x, format("argsort_xp_{}", j), IntegerVariableProofRepresentation::Bits));

    for (size_t j = 0; j < n; ++j)
        for (size_t k = 0; k < n; ++k)
            model.add_constraint("ArgSort", "value channel",
                WPBSum{} + 1_i * xp[j] + -1_i * _x[k] == 0_i,
                HalfReifyOnConjunctionOf{{_p[j] == _offset + Integer(k)}});

    // Sorted, with a stable tie-break. For each consecutive pair:
    //   xp[j] <= xp[j+1]                      (non-decreasing)
    //   eq_j <-> xp[j] >= xp[j+1]             (equality, given the line above)
    //   eq_j -> p[j] + 1 <= p[j+1]            (ties broken by original index)
    for (size_t j = 0; j + 1 < n; ++j) {
        model.add_constraint("ArgSort", "non-decreasing",
            WPBSum{} + 1_i * xp[j] + -1_i * xp[j + 1] <= 0_i);

        auto eq = model.create_proof_flag_fully_reifying("argsort_eq",
            "ArgSort", "tie value",
            WPBSum{} + 1_i * xp[j] + -1_i * xp[j + 1] >= 0_i);

        model.add_constraint("ArgSort", "stable tie-break",
            WPBSum{} + 1_i * _p[j] + -1_i * _p[j + 1] <= -1_i,
            HalfReifyOnConjunctionOf{{eq}});
    }
}

auto ArgSort::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_instantiated.insert(triggers.on_instantiated.end(), _x.begin(), _x.end());
    triggers.on_instantiated.insert(triggers.on_instantiated.end(), _p.begin(), _p.end());

    // Checking-only propagator: act only once every element of x and p is
    // fixed, then verify p really is the stable sorting permutation of x.
    propagators.install([x = _x, p = _p, offset = _offset](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        for (const auto & v : x)
            if (! state.has_single_value(v))
                return PropagatorState::Enable;
        for (const auto & v : p)
            if (! state.has_single_value(v))
                return PropagatorState::Enable;

        auto all_vars = [&]() {
            vector<IntegerVariableID> vars = x;
            vars.insert(vars.end(), p.begin(), p.end());
            return vars;
        };

        auto n = x.size();
        vector<Integer> p_vals;
        for (const auto & v : p)
            p_vals.push_back(state(v));

        // p must be a permutation of {offset, ..., offset + n - 1}.
        vector<bool> seen(n, false);
        for (auto pv : p_vals) {
            auto idx = (pv - offset).raw_value;
            if (idx < 0 || idx >= static_cast<long long>(n) || seen[idx])
                inference.contradiction(logger, JustifyUsingRUP{}, generic_reason(state, all_vars()));
            seen[idx] = true;
        }

        // x[p[j]] must be non-decreasing, with ties broken by index.
        for (size_t j = 0; j + 1 < n; ++j) {
            auto a = state(x[(p_vals[j] - offset).as_index()]);
            auto b = state(x[(p_vals[j + 1] - offset).as_index()]);
            if (a > b || (a == b && p_vals[j] >= p_vals[j + 1]))
                inference.contradiction(logger, JustifyUsingRUP{}, generic_reason(state, all_vars()));
        }

        return PropagatorState::DisableUntilBacktrack;
    },
        triggers);
}

auto ArgSort::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} arg_sort\n          (", _name);
    for (const auto & v : _x)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, ")\n          (");
    for (const auto & v : _p)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, ")\n          {})", _offset);

    return s.str();
}
