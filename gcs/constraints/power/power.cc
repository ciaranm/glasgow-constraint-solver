#include <gcs/constraints/innards/arithmetic_utils.hh>
#include <gcs/constraints/innards/linear_stages.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/multiply/multiply_bc.hh>
#include <gcs/constraints/power/hints.hh>
#include <gcs/constraints/power/power.hh>
#include <gcs/constraints/power/power_table.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <cstddef>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::clamp;
using std::make_unique;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    // Above this exponent, no base of magnitude two or more has a
    // representable power, so the constraint collapses to a case analysis on
    // base in {-1, 0, 1}.
    constexpr long long largest_meaningful_exponent = 62;

    // A corner of a product-bound computation, saturating at +-m rather than
    // overflowing: the auxiliary chain variables are clamped anyway.
    auto saturating_product(Integer a, Integer b, Integer m) -> Integer
    {
        if (auto p = product_if_representable(a, b))
            return clamp(*p, -m, m);
        return ((a > 0_i) == (b > 0_i)) ? m : -m;
    }
}

Power::Power(IntegerVariableID base, IntegerVariableID exponent, IntegerVariableID result) : _base(base), _exponent(exponent), _result(result)
{
}

auto Power::with_consistency(PowerConsistency level) -> Power &
{
    _level = level;
    return *this;
}

auto Power::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<Power>(_base, _exponent, _result);
    cloned->with_consistency(_level);
    return cloned;
}

auto Power::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    auto a1 = affine_of(_base), a2 = affine_of(_exponent), a3 = affine_of(_result);

    // A variable exponent is rare and has no sensible PB encoding: it gets the
    // one remaining materialised table.
    if (a2.var) {
        PowerTable table{_base, _exponent, _result};
        table.set_constraint_id(constraint_id());
        move(table).install(propagators, initial_state, optional_model);
        return;
    }

    auto k = a2.offset;
    auto label = as_string(constraint_id());

    vector<LinearStage> stages;
    auto add_equality = [&](const WeightedSum & sum, Integer value, const string & role) {
        add_equality_stage(stages, optional_model, label, sum, value, role);
    };
    auto add_le = [&](const WeightedSum & sum, Integer value, const string & role, const optional<IntegerVariableCondition> & gate) {
        add_le_stage(stages, optional_model, label, sum, value, role, gate);
    };
    auto add_gated_equality = [&](const IntegerVariableCondition & gate, Integer value, const string & role) {
        // an equality under a gate, as its two half-reified halves
        add_le(WeightedSum{} + 1_i * _result, value, role + "hi", gate);
        add_le(WeightedSum{} + -1_i * _result, -value, role + "lo", gate);
    };

    // One multiplication link of the chain, with its own encoding block
    // (role-prefixed) and persistent bit-product state.
    struct MultLink
    {
        SimpleIntegerVariableID a, b, product;
        mult_bc::EncodingData encoding;
        ConstraintStateHandle bit_products_handle;
    };
    vector<MultLink> links;
    auto add_link = [&](const string & prefix, SimpleIntegerVariableID a, SimpleIntegerVariableID b, SimpleIntegerVariableID product) {
        mult_bc::EncodingData encoding;
        if (optional_model)
            encoding = mult_bc::define_encoding(*optional_model, initial_state, constraint_id(), label, prefix, a, b, product);
        auto handle = initial_state.add_persistent_constraint_state(encoding.initial_bit_products);
        links.emplace_back(MultLink{a, b, product, move(encoding), handle});
    };

    bool prune_zero_base = false;

    if (! a1.var) {
        // Both base and exponent constant: the result is a single value, or
        // nothing representable at all.
        if (auto val = checked_integer_power(a1.offset, k))
            add_equality(WeightedSum{} + 1_i * _result, *val, "value");
        else {
            // No representable result value exists (an overflowing power, or
            // zero to a negative power), so the constraint itself is the
            // empty relation, like a Table with no tuples.
            if (optional_model)
                optional_model->add_constraint("Power", "no representable result", WPBSum{} >= 1_i);
            propagators.install_initial_contradiction("no representable power result", JustifyUsingRUP{hints::Power{constraint_id()}});
            return;
        }
    }
    else if (k == 0_i) {
        // Anything (including zero) to the zeroth power is one.
        add_equality(WeightedSum{} + 1_i * _result, 1_i, "value");
    }
    else if (k == 1_i) {
        add_equality(WeightedSum{} + 1_i * _base + -1_i * _result, 0_i, "sum");
    }
    else if (k < 0_i || k.raw_value > largest_meaningful_exponent) {
        // A negative exponent means 1 div base^|k|, truncated: 1 for base 1,
        // parity of |k| decides for base -1, no support at all for base 0, and
        // 0 for everything else. An enormous positive exponent is the same
        // case analysis except that base 0 gives 0 and bigger bases have no
        // representable power.
        auto parity = ((k.raw_value % 2) == 0) ? 1_i : -1_i;
        if (k < 0_i) {
            if (optional_model)
                optional_model->add_labelled_constraint(
                    label, "nonzero", "Power", "base is not zero", WPBSum{} + 1_i * (_base >= 1_i) + 1_i * (_base < 0_i) >= 1_i);
            prune_zero_base = true;

            add_gated_equality(_base >= 2_i, 0_i, "bigpos");
            add_gated_equality(_base < -1_i, 0_i, "bigneg");
        }
        else {
            // base in {-1, 0, 1}, since 2^63 and up do not fit
            add_le(WeightedSum{} + 1_i * _base, 1_i, "basehi", nullopt);
            add_le(WeightedSum{} + -1_i * _base, 1_i, "baselo", nullopt);
            add_gated_equality(_base == 0_i, 0_i, "zero");
        }

        add_gated_equality(_base == 1_i, 1_i, "one");
        add_gated_equality(_base == -1_i, parity, "minusone");
    }
    else {
        // 2 <= k <= 62: a chain of multiplications. In any solution the
        // intermediate power's magnitude is bounded by max(1, |result|) --
        // for |base| <= 1 trivially, and for |base| >= 2 because it divides
        // the result -- so the auxiliaries' ranges are clamped by the
        // result's. That keeps a hopeless chain (say 10^20 with a small
        // result) failing by propagation rather than overflowing at install
        // time. The base multiplies itself on the first link, so it gets a
        // plain copy; a view base gets channelled to a plain variable first.
        auto [zlo, zhi] = initial_state.bounds(_result);
        auto m = max({1_i, zlo < 0_i ? -zlo : zlo, zhi < 0_i ? -zhi : zhi});

        auto base_eff = *a1.var;
        if (a1.coeff != 1_i || a1.offset != 0_i) {
            auto [blo, bhi] = initial_state.bounds(_base);
            auto base_plain = initial_state.allocate_integer_variable_with_state(blo, bhi);
            if (optional_model)
                optional_model->set_up_integer_variable(base_plain, blo, bhi, "aux_power_base" + to_string(base_plain.index), nullopt);
            add_equality(WeightedSum{} + 1_i * base_plain + -1_i * _base, 0_i, "base");
            base_eff = base_plain;
        }

        auto [blo, bhi] = initial_state.bounds(base_eff);
        auto base_copy = initial_state.allocate_integer_variable_with_state(blo, bhi);
        if (optional_model)
            optional_model->set_up_integer_variable(base_copy, blo, bhi, "aux_power_copy" + to_string(base_copy.index), nullopt);
        add_equality(WeightedSum{} + 1_i * base_eff + -1_i * base_copy, 0_i, "copy");

        bool result_plain = a3.var && a3.coeff == 1_i && a3.offset == 0_i;
        auto prev = base_eff;
        auto other = base_copy;
        for (long long i = 2; i <= k.raw_value; ++i) {
            SimpleIntegerVariableID t = prev;
            bool is_last = i == k.raw_value;
            if (is_last && result_plain && *a3.var != prev && *a3.var != other)
                t = *a3.var;
            else {
                auto [plo, phi] = initial_state.bounds(prev);
                auto [xlo, xhi] = initial_state.bounds(other);
                auto lo = min({saturating_product(plo, xlo, m), saturating_product(plo, xhi, m), saturating_product(phi, xlo, m),
                    saturating_product(phi, xhi, m)});
                auto hi = max({saturating_product(plo, xlo, m), saturating_product(plo, xhi, m), saturating_product(phi, xlo, m),
                    saturating_product(phi, xhi, m)});
                t = initial_state.allocate_integer_variable_with_state(lo, hi);
                if (optional_model)
                    optional_model->set_up_integer_variable(t, lo, hi, "aux_power" + to_string(t.index), nullopt);
            }

            add_link("c" + to_string(i) + "_", prev, other, t);

            if (is_last && ! (result_plain && t == *a3.var))
                add_equality(WeightedSum{} + 1_i * t + -1_i * _result, 0_i, "resultsum");

            prev = t;
            other = base_eff;
        }
    }

    if ((! stages.empty()) || (! links.empty()) || prune_zero_base) {
        Triggers triggers;
        vector<IntegerVariableID> watched;
        auto watch = [&](const IntegerVariableID & v) {
            if (! holds_alternative<ConstantIntegerVariableID>(v) && std::find(watched.begin(), watched.end(), v) == watched.end())
                watched.push_back(v);
        };
        watch(_base);
        watch(_result);
        for (const auto & link : links) {
            watch(link.a);
            watch(link.b);
            watch(link.product);
        }
        triggers.on_bounds = watched;

        propagators.install(
            constraint_id(),
            [stages = stages, links = links, prune_zero_base = prune_zero_base, base = _base, owner = constraint_id()](
                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                do {
                    if (prune_zero_base && state.in_domain(base, 0_i))
                        inference.infer(logger, base != 0_i, JustifyUsingRUP{hints::Power{owner}}, ExplicitReason{ReasonLiterals{}});

                    if (! propagate_stages(stages, state, inference, logger, owner))
                        return PropagatorState::Enable;

                    for (const auto & link : links)
                        mult_bc::propagate(link.a, link.b, link.product, state, inference, logger, link.encoding, link.bit_products_handle, owner);
                } while (inference.did_anything_since_last_call_inside_propagator());

                return PropagatorState::Enable;
            },
            triggers);
    }

    // Tabulation for GAC over the base and result (the exponent is constant
    // here). The auxiliary chain variables are not enumerated; they pin by
    // unit propagation through the multiplication links.
    TabulationVariables enum_vars;
    auto px = enum_vars.position_of(*a1.var);
    optional<size_t> pz = a3.var ? optional{enum_vars.position_of(*a3.var)} : nullopt;

    // the result is a function of the base, pinned by unit propagation
    // through the multiplication chain; the base is not a function of the
    // result (even exponents have two roots).
    vector<DeterminedVariable> determined;
    if (pz && *pz != px)
        determined.push_back({*a3.var, [a1, a3, k, px](const vector<Integer> & vals) -> optional<Integer> {
                                  auto xv = a1.coeff * vals[px] + a1.offset;
                                  auto want = checked_integer_power(xv, k);
                                  if ((! want) || (*want - a3.offset) % a3.coeff != 0_i)
                                      return nullopt;
                                  return (*want - a3.offset) / a3.coeff;
                              }});

    if (want_tabulation(_level, enum_vars.vars(), determined, initial_state)) {
        auto accept = [a1, a3, k, px, pz](const vector<Integer> & vals) -> bool {
            auto xv = a1.coeff * vals[px] + a1.offset;
            auto zv = pz ? a3.coeff * vals[*pz] + a3.offset : a3.offset;
            auto want = checked_integer_power(xv, k);
            return want && *want == zv;
        };

        install_tabulation<hints::Power>(
            propagators, constraint_id(), enum_vars.vars(), move(determined), nullopt, accept, "powtab", "building GAC table for power");
    }
}

auto Power::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("power"),
        SExpr::list({tracker.s_expr_term_of(_base), tracker.s_expr_term_of(_exponent), tracker.s_expr_term_of(_result)})});
}
