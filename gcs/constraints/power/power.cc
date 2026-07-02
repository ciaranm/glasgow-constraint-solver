#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/arithmetic_utils.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/linear/linear_equality.hh>
#include <gcs/constraints/multiply/multiply.hh>
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

using std::make_shared;
using std::make_unique;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::size_t;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    // Above this exponent, no base of magnitude two or more has a
    // representable power, so the constraint collapses to a case analysis on
    // base in {-1, 0, 1}.
    constexpr long long largest_meaningful_exponent = 62;

    auto clamp_to(Integer v, Integer m) -> Integer
    {
        return min(max(v, -m), m);
    }

    // A corner of a product-bound computation, saturating at +-m rather than
    // overflowing: the auxiliary chain variables are clamped anyway.
    auto saturating_product(Integer a, Integer b, Integer m) -> Integer
    {
        if (auto p = product_if_representable(a, b))
            return clamp_to(*p, m);
        return ((a > 0_i) == (b > 0_i)) ? m : -m;
    }
}

Power::Power(IntegerVariableID base, IntegerVariableID exponent, IntegerVariableID result, PowerConsistency level) :
    _base(base), _exponent(exponent), _result(result), _level(level)
{
}

auto Power::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Power>(_base, _exponent, _result, _level);
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

    // Both base and exponent constant: the result is a single value, or
    // nothing representable at all.
    if (! a1.var) {
        if (auto val = checked_integer_power(a1.offset, k)) {
            LinearEquality lin{WeightedSum{} + 1_i * _result, *val};
            lin.set_constraint_id(constraint_id());
            move(lin).install(propagators, initial_state, optional_model);
        }
        else {
            // No representable result value exists (an overflowing power, or
            // zero to a negative power), so the constraint itself is the
            // empty relation, like a Table with no tuples.
            if (optional_model)
                optional_model->add_constraint("Power", "no representable result", WPBSum{} >= 1_i);
            propagators.install_initial_contradiction("no representable power result", JustifyUsingRUP{hints::Power{constraint_id()}});
        }
        return;
    }

    if (k == 0_i) {
        // Anything (including zero) to the zeroth power is one.
        LinearEquality lin{WeightedSum{} + 1_i * _result, 1_i};
        lin.set_constraint_id(constraint_id());
        move(lin).install(propagators, initial_state, optional_model);
        return;
    }

    if (k == 1_i) {
        LinearEquality lin{WeightedSum{} + 1_i * _base + -1_i * _result, 0_i};
        lin.set_constraint_id(constraint_id());
        move(lin).install(propagators, initial_state, optional_model);
    }
    else if (k < 0_i || k.raw_value > largest_meaningful_exponent) {
        // A negative exponent means 1 div base^|k|, truncated: 1 for base 1,
        // parity of |k| decides for base -1, no support at all for base 0, and
        // 0 for everything else. An enormous positive exponent is the same
        // case analysis except that base 0 gives 0 and bigger bases have no
        // representable power.
        if (k < 0_i) {
            NotEquals ne{_base, 0_c};
            ne.set_constraint_id(child_constraint_id(constraint_id(), "nonzero"));
            move(ne).install(propagators, initial_state, optional_model);

            LinearEqualityIf big_pos{WeightedSum{} + 1_i * _result, 0_i, _base >= 2_i};
            big_pos.set_constraint_id(child_constraint_id(constraint_id(), "bigpos"));
            move(big_pos).install(propagators, initial_state, optional_model);
            LinearEqualityIf big_neg{WeightedSum{} + 1_i * _result, 0_i, _base < -1_i};
            big_neg.set_constraint_id(child_constraint_id(constraint_id(), "bigneg"));
            move(big_neg).install(propagators, initial_state, optional_model);
        }
        else {
            // base in {-1, 0, 1}, since 2^63 and up do not fit
            LessThanEqual le{_base, 1_c};
            le.set_constraint_id(child_constraint_id(constraint_id(), "basehi"));
            move(le).install(propagators, initial_state, optional_model);
            GreaterThanEqual ge{_base, -1_c};
            ge.set_constraint_id(child_constraint_id(constraint_id(), "baselo"));
            move(ge).install(propagators, initial_state, optional_model);

            LinearEqualityIf zero{WeightedSum{} + 1_i * _result, 0_i, _base == 0_i};
            zero.set_constraint_id(child_constraint_id(constraint_id(), "zero"));
            move(zero).install(propagators, initial_state, optional_model);
        }

        LinearEqualityIf one{WeightedSum{} + 1_i * _result, 1_i, _base == 1_i};
        one.set_constraint_id(child_constraint_id(constraint_id(), "one"));
        move(one).install(propagators, initial_state, optional_model);

        auto parity = ((k.raw_value % 2) == 0) ? 1_i : -1_i;
        LinearEqualityIf minus_one{WeightedSum{} + 1_i * _result, parity, _base == -1_i};
        minus_one.set_constraint_id(child_constraint_id(constraint_id(), "minusone"));
        move(minus_one).install(propagators, initial_state, optional_model);
    }
    else {
        // 2 <= k <= 62: a chain of multiplications through auxiliary
        // variables. In any solution the intermediate power's magnitude is
        // bounded by max(1, |result|) -- for |base| <= 1 trivially, and for
        // |base| >= 2 because it divides the result -- so the auxiliaries'
        // ranges are clamped by the result's. That keeps a hopeless chain
        // (say 10^20 with a small result) failing by propagation rather than
        // overflowing at install time.
        auto [zlo, zhi] = initial_state.bounds(_result);
        auto m = max({1_i, zlo < 0_i ? -zlo : zlo, zhi < 0_i ? -zhi : zhi});

        auto prev = _base;
        for (long long i = 2; i < k.raw_value; ++i) {
            auto [plo, phi] = initial_state.bounds(prev);
            auto [xlo, xhi] = initial_state.bounds(_base);
            auto lo = min(
                {saturating_product(plo, xlo, m), saturating_product(plo, xhi, m), saturating_product(phi, xlo, m), saturating_product(phi, xhi, m)});
            auto hi = max(
                {saturating_product(plo, xlo, m), saturating_product(plo, xhi, m), saturating_product(phi, xlo, m), saturating_product(phi, xhi, m)});
            auto t = initial_state.allocate_integer_variable_with_state(lo, hi);
            if (optional_model)
                optional_model->set_up_integer_variable(t, lo, hi, "aux_power" + to_string(t.index), nullopt);

            Multiply mult{prev, _base, t, consistency::BC{}};
            mult.set_constraint_id(child_constraint_id(constraint_id(), "chain" + to_string(i)));
            move(mult).install(propagators, initial_state, optional_model);
            prev = t;
        }

        Multiply last{prev, _base, _result, consistency::BC{}};
        last.set_constraint_id(child_constraint_id(constraint_id(), "chainlast"));
        move(last).install(propagators, initial_state, optional_model);
    }

    // Tabulation for GAC over the base and result (the exponent is constant
    // here). The auxiliary chain variables are not enumerated; they pin by
    // unit propagation through the Multiply children.
    vector<SimpleIntegerVariableID> enum_vars;
    auto position_of = [&](const SimpleIntegerVariableID & v) -> size_t {
        for (size_t i = 0; i < enum_vars.size(); ++i)
            if (enum_vars[i] == v)
                return i;
        enum_vars.push_back(v);
        return enum_vars.size() - 1;
    };
    auto px = position_of(*a1.var);
    optional<size_t> pz = a3.var ? optional{position_of(*a3.var)} : nullopt;

    bool tabulate = overloaded{[&](const consistency::GAC &) { return true; }, [&](const consistency::BC &) { return false; },
        [&](const consistency::Auto &) {
            long long size = 1;
            for (const auto & v : enum_vars)
                if (__builtin_mul_overflow(size, initial_state.domain_size(v).raw_value, &size))
                    return false;
            return size <= default_tabulation_threshold;
        }}.visit(_level);

    if (tabulate) {
        auto accept = [a1, a3, k, px, pz](const vector<Integer> & vals) -> bool {
            auto xv = a1.coeff * vals[px] + a1.offset;
            auto zv = pz ? a3.coeff * vals[*pz] + a3.offset : a3.offset;
            auto want = checked_integer_power(xv, k);
            return want && *want == zv;
        };

        Triggers triggers;
        for (const auto & v : enum_vars)
            triggers.on_change.push_back(v);

        auto data = make_shared<optional<ExtensionalData>>(nullopt);
        propagators.install_initialiser(
            [data = data, enumerate_over = vector<IntegerVariableID>(enum_vars.begin(), enum_vars.end()), accept = accept, owner = constraint_id()](
                State & state, auto & inference, ProofLogger * const logger) {
                *data = build_table_in_proof(enumerate_over, accept, "powtab", "building GAC table for power", state, logger);
                if (! data->has_value())
                    inference.infer(logger, FalseLiteral{}, JustifyUsingRUP{hints::Power{owner}}, ExplicitReason{ReasonLiterals{}});
            },
            InitialiserPriority::Expensive);

        propagators.install(
            constraint_id(),
            [data = data, owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                if (data->has_value())
                    return propagate_extensional(data->value(), state, inference, logger, hints::Power{owner});
                else
                    return PropagatorState::DisableUntilBacktrack;
            },
            triggers);
    }
}

auto Power::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("power"),
        SExpr::list({tracker.s_expr_term_of(_base), tracker.s_expr_term_of(_exponent), tracker.s_expr_term_of(_result)})});
}
