#include <gcs/constraints/innards/product_encoding.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <util/overloaded.hh>

#include <utility>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::product_enc;

using std::get_if;
using std::max;
using std::pair;
using std::string;
using std::vector;

namespace
{
    // The four half-reified rows pinning mag = |v|: [v>=0] => mag = v and
    // [v<0] => mag = -v, with cake's role names <prefix><letter>{ge0,lt0}_{ge,le}.
    // A constant operand keeps the same four rows, cake style: the constant
    // folds into each row's degree and the sign gates become its pinned
    // n[k][ge0] atom (issue #483).
    auto emit_channel_rows(ProofModel & model, const ConstraintID & owner, IntegerVariableID v, const SimpleOrProofOnlyIntegerVariableID & mag,
        const string & role_prefix, const string & letter) -> MagnitudeChannel
    {
        auto as_term = [&](Integer coeff) -> Weighted<PseudoBooleanTerm> {
            return overloaded{[&](const SimpleIntegerVariableID & m) { return Weighted<PseudoBooleanTerm>{coeff, m}; },
                [&](const ProofOnlySimpleIntegerVariableID & m) { return Weighted<PseudoBooleanTerm>{coeff, m}; }}
                .visit(mag);
        };
        auto [ge0, lt0] = [&]() -> pair<HalfReifyOnConjunctionOf, HalfReifyOnConjunctionOf> {
            if (auto cv = get_if<ConstantIntegerVariableID>(&v)) {
                auto atoms = model.cake_constant_atoms(cv->const_value);
                return {HalfReifyOnConjunctionOf{atoms.ge0}, HalfReifyOnConjunctionOf{! atoms.ge0}};
            }
            return {HalfReifyOnConjunctionOf{v >= 0_i}, HalfReifyOnConjunctionOf{v < 0_i}};
        }();
        auto pos_ge = model.add_labelled_constraint(owner, role_prefix + letter + "ge0_ge", WPBSum{} + 1_i * v + as_term(-1_i) >= 0_i, ge0);
        auto pos_le = model.add_labelled_constraint(owner, role_prefix + letter + "ge0_le", WPBSum{} + -1_i * v + as_term(1_i) >= 0_i, ge0);
        auto neg_ge = model.add_labelled_constraint(owner, role_prefix + letter + "lt0_ge", WPBSum{} + 1_i * v + as_term(1_i) >= 0_i, lt0);
        auto neg_le = model.add_labelled_constraint(owner, role_prefix + letter + "lt0_le", WPBSum{} + -1_i * v + as_term(-1_i) >= 0_i, lt0);
        return MagnitudeChannel{mag, pos_ge, pos_le, neg_ge, neg_le};
    }
}

auto gcs::innards::product_enc::emit_magnitude_channel(ProofModel & model, const State & initial_state, const ConstraintID & owner,
    IntegerVariableID v, long long axis, const string & letter, const LinkNaming & naming) -> MagnitudeChannel
{
    // Range [0, max(|lb|, |ub|)] so a signed operand's magnitude has enough
    // bits; for a non-negative operand this is just [0, ub], unchanged.
    auto mag_ub = max(abs(initial_state.lower_bound(v)), abs(initial_state.upper_bound(v)));
    auto mag = model.create_proof_only_integer_variable(0_i, mag_ub, "mult_mag_" + naming.role_prefix() + letter,
        IntegerVariableProofRepresentation::Bits, CakeBitNaming{owner, naming.bit_indices({axis}), "bin", std::nullopt, false, true});
    return emit_channel_rows(model, owner, v, mag, naming.role_prefix(), letter);
}

auto gcs::innards::product_enc::emit_magnitude_channel(ProofModel & model, const ConstraintID & owner, IntegerVariableID v,
    SimpleIntegerVariableID mag, Integer mag_bit_max, long long axis, const string & letter, const string & mag_name) -> MagnitudeChannel
{
    model.register_state_variable_bits_in_proof(mag, 0_i, mag_bit_max, mag_name, CakeBitNaming{owner, {axis}, "bin", std::nullopt, false, true});
    return emit_channel_rows(model, owner, v, mag, string{}, letter);
}

auto gcs::innards::product_enc::emit_bit_product_grid(ProofModel & model, const ConstraintID & owner,
    const SimpleOrProofOnlyIntegerVariableID & bits_a, const SimpleOrProofOnlyIntegerVariableID & bits_b, const LinkNaming & naming) -> BitProductGrid
{
    auto & tracker = model.names_and_ids_tracker();
    auto n1 = tracker.num_bits(bits_a);
    auto n2 = tracker.num_bits(bits_b);

    // Bit products x[id][i_j][prod] <=> bit_a_i AND bit_b_j, summed with
    // 2^(i+j). The two reifying halves carry deterministic labels
    // (create_proof_flag_fully_reifying): [r] = flag -> ineq ("forwards"),
    // [f] = ~flag -> ~ineq ("reverse"); justifications reference them by
    // those labels.
    BitProductGrid grid;
    for (Integer i = 0_i; i < n1; ++i) {
        grid.cells.emplace_back();
        for (Integer j = 0_i; j < n2; ++j) {
            auto flag = model.create_proof_flag_fully_reifying(owner, naming.bit_indices({i.raw_value, j.raw_value}), "prod",
                WPBSum{} + 1_i * ProofBitVariable{bits_a, i, true} + 1_i * ProofBitVariable{bits_b, j, true} >= 2_i);
            auto base = "x[" + as_string(owner) + "][" + naming.grid_cell_name(i, j) + "][prod]";
            grid.cells[i.as_index()].emplace_back(BitProductCell{flag, ProofLineLabel{base + "[r]"}, ProofLineLabel{base + "[f]"}});
            grid.sum += power2(i + j) * flag;
            grid.neg_sum += -power2(i + j) * flag;
        }
    }
    return grid;
}

auto gcs::innards::product_enc::emit_result_channel(
    ProofModel & model, const ConstraintID & owner, IntegerVariableID v3, const BitProductGrid & grid, const LinkNaming & naming) -> ResultChannel
{
    auto lp = naming.role_prefix();
    auto zge0 = HalfReifyOnConjunctionOf{v3 >= 0_i};
    auto zlt0 = HalfReifyOnConjunctionOf{v3 < 0_i};
    auto ge0_ge = model.add_labelled_constraint(owner, lp + "mag_Zge0_ge", grid.neg_sum + 1_i * v3 >= 0_i, zge0);
    auto ge0_le = model.add_labelled_constraint(owner, lp + "mag_Zge0_le", grid.sum + -1_i * v3 >= 0_i, zge0);
    auto lt0_ge = model.add_labelled_constraint(owner, lp + "mag_Zlt0_ge", grid.sum + 1_i * v3 >= 0_i, zlt0);
    auto lt0_le = model.add_labelled_constraint(owner, lp + "mag_Zlt0_le", grid.neg_sum + -1_i * v3 >= 0_i, zlt0);
    return ResultChannel{ge0_ge, ge0_le, lt0_ge, lt0_le};
}

auto gcs::innards::product_enc::emit_sign_clauses(ProofModel & model, const ConstraintID & owner, IntegerVariableID v1, IntegerVariableID v2,
    IntegerVariableID v3, const LinkNaming & naming) -> vector<ProofLine>
{
    auto lp = naming.role_prefix();
    vector<ProofLine> lines;
    lines.emplace_back(model.add_labelled_constraint(owner, lp + "sgn_x0", WPBSum{} + 1_i * (v1 != 0_i) + 1_i * (v3 >= 0_i) >= 1_i));
    lines.emplace_back(model.add_labelled_constraint(owner, lp + "sgn_y0", WPBSum{} + 1_i * (v2 != 0_i) + 1_i * (v3 >= 0_i) >= 1_i));
    lines.emplace_back(
        model.add_labelled_constraint(owner, lp + "sgn_pp", WPBSum{} + 1_i * (v1 < 1_i) + 1_i * (v2 < 1_i) + 1_i * (v3 >= 0_i) >= 1_i));
    lines.emplace_back(
        model.add_labelled_constraint(owner, lp + "sgn_nn", WPBSum{} + 1_i * (v1 >= 0_i) + 1_i * (v2 >= 0_i) + 1_i * (v3 >= 0_i) >= 1_i));
    lines.emplace_back(
        model.add_labelled_constraint(owner, lp + "sgn_np", WPBSum{} + 1_i * (v1 >= 0_i) + 1_i * (v2 < 1_i) + 1_i * (v3 < 0_i) >= 1_i));
    lines.emplace_back(
        model.add_labelled_constraint(owner, lp + "sgn_pn", WPBSum{} + 1_i * (v1 < 1_i) + 1_i * (v2 >= 0_i) + 1_i * (v3 < 0_i) >= 1_i));
    return lines;
}
