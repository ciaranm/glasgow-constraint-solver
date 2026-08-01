#include <gcs/exception.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/bits_encoding.hh>
#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/interval_set.hh>

#include <algorithm>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <map>
#include <set>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#endif

#include <util/overloaded.hh>

using namespace gcs;
using namespace gcs::innards;

using std::ios;
using std::ios_base;
using std::make_unique;
using std::map;
using std::nullopt;
using std::ofstream;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::variant;
using std::vector;
using std::ranges::sort;
using std::ranges::unique;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::print;
#endif

namespace
{
    // The string-append twin of ProofLineLabel's ostream operator (a leading
    // `@`, then the label), plus the trailing space the OPB sites all want.
    auto append_label_to(string & out, const ProofLineLabel & label) -> void
    {
        out += '@';
        out += label.label;
        out += ' ';
    }
}

struct ProofModel::Imp
{
    NamesAndIDsTracker & tracker;

    ProofLineNumber number_of_constraints{0};

    optional<IntegerVariableID> optional_minimise_variable;
    optional<vector<IntegerVariableID>> preserved_variables;
    unsigned long long proof_only_integer_variable_nr = 0;

    map<Integer, ProofModel::CakeConstantAtoms> cake_constant_atoms;

    string opb_file;
    // Text not yet written out. Until write_preamble() runs this holds
    // everything emitted so far (the variable set-up rows); afterwards each
    // emitting method sends it straight on to the file.
    string opb;
    ofstream opb_stream;
    bool streaming = false;

    bool always_use_full_encoding = false;
    bool finalised = false;

    explicit Imp(NamesAndIDsTracker & t) : tracker(t)
    {
    }
};

ProofModel::ProofModel(const ProofOptions & proof_options, NamesAndIDsTracker & t) : _imp(make_unique<Imp>(t))
{
    _imp->opb_file = proof_options.proof_file_names.opb_file;
    _imp->always_use_full_encoding = proof_options.always_use_full_encoding;
}

ProofModel::~ProofModel()
{
    if (! _imp->finalised && std::uncaught_exceptions() == 0) {
        print(stderr, "ProofModel destroyed without calling finalise()\n");
        std::abort();
    }
}

auto ProofModel::advance_constraint_counter() -> ProofLineNumber
{
    return ProofLineNumber{++_imp->number_of_constraints.number};
}

auto ProofModel::claim_labels(const vector<string> & labels) -> void
{
    // The set itself lives in the tracker, not here, because it has a second
    // reader: NamesAndIDsTracker::constraint_row_label answers "was a row
    // emitted under this (id, role), so may I cite it?", and its caller is a
    // presolver, which holds a ProofLogger and no ProofModel. Both objects are
    // constructed with the same tracker, so moving the set there is what puts it
    // in reach of both without handing anyone a ProofModel after the model is
    // closed. The claiming rule, and the reasons for it, are documented on
    // NamesAndIDsTracker::claim_constraint_row_labels.
    _imp->tracker.claim_constraint_row_labels(labels);
}

auto ProofModel::emit_constraint_label(const string & constraint_id, const string & role) -> ProofLineLabel
{
    // The leading @ is added when a ProofLineLabel is written to the stream.
    return ProofLineLabel{"c[" + constraint_id + "]" + (role.empty() ? "" : "[" + role + "]")};
}

auto ProofModel::begin_constraint_block_comment(const string & constraint_type, const ConstraintID & constraint_id) -> void
{
    _imp->opb += "* constraint ";
    _imp->opb += constraint_type;
    _imp->opb += ' ';
    _imp->opb += as_string(constraint_id);
    _imp->opb += '\n';
    write_out_pending();
}

auto ProofModel::add_constraint(const Literals & lits) -> void
{
    WPBSum sum;

    // A clause containing a statically-true literal is a tautology. It
    // constrains nothing, but we still emit it as a trivially-true `sum >= 0`
    // rather than omitting it, so the constraint counter stays in step.
    bool tautological = false;
    for (auto & lit : lits) {
        overloaded{
            [&](const TrueLiteral &) { tautological = true; },                              //
            [&](const FalseLiteral &) {},                                                   //
            [&]<typename T_>(const VariableConditionFrom<T_> & cond) { sum += 1_i * cond; } //
        }
            .visit(simplify_literal(names_and_ids_tracker(), lit));
    }

    // put these in some kind of order
    sort(sum.terms);

    // remove duplicates
    sum.terms.erase(unique(sum.terms).begin(), sum.terms.end());

    add_constraint(move(sum) >= (tautological ? 0_i : 1_i), nullopt);
}

auto ProofModel::add_constraint(const WPBSumLE & ineq, const optional<HalfReifyOnConjunctionOf> & half_reif) -> void
{
    names_and_ids_tracker().need_all_proof_names_in(ineq.lhs);
    if (half_reif)
        names_and_ids_tracker().need_all_proof_names_in(*half_reif);

    emit_inequality_to(names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(ineq, *half_reif) : ineq, _imp->opb, EnsureNames::No);
    _imp->opb += ";\n";
    write_out_pending();
    auto line = advance_constraint_counter();
    // emit_inequality_to negates the LE inequality to land in PB >= form.
    names_and_ids_tracker().derive_deviewed_form_for(line, ineq.lhs, /*le_half=*/true);
}

auto ProofModel::add_constraint(const WPBSumEq & eq, const optional<HalfReifyOnConjunctionOf> & half_reif) -> void
{
    names_and_ids_tracker().need_all_proof_names_in(eq.lhs);
    if (half_reif)
        names_and_ids_tracker().need_all_proof_names_in(*half_reif);

    emit_inequality_to(names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(eq.lhs <= eq.rhs, *half_reif) : eq.lhs <= eq.rhs, _imp->opb,
        EnsureNames::No);
    _imp->opb += ";\n";
    auto first = advance_constraint_counter();
    // LE half: emit_inequality_to negates coefficients on emit.
    names_and_ids_tracker().derive_deviewed_form_for(first, eq.lhs, /*le_half=*/true);

    emit_inequality_to(names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(eq.lhs >= eq.rhs, *half_reif) : eq.lhs >= eq.rhs, _imp->opb,
        EnsureNames::No);
    _imp->opb += ";\n";
    write_out_pending();
    auto second = advance_constraint_counter();
    // GE half: the >= operator in expression.hh negates the sum once before
    // emit_inequality_to negates it again, so OPB-form coefficients match
    // the input WPBSum.
    names_and_ids_tracker().derive_deviewed_form_for(second, eq.lhs, /*le_half=*/false);
}

auto ProofModel::add_labelled_constraint(const ConstraintID & constraint_id, const string & role_le, const string & role_ge, const WPBSumEq & eq,
    const optional<HalfReifyOnConjunctionOf> & half_reif) -> pair<ProofLine, ProofLine>
{
    auto id = as_string(constraint_id);
    auto label_le = emit_constraint_label(id, role_le).label;
    auto label_ge = emit_constraint_label(id, role_ge).label;
    // Both halves up front: a colliding pair must not leave its LE row behind.
    claim_labels({label_le, label_ge});
    return add_labelled_constraint(label_le, label_ge, eq, half_reif);
}

auto ProofModel::add_labelled_constraint(const string & label_le, const string & label_ge, const WPBSumEq & eq,
    const optional<HalfReifyOnConjunctionOf> & half_reif) -> pair<ProofLine, ProofLine>
{
    names_and_ids_tracker().need_all_proof_names_in(eq.lhs);
    if (half_reif)
        names_and_ids_tracker().need_all_proof_names_in(*half_reif);

    ProofLineLabel le{label_le};
    append_label_to(_imp->opb, le);
    emit_inequality_to(names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(eq.lhs <= eq.rhs, *half_reif) : eq.lhs <= eq.rhs, _imp->opb,
        EnsureNames::No);
    _imp->opb += ";\n";
    advance_constraint_counter();
    // LE half: emit_inequality_to negates coefficients on emit.
    names_and_ids_tracker().derive_deviewed_form_for(le, eq.lhs, /*le_half=*/true);

    ProofLineLabel ge{label_ge};
    append_label_to(_imp->opb, ge);
    emit_inequality_to(names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(eq.lhs >= eq.rhs, *half_reif) : eq.lhs >= eq.rhs, _imp->opb,
        EnsureNames::No);
    _imp->opb += ";\n";
    write_out_pending();
    advance_constraint_counter();
    // GE half: see the unlabelled add_constraint above for the double-negation note.
    names_and_ids_tracker().derive_deviewed_form_for(ge, eq.lhs, /*le_half=*/false);

    return pair{le, ge};
}

auto ProofModel::add_labelled_constraint(const string & label, const WPBSumLE & ineq, const optional<HalfReifyOnConjunctionOf> & half_reif)
    -> ProofLine
{
    names_and_ids_tracker().need_all_proof_names_in(ineq.lhs);
    if (half_reif)
        names_and_ids_tracker().need_all_proof_names_in(*half_reif);

    ProofLineLabel l{label};
    append_label_to(_imp->opb, l);
    emit_inequality_to(names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(ineq, *half_reif) : ineq, _imp->opb, EnsureNames::No);
    _imp->opb += ";\n";
    write_out_pending();
    advance_constraint_counter();
    // As the (constraint_id, role) overload: a labelled constraint over a view
    // still needs its deviewed form, so a proof-only view variable's encoding
    // definitions are referenced (by label) in deview-form. A no-op when the
    // inequality mentions no views. emit_inequality_to negates the LE half.
    names_and_ids_tracker().derive_deviewed_form_for(l, ineq.lhs, /*le_half=*/true);
    return l;
}

auto ProofModel::add_labelled_constraint(const string & label, const Literals & lits) -> ProofLine
{
    // The labelled counterpart of add_constraint(Literals): build the clause's
    // pseudo-Boolean sum (a statically-true literal collapses it to the
    // trivially-true `sum >= 0`) and emit it under @label.
    WPBSum sum;
    bool tautological = false;
    for (auto & lit : lits) {
        overloaded{
            [&](const TrueLiteral &) { tautological = true; },                              //
            [&](const FalseLiteral &) {},                                                   //
            [&]<typename T_>(const VariableConditionFrom<T_> & cond) { sum += 1_i * cond; } //
        }
            .visit(simplify_literal(names_and_ids_tracker(), lit));
    }
    sort(sum.terms);
    sum.terms.erase(unique(sum.terms).begin(), sum.terms.end());
    return add_labelled_constraint(label, move(sum) >= (tautological ? 0_i : 1_i), nullopt);
}

auto ProofModel::add_labelled_constraint(
    const ConstraintID & constraint_id, const string & role, const WPBSumLE & ineq, const optional<HalfReifyOnConjunctionOf> & half_reif) -> ProofLine
{
    auto label = emit_constraint_label(as_string(constraint_id), role).label;
    claim_labels({label});
    return add_labelled_constraint(label, ineq, half_reif);
}

auto ProofModel::add_two_way_reified_constraint(const WPBSumLE & ineq, const ProofFlag & flag) -> pair<ProofLine, ProofLine>
{
    // Emit both halves under labels derived from the flag's own name --- base[r]
    // is the forward half (flag -> ineq), base[f] the reverse (~flag -> ~ineq) ---
    // so callers reference the halves by @label, never by line number, and for a
    // cake-named flag (x[id][..] / v[id][..]) the labels match cake_pb_cp. Mirrors
    // the manual labelling in create_proof_flag_fully_reifying(ConstraintID, ...).
    // Use the flag's full PB rendering (e.g. f[3][sort_before] or x[id][i_j][bf]),
    // not name_of, whose plain-flag form is the bare stem and would collide across
    // flags sharing it.
    auto base = names_and_ids_tracker().pb_file_string_for(flag);
    auto forward = add_labelled_constraint(base + "[r]", ineq, HalfReifyOnConjunctionOf{{flag}});
    names_and_ids_tracker().derive_deviewed_form_for(forward, ineq.lhs, /*le_half=*/true);
    auto reverse_ineq = negate_inequality(ineq);
    auto reverse = add_labelled_constraint(base + "[f]", reverse_ineq, HalfReifyOnConjunctionOf{{! flag}});
    names_and_ids_tracker().derive_deviewed_form_for(reverse, reverse_ineq.lhs, /*le_half=*/true);
    return {forward, reverse};
}

auto ProofModel::create_proof_flag_fully_reifying(const string & flag_name, const WPBSumLE & ineq) -> ProofFlag
{
    auto flag = create_proof_flag(flag_name);
    add_two_way_reified_constraint(ineq, flag);
    return flag;
}

auto ProofModel::create_proof_flag_fully_reifying(
    const ConstraintID & id, const vector<long long> & indices, const optional<string> & annotation, const WPBSumLE & ineq) -> ProofFlag
{
    auto flag = names_and_ids_tracker().create_proof_flag(id, indices, annotation);
    // Derive the two half-labels from the flag's own name: x[..][r] is the forward
    // half (flag -> ineq), [f] the reverse (~flag -> ~ineq). The single-argument
    // add_labelled_constraint emits the @label verbatim.
    auto base = names_and_ids_tracker().name_of(flag);
    add_labelled_constraint(base + "[r]", ineq, HalfReifyOnConjunctionOf{{flag}});
    add_labelled_constraint(base + "[f]", negate_inequality(ineq), HalfReifyOnConjunctionOf{{! flag}});
    return flag;
}

auto ProofModel::create_proof_flag_values_fully_reifying(
    const ConstraintID & id, const vector<long long> & values, const optional<string> & annotation, const WPBSumLE & ineq) -> ProofFlag
{
    auto flag = names_and_ids_tracker().create_proof_flag_values(id, values, annotation);
    // As the index-list variant: v[..][r] is the forward half (flag -> ineq),
    // [f] the reverse (~flag -> ~ineq).
    auto base = names_and_ids_tracker().name_of(flag);
    add_labelled_constraint(base + "[r]", ineq, HalfReifyOnConjunctionOf{{flag}});
    add_labelled_constraint(base + "[f]", negate_inequality(ineq), HalfReifyOnConjunctionOf{{! flag}});
    return flag;
}

auto ProofModel::names_and_ids_tracker() -> NamesAndIDsTracker &
{
    return _imp->tracker;
}

auto ProofModel::names_and_ids_tracker() const -> const NamesAndIDsTracker &
{
    return _imp->tracker;
}

auto ProofModel::create_proof_only_integer_variable(Integer lower, Integer upper, const string & name, const IntegerVariableProofRepresentation rep,
    const optional<CakeBitNaming> & bit_naming) -> ProofOnlySimpleIntegerVariableID
{
    ProofOnlySimpleIntegerVariableID id{_imp->proof_only_integer_variable_nr++};
    if (bit_naming) {
        // cake names its position/rank/value auxiliaries as free bit-sums with no
        // bound constraints in the OPB; register the (cake-named) bits only, so the
        // variable's eq/ge atoms are introduced lazily in the proof when first used.
        register_bits_variable_encoding(id, lower, upper, name, bit_naming);
        return id;
    }
    switch (rep) {
    case IntegerVariableProofRepresentation::DirectOnly: set_up_direct_only_variable_encoding(id, lower, upper, name); break;
    case IntegerVariableProofRepresentation::Bits: set_up_bits_variable_encoding(id, lower, upper, name); break;
    }

    return id;
}

auto ProofModel::create_proof_only_integer_variable_in_proof(Integer lower, Integer upper, const string & name) -> ProofOnlySimpleIntegerVariableID
{
    // A bits-encoded proof-only variable whose encoding is NOT emitted to the OPB:
    // the bits are registered (named, referenceable) but the model asserts nothing
    // about them. The caller is responsible for introducing the variable's meaning
    // inside the proof (e.g. ProofLogger::introduce_bits_of for a linear form), so
    // that it is a conservative extension rather than a model axiom --- which is
    // what makes it chain-portable against cake_pb_cp's OPB. This mirrors the
    // direct-encoding create_literals_for_introduced_variable_value, in bits.
    ProofOnlySimpleIntegerVariableID id{_imp->proof_only_integer_variable_nr++};
    register_bits_variable_encoding(id, lower, upper, name);
    // No OPB rows means the [lo, hi] bounds are NOT a trivial consequence of
    // the model: a need_gevar boundary pin (a top-of-proof RUP line) would
    // have nothing to propagate from, and would be queued before the caller's
    // in-proof definition lines even exist. Nothing creates gevars over such
    // a variable today, so this is a trap-removal, not a behaviour change.
    names_and_ids_tracker().note_bounds_not_trivially_derivable(id);
    return id;
}

auto ProofModel::register_state_variable_bits_in_proof(
    const SimpleIntegerVariableID & id, Integer lower, Integer upper, const string & name, const optional<CakeBitNaming> & bit_naming) -> void
{
    // Like create_proof_only_integer_variable_in_proof, but for a variable that is
    // ALSO state-allocated (so it can drive propagation): register its bits, emit
    // nothing to the OPB, and leave the caller to introduce its meaning in-proof. A
    // CakeBitNaming names the bits in cake's value-flag scheme (modulus's quotient).
    register_bits_variable_encoding(id, lower, upper, name, bit_naming);
    // Under OrderEncodingDeletion::Literals this variable's ge order literals are named
    // at ProofLevel::Top by the divide/modulus product-justification caches, so they must
    // never be deleted on backtrack: keep the whole order encoding resident (defs at Top).
    names_and_ids_tracker().note_order_encoding_stays_resident(id);
}

auto ProofModel::set_up_direct_only_variable_encoding(SimpleOrProofOnlyIntegerVariableID id, Integer lower, Integer upper, const string & name)
    -> void
{
    names_and_ids_tracker().track_bounds(id, lower, upper);

    if (0_i == lower && 1_i == upper) {
        names_and_ids_tracker().track_variable_name(id, name);
        // Name the single PB variable as bit 0 (`i[name][b0]`), matching how
        // cake_pb_cp encodes a {0,1} variable. For a {0,1} variable the bit-0
        // literal *is* the (== 1)/(== 0) literal, so those eq associations below
        // alias it directly; only the name differs. We still emit just the one
        // (tautological) line -- cake additionally emits an upper-bound line, but
        // VeriPB no longer pins the constraint count, and references are relative.
        //
        // The (>= 1)/(< 1) ORDER atom is deliberately NOT aliased to the bit
        // here (issue #554). A weighted pol that substitutes a lower-bound atom
        // needs a genuine reified line (`b0 + 1 ~g1 >= 1`, g1 a fresh reif
        // literal), whose degree and gate term survive the combination; a bare
        // bit-literal axiom pushed in its place has no degree and cancels the
        // base constraint's own `~b0` term outright, silently weakening the
        // derived bound. So leave the >= 1 gevar unset and let need_gevar build
        // it lazily as the standard reified pair over the bit, exactly as for a
        // bits-encoded variable. (The two `red` lines are created in-proof on
        // first use, so the OPB is unchanged.)
        auto eqvar = names_and_ids_tracker().allocate_xliteral_meaning_bit_of(id, 0_i);
        _imp->opb += "1 ";
        _imp->opb += names_and_ids_tracker().pb_file_string_for(eqvar);
        _imp->opb += " >= 0 ;\n";
        write_out_pending();
        advance_constraint_counter();

        overloaded{
            [&](const SimpleIntegerVariableID & id) {
                names_and_ids_tracker().associate_condition_with_xliteral(id == 1_i, eqvar);
                names_and_ids_tracker().associate_condition_with_xliteral(id != 1_i, ! eqvar);
                names_and_ids_tracker().associate_condition_with_xliteral(id == 0_i, ! eqvar);
                names_and_ids_tracker().associate_condition_with_xliteral(id != 0_i, eqvar);
                // track_eqvar stores the (== v, != v) pol-item pair that
                // need_pol_item_defining_literal returns. For value 1 the eq atom
                // is eqvar and the disequality is !eqvar; for value 0 the polarity
                // is flipped (id == 0 is !eqvar, id != 0 is eqvar), so value 0 gets
                // the swapped pair -- otherwise need_pol_item_defining_literal(id ==
                // 0) / (id != 0) would return the opposite-polarity bit (issue #559).
                pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>> names_1{eqvar, ! eqvar};
                names_and_ids_tracker().track_eqvar(id, 1_i, names_1);
                pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>> names_0{! eqvar, eqvar};
                names_and_ids_tracker().track_eqvar(id, 0_i, names_0);
            }, //
            [](const ProofOnlySimpleIntegerVariableID &) {
                // currently there's no API for asking for literals for these
            } //
        }
            .visit(id);

        names_and_ids_tracker().track_bits(id, 0_i, {{1_i, eqvar}});
    }
    else {
        for (auto v = lower; v <= upper; ++v) {
            names_and_ids_tracker().track_variable_name(id, name);
            auto eqvar = names_and_ids_tracker().allocate_xliteral_meaning(id, EqualsOrGreaterEqual::Equals, v);
            _imp->opb += "1 ";
            _imp->opb += names_and_ids_tracker().pb_file_string_for(eqvar);
            _imp->opb += ' ';

            visit(
                [&](const auto & id) {
                    names_and_ids_tracker().associate_condition_with_xliteral(id == v, eqvar);
                    names_and_ids_tracker().associate_condition_with_xliteral(id != v, ! eqvar);
                },
                id);
        }
        _imp->opb += ">= 1 ;\n";
        names_and_ids_tracker().track_variable_takes_at_least_one_value(id, advance_constraint_counter());

        for (auto v = lower; v <= upper; ++v) {
            _imp->opb += "-1 ";
            _imp->opb += names_and_ids_tracker().pb_file_string_for(id == v);
            _imp->opb += ' ';
        }
        _imp->opb += ">= -1 ;\n";
        write_out_pending();
        advance_constraint_counter();
    }
}

auto ProofModel::set_up_integer_variable(SimpleIntegerVariableID id, Integer lower, Integer upper, const string & name,
    const optional<IntegerVariableProofRepresentation> & rep, const optional<CakeBitNaming> & bit_naming) -> void
{
    if (bit_naming) {
        // A State variable that cake encodes as a proof-only bit-sum (cake-named
        // bits, no OPB bounds); the bits path handles both.
        set_up_bits_variable_encoding(id, lower, upper, name, bit_naming);
        return;
    }
    if (! rep) {
        if (lower == 0_i && upper == 1_i)
            set_up_direct_only_variable_encoding(id, lower, upper, name);
        else
            set_up_bits_variable_encoding(id, lower, upper, name);
    }
    else {
        switch (*rep) {
        case IntegerVariableProofRepresentation::Bits: set_up_bits_variable_encoding(id, lower, upper, name); break;
        case IntegerVariableProofRepresentation::DirectOnly: set_up_direct_only_variable_encoding(id, lower, upper, name); break;
        }
    }
}

auto ProofModel::register_bits_variable_encoding(
    SimpleOrProofOnlyIntegerVariableID id, Integer lower, Integer upper, const string & name, const optional<CakeBitNaming> & bit_naming) -> void
{
    // The "register" half of a bits encoding: allocate and name the bit literals
    // and record the bounds, but emit nothing to the OPB. set_up_bits_variable_encoding
    // wraps this with the OPB bound constraints; create_proof_only_integer_variable_in_proof
    // uses it alone, for a variable whose encoding is introduced inside the proof
    // (e.g. via ProofLogger::introduce_bits_of) rather than asserted in the model.
    auto [highest_bit_shift, highest_bit_coeff, negative_bit_coeff] = get_bits_encoding_coeffs(lower, upper);
    // See CakeBitNaming: cake's arg_sort always signs its sorted-value variables, so
    // force a sign bit (at -2^(number of value bits)) even for a non-negative range.
    if (bit_naming && bit_naming->add_a_pointless_sign_bit_only_because_cake_argsort_wastefully_always_does && 0_i == negative_bit_coeff)
        negative_bit_coeff = -power2(highest_bit_shift + 1_i);
    vector<pair<Integer, XLiteral>> bits;
    auto & tracker = names_and_ids_tracker();
    tracker.track_variable_name(id, name);

    // cake's arg_sort sorted-value variables (the ones carrying this flag) are free
    // signed bit-sums with no OPB bound line; their [lo, hi] bounds are entailed only
    // through the conditional value/position channels, so they are not RUP-derivable
    // boundary literals. Tell need_gevar not to pin them -- ArgSort derives them once,
    // explicitly, at proof start instead.
    if (bit_naming && bit_naming->add_a_pointless_sign_bit_only_because_cake_argsort_wastefully_always_does)
        tracker.note_bounds_not_trivially_derivable(id);

    // With a CakeBitNaming, a bit is named v[id][values...][annotation] (as
    // create_proof_flag_values would); the value bits carry the bit number as the
    // final index and the sign bit does not. Without one, name_override is nullopt
    // and the tracker uses the default p[index_name][b] names.
    auto cake_bit_name = [&](const vector<long long> & values, const string & annotation) -> optional<string> {
        if (! bit_naming)
            return nullopt;
        // Default v[...] (Values family); cake's multiply-style magnitude bits are
        // the x[...] Indices family (see CakeBitNaming::use_indices_family).
        string s = (bit_naming->use_indices_family ? "x[" : "v[") + as_string(bit_naming->id) + "][";
        for (size_t k = 0; k < values.size(); ++k)
            s += (k != 0 ? "_" : "") + std::to_string(values[k]);
        return s + "][" + annotation + "]";
    };

    if (0_i != negative_bit_coeff) {
        if (bit_naming && ! bit_naming->sign_annotation)
            throw ProofError{"a signed cake-named proof-only variable needs a sign annotation to name its sign bit"};
        auto sign_name = bit_naming ? cake_bit_name(bit_naming->indices, *bit_naming->sign_annotation) : nullopt;
        bits.emplace_back(negative_bit_coeff, tracker.allocate_xliteral_meaning_negative_bit_of(id, negative_bit_coeff, sign_name));
    }
    for (Integer b = 0_i; b <= highest_bit_shift; ++b) {
        optional<string> value_name;
        if (bit_naming) {
            auto values = bit_naming->indices;
            values.push_back(b.raw_value);
            value_name = cake_bit_name(values, bit_naming->value_annotation);
        }
        bits.emplace_back(power2(b), tracker.allocate_xliteral_meaning_bit_of(id, Integer{b}, value_name));
    }

    tracker.track_bits(id, negative_bit_coeff, bits);
    tracker.track_bounds(id, lower, upper);
}

auto ProofModel::set_up_bits_variable_encoding(
    SimpleOrProofOnlyIntegerVariableID id, Integer lower, Integer upper, const string & name, const optional<CakeBitNaming> & bit_naming) -> void
{
    register_bits_variable_encoding(id, lower, upper, name, bit_naming);
    // A cake-named variable is a free bit-sum: cake emits no bound lines for it, so
    // stop here (as create_proof_only_integer_variable does), leaving the atoms to be
    // introduced lazily in the proof when first used.
    if (bit_naming)
        return;
    vector<pair<Integer, XLiteral>> bits;
    for (auto b : names_and_ids_tracker().each_bit(id))
        bits.push_back(b);

    // @i[name][lb]/[ub] labels match cake_pb_cp, for a real variable; a vector
    // name like box[0] is fine (veripb's @label parser accepts the nested
    // brackets). Proof-only variables are not in cake's OPB, so their bounds stay
    // unlabelled (nothing references them, and there is no cake label to match).
    bool labelled = std::holds_alternative<SimpleIntegerVariableID>(id);

    // lower bound
    if (labelled)
        append_label_to(_imp->opb, ProofLineLabel{"i[" + name + "][lb]"});
    for (auto & [coeff, var] : bits) {
        append_number_to(_imp->opb, coeff);
        _imp->opb += ' ';
        _imp->opb += names_and_ids_tracker().pb_file_string_for(var);
        _imp->opb += ' ';
    }
    _imp->opb += ">= ";
    append_number_to(_imp->opb, lower);
    _imp->opb += " ;\n";
    auto lower_row = advance_constraint_counter();

    // upper bound
    if (labelled)
        append_label_to(_imp->opb, ProofLineLabel{"i[" + name + "][ub]"});
    for (auto & [coeff, var] : bits) {
        append_number_to(_imp->opb, -coeff);
        _imp->opb += ' ';
        _imp->opb += names_and_ids_tracker().pb_file_string_for(var);
        _imp->opb += ' ';
    }
    _imp->opb += ">= ";
    append_number_to(_imp->opb, -upper);
    _imp->opb += " ;\n";
    write_out_pending();
    auto upper_row = advance_constraint_counter();

    // Track the two rows so proof steps can combine them by pol (e.g.
    // ProofLogger::introduce_bits_of deriving a linear form's own bound
    // lines): by label for a state variable, so the references stay
    // count-robust under cake_pb_cp's re-derived OPB, and by constraint
    // number for a proof-only variable, which never appears in a cake chain.
    if (labelled)
        names_and_ids_tracker().track_bound_rows(id, ProofLineLabel{"i[" + name + "][lb]"}, ProofLineLabel{"i[" + name + "][ub]"});
    else
        names_and_ids_tracker().track_bound_rows(id, lower_row, upper_row);

    if (_imp->always_use_full_encoding)
        overloaded{
            [&](const SimpleIntegerVariableID & id) {
                for (; lower <= upper; ++lower)
                    names_and_ids_tracker().need_direct_encoding_for(id, lower);
            },                                               //
            [&](const ProofOnlySimpleIntegerVariableID &) {} //
        }
            .visit(id);
}

auto ProofModel::create_proof_flag(const string & name) -> ProofFlag
{
    return names_and_ids_tracker().create_proof_flag(name);
}

auto ProofModel::create_proof_flag(const ConstraintID & id, const vector<long long> & indices, const optional<string> & annotation) -> ProofFlag
{
    return names_and_ids_tracker().create_proof_flag(id, indices, annotation);
}

auto ProofModel::create_proof_flag(const ConstraintID & id, const string & annotation) -> ProofFlag
{
    return names_and_ids_tracker().create_proof_flag(id, annotation);
}

auto ProofModel::create_proof_flag_values(const ConstraintID & id, const vector<long long> & values, const optional<string> & annotation) -> ProofFlag
{
    return names_and_ids_tracker().create_proof_flag_values(id, values, annotation);
}

auto ProofModel::cake_constant_atoms(Integer k) -> CakeConstantAtoms
{
    if (auto it = _imp->cake_constant_atoms.find(k); it != _imp->cake_constant_atoms.end())
        return it->second;

    auto base = "n[" + std::to_string(k.raw_value) + "]";
    auto ge0 = names_and_ids_tracker().create_proof_flag_for_constant(k, "ge0");
    auto ge1 = names_and_ids_tracker().create_proof_flag_for_constant(k, "ge1");
    auto eq0 = names_and_ids_tracker().create_proof_flag_for_constant(k, "eq0");

    // A ge atom's [f] half pins a true atom and is vacuous for a false one; the
    // [r] half is the mirror image. cake writes each vacuous half with a zero
    // coefficient; a unit coefficient over a degree-0 row is the same vacuous
    // truth without leaning on zero-coefficient parsing.
    auto pin = [&](const string & atom_base, const ProofFlag & atom, bool truth) {
        add_labelled_constraint(atom_base + "[f]", WPBSum{} + 1_i * atom >= (truth ? 1_i : 0_i));
        add_labelled_constraint(atom_base + "[r]", WPBSum{} + 1_i * ! atom >= (truth ? 0_i : 1_i));
    };
    pin(base + "[ge0]", ge0, k >= 0_i);
    pin(base + "[ge1]", ge1, k >= 1_i);
    add_labelled_constraint(base + "[eq0][f]", WPBSum{} + 1_i * eq0 + -1_i * ge0 + -1_i * ! ge1 >= -1_i);
    add_labelled_constraint(base + "[eq0][r]", WPBSum{} + 2_i * ! eq0 + 1_i * ge0 + 1_i * ! ge1 >= 2_i);

    auto result = CakeConstantAtoms{ge0, ge1, eq0};
    _imp->cake_constant_atoms.emplace(k, result);
    return result;
}

auto ProofModel::write_out_pending() -> void
{
    if (! _imp->streaming)
        return;
    try {
        _imp->opb_stream << _imp->opb;
    }
    catch (const ios_base::failure &) {
        throw ProofError{"Error writing opb file to '" + _imp->opb_file + "'"};
    }
    _imp->opb.clear();
}

auto ProofModel::write_preamble() -> void
{
    if (_imp->streaming)
        throw UnexpectedException{"proof model preamble has already been written"};

    // A view objective is rendered over its own proof-only bit vector, so
    // register it now (this appends BinEnc(V)'s set-up rows to the pending
    // text, where they land just after the variable rows). This also
    // guarantees find_view succeeds for the objective later, e.g. in the
    // solution-logging soli path. There are two exceptions, both of which stay
    // unregistered so that min: falls back to deviewing through the underlying:
    //
    //  - a view whose bit vector cannot be represented at all -- negating a
    //    FlatZinc unbounded-int objective spans one more bit than an Integer
    //    holds;
    //
    //  - a plain negation, which is what Problem::maximise() stores. Its bit
    //    vector would be an extra proof-only variable that cake_pb_cp cannot
    //    know about: cake re-derives a `(maximize V)` .scp as `min: -1 i[V][b0]
    //    ...` straight over V's own bits, so an objective hosted on its own
    //    vector leaves the solver's proof citing view-linking labels that
    //    cake's OPB has no counterpart for, and the workflow-2 chain cannot
    //    check a maximisation at all. Deviewing writes exactly cake's line.
    //    Only the offset-free case is done this way: `then_add` shifts the
    //    objective by a constant that the deviewed min: cannot carry, and the
    //    .scp cannot express either (it renders as a bare `(maximize V)`).
    if (_imp->optional_minimise_variable)
        if (auto * view = std::get_if<ViewOfIntegerVariableID>(&*_imp->optional_minimise_variable)) {
            auto [v_lo, v_hi] = names_and_ids_tracker().view_bounds(*view);
            if (bits_encoding_fits(v_lo, v_hi) && ! (view->negate_first && view->then_add == 0_i))
                static_cast<void>(names_and_ids_tracker().need_view(*view));
        }

    try {
        _imp->opb_stream.exceptions(ios::failbit | ios::badbit);
        _imp->opb_stream.open(_imp->opb_file, ios::out);
        // No `* #variable= .. #constraint= ..` counts comment: VeriPB 3 does
        // not need it, and not writing it is what lets everything stream out
        // as it is produced instead of being buffered until the counts are
        // known.

        if (_imp->optional_minimise_variable) {
            _imp->opb_stream << "min: ";
            overloaded{
                [&](const SimpleIntegerVariableID & v) {
                    for (const auto & [bit_value, bit_name] : names_and_ids_tracker().each_bit(v))
                        _imp->opb_stream << bit_value << " " << names_and_ids_tracker().pb_file_string_for(bit_name) << " ";
                },                                                                          //
                [&](const ConstantIntegerVariableID &) { throw UnimplementedException{}; }, //
                [&](const ViewOfIntegerVariableID & v) {
                    // Registered just above whenever its bit vector is
                    // representable; otherwise fall back to deviewing through
                    // the underlying (the objective's constant offset doesn't
                    // matter for optimisation order).
                    if (auto v_id = names_and_ids_tracker().find_view(v)) {
                        for (const auto & [bit_value, bit_name] : names_and_ids_tracker().each_bit(*v_id))
                            _imp->opb_stream << bit_value << " " << names_and_ids_tracker().pb_file_string_for(bit_name) << " ";
                    }
                    else {
                        for (const auto & [bit_value, bit_name] : names_and_ids_tracker().each_bit(v.actual_variable))
                            _imp->opb_stream << (v.negate_first ? -bit_value : bit_value) << " "
                                             << names_and_ids_tracker().pb_file_string_for(bit_name) << " ";
                    }
                } //
            }
                .visit(*_imp->optional_minimise_variable);

            _imp->opb_stream << ";\n";
        }

        if (_imp->preserved_variables) {
            // The projection set for solx/soli only includes the
            // underlying's bits. View bits (allocated by need_view) are
            // deliberately omitted; VeriPB UP-extends them from the
            // underlying via the bit-vector link emitted in need_view by
            // Theorem 2.8 (equality of two binary sums propagates from one
            // side fixed to the other). Dedup so that X and a view of X (or
            // two views of the same X) in the preserve list don't emit X's
            // bits twice.
            _imp->opb_stream << "preserved: ";
            std::set<SimpleIntegerVariableID> already_emitted;
            auto emit_underlying = [&](const SimpleIntegerVariableID & v) {
                if (already_emitted.insert(v).second)
                    for (const auto & [bit_value, bit_name] : names_and_ids_tracker().each_bit(v))
                        _imp->opb_stream << names_and_ids_tracker().pb_file_string_for(bit_name) << " ";
            };
            for (const auto & var : *_imp->preserved_variables) {
                overloaded{
                    [&](const SimpleIntegerVariableID & v) { emit_underlying(v); },                //
                    [&](const ConstantIntegerVariableID &) {},                                     //
                    [&](const ViewOfIntegerVariableID & v) { emit_underlying(v.actual_variable); } //
                }
                    .visit(var);
            }

            _imp->opb_stream << ";\n";
        }
    }
    catch (const ios_base::failure &) {
        throw ProofError{"Error writing opb file to '" + _imp->opb_file + "'"};
    }

    _imp->streaming = true;
    write_out_pending();
}

auto ProofModel::finalise() -> void
{
    _imp->finalised = true;
    // Anything built without going through write_preamble (tests that drive a
    // ProofModel directly) has everything still pending; writing the preamble
    // now flushes it too, giving the old write-everything-at-the-end
    // behaviour.
    if (! _imp->streaming)
        write_preamble();
    else
        write_out_pending();
    try {
        _imp->opb_stream << std::flush;
        _imp->opb_stream.close();
    }
    catch (const ios_base::failure &) {
        throw ProofError{"Error writing opb file to '" + _imp->opb_file + "'"};
    }
}

auto ProofModel::number_of_constraints() const -> ProofLineNumber
{
    return _imp->number_of_constraints;
}

auto ProofModel::minimise(const IntegerVariableID & var) -> void
{
    if (_imp->streaming)
        throw UnexpectedException{"objective must be set before the OPB preamble is written"};
    _imp->optional_minimise_variable = var;

    // Exempt the objective from order-encoding deletion (dev_docs/brancher-design.md,
    // payload 3). Branch-and-bound re-tightens it at every improving solution and every
    // backtrack relaxes it again, so under Literals its thresholds are deleted and
    // re-introduced forever -- on seat-moving 2018 that is essentially all of the residual
    // churn at the default gate, verify-neutrally and for zero shrinkage. The chain gate
    // cannot suppress it, because the objective's chain is long for a churn reason rather
    // than a win reason and the gate only measures length.
    //
    // Here rather than in solve_with because this is where the objective is declared to the
    // proof machinery, so every path that sets one gets the exemption. A view objective is
    // exempted through its underlying, which is the variable whose `ge` definitions the
    // deletion machinery tracks (and which is already resident as a view underlying anyway).
    overloaded{
        [&](const SimpleIntegerVariableID & v) { names_and_ids_tracker().note_deletion_exempt(v); },                 //
        [&](const ViewOfIntegerVariableID & v) { names_and_ids_tracker().note_deletion_exempt(v.actual_variable); }, //
        [&](const ConstantIntegerVariableID &) {}                                                                    //
    }
        .visit(var);
}

auto ProofModel::preserve(vector<IntegerVariableID> vars) -> void
{
    if (_imp->streaming)
        throw UnexpectedException{"preserved variables must be set before the OPB preamble is written"};
    _imp->preserved_variables = move(vars);
}
