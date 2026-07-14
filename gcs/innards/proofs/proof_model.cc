#include <gcs/innards/interval_set.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/bits_encoding.hh>
#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/simplify_literal.hh>

#include <algorithm>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <iterator>
#include <map>
#include <set>
#include <sstream>

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

using std::fstream;
using std::ios;
using std::ios_base;
using std::istreambuf_iterator;
using std::make_unique;
using std::map;
using std::nullopt;
using std::ofstream;
using std::optional;
using std::ostreambuf_iterator;
using std::pair;
using std::string;
using std::stringstream;
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

struct ProofModel::Imp
{
    NamesAndIDsTracker & tracker;

    unsigned long long model_variables = 0;
    ProofLineNumber number_of_constraints{0};

    optional<IntegerVariableID> optional_minimise_variable;
    optional<vector<IntegerVariableID>> preserved_variables;
    unsigned long long proof_only_integer_variable_nr = 0;

    map<Integer, ProofModel::CakeConstantAtoms> cake_constant_atoms;

    string opb_file;
    stringstream opb;

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
    auto line = ProofLineNumber{++_imp->number_of_constraints.number};
    // Attribute this OPB row to the constraint whose block is being written, so
    // it becomes a member of that constraint's @@c[...] group (no-op unless
    // constraint-group RUP hints are on).
    names_and_ids_tracker().note_constraint_line(line);
    return line;
}

auto ProofModel::emit_constraint_label(const string & constraint_id, const string & role) -> ProofLineLabel
{
    // The leading @ is added when a ProofLineLabel is written to the stream.
    return ProofLineLabel{"c[" + constraint_id + "]" + (role.empty() ? "" : "[" + role + "]")};
}

auto ProofModel::begin_constraint_block_comment(const string & constraint_type, const ConstraintID & constraint_id) -> void
{
    _imp->opb << "* constraint " << constraint_type << ' ' << as_string(constraint_id) << '\n';
    names_and_ids_tracker().begin_constraint_block(constraint_id);
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

    emit_inequality_to(names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(ineq, *half_reif) : ineq, _imp->opb);
    _imp->opb << ";\n";
    auto line = advance_constraint_counter();
    // emit_inequality_to negates the LE inequality to land in PB >= form.
    names_and_ids_tracker().derive_deviewed_form_for(line, ineq.lhs, /*le_half=*/true);
}

auto ProofModel::add_constraint(const WPBSumEq & eq, const optional<HalfReifyOnConjunctionOf> & half_reif) -> void
{
    names_and_ids_tracker().need_all_proof_names_in(eq.lhs);
    if (half_reif)
        names_and_ids_tracker().need_all_proof_names_in(*half_reif);

    emit_inequality_to(
        names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(eq.lhs <= eq.rhs, *half_reif) : eq.lhs <= eq.rhs, _imp->opb);
    _imp->opb << ";\n";
    auto first = advance_constraint_counter();
    // LE half: emit_inequality_to negates coefficients on emit.
    names_and_ids_tracker().derive_deviewed_form_for(first, eq.lhs, /*le_half=*/true);

    emit_inequality_to(
        names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(eq.lhs >= eq.rhs, *half_reif) : eq.lhs >= eq.rhs, _imp->opb);
    _imp->opb << ";\n";
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
    return add_labelled_constraint(emit_constraint_label(id, role_le).label, emit_constraint_label(id, role_ge).label, eq, half_reif);
}

auto ProofModel::add_labelled_constraint(const string & label_le, const string & label_ge, const WPBSumEq & eq,
    const optional<HalfReifyOnConjunctionOf> & half_reif) -> pair<ProofLine, ProofLine>
{
    names_and_ids_tracker().need_all_proof_names_in(eq.lhs);
    if (half_reif)
        names_and_ids_tracker().need_all_proof_names_in(*half_reif);

    ProofLineLabel le{label_le};
    _imp->opb << le << " ";
    emit_inequality_to(
        names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(eq.lhs <= eq.rhs, *half_reif) : eq.lhs <= eq.rhs, _imp->opb);
    _imp->opb << ";\n";
    advance_constraint_counter();
    // LE half: emit_inequality_to negates coefficients on emit.
    names_and_ids_tracker().derive_deviewed_form_for(le, eq.lhs, /*le_half=*/true);

    ProofLineLabel ge{label_ge};
    _imp->opb << ge << " ";
    emit_inequality_to(
        names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(eq.lhs >= eq.rhs, *half_reif) : eq.lhs >= eq.rhs, _imp->opb);
    _imp->opb << ";\n";
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
    _imp->opb << l << " ";
    emit_inequality_to(names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(ineq, *half_reif) : ineq, _imp->opb);
    _imp->opb << ";\n";
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
    return add_labelled_constraint(emit_constraint_label(as_string(constraint_id), role).label, ineq, half_reif);
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
}

auto ProofModel::set_up_direct_only_variable_encoding(SimpleOrProofOnlyIntegerVariableID id, Integer lower, Integer upper, const string & name)
    -> void
{
    names_and_ids_tracker().track_bounds(id, lower, upper);

    if (0_i == lower && 1_i == upper) {
        names_and_ids_tracker().track_variable_name(id, name);
        // Name the single PB variable as bit 0 (`i[name][b0]`), matching how
        // cake_pb_cp encodes a {0,1} variable. For a {0,1} variable the bit-0
        // literal *is* the (== 1)/(>= 1) literal, so the condition associations
        // below are unchanged; only the name differs. We still emit just the one
        // (tautological) line -- cake additionally emits an upper-bound line, but
        // VeriPB no longer pins the constraint count, and references are relative.
        auto eqvar = names_and_ids_tracker().allocate_xliteral_meaning_bit_of(id, 0_i);
        _imp->opb << "1 " << names_and_ids_tracker().pb_file_string_for(eqvar) << " >= 0 ;\n";
        ++_imp->model_variables;
        advance_constraint_counter();

        overloaded{
            [&](const SimpleIntegerVariableID & id) {
                names_and_ids_tracker().associate_condition_with_xliteral(id == 1_i, eqvar);
                names_and_ids_tracker().associate_condition_with_xliteral(id != 1_i, ! eqvar);
                names_and_ids_tracker().associate_condition_with_xliteral(id == 0_i, ! eqvar);
                names_and_ids_tracker().associate_condition_with_xliteral(id != 0_i, eqvar);
                pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>> names{eqvar, ! eqvar};
                names_and_ids_tracker().track_eqvar(id, 1_i, names);
                names_and_ids_tracker().track_eqvar(id, 0_i, names);
            }, //
            [](const ProofOnlySimpleIntegerVariableID &) {
                // currently there's no API for asking for literals for these
            } //
        }
            .visit(id);

        names_and_ids_tracker().track_bits(id, 0_i, {{1_i, eqvar}});

        overloaded{
            [&](const SimpleIntegerVariableID & id) {
                names_and_ids_tracker().associate_condition_with_xliteral(id >= 1_i, eqvar);
                names_and_ids_tracker().associate_condition_with_xliteral(id < 1_i, ! eqvar);
                pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>> names{eqvar, ! eqvar};
                names_and_ids_tracker().track_gevar(id, 1_i, names);
            }, //
            [](const ProofOnlySimpleIntegerVariableID &) {
                // currently there's no API for asking for literals for these
            } //
        }
            .visit(id);
    }
    else {
        for (auto v = lower; v <= upper; ++v) {
            names_and_ids_tracker().track_variable_name(id, name);
            auto eqvar = names_and_ids_tracker().allocate_xliteral_meaning(id, EqualsOrGreaterEqual::Equals, v);
            _imp->opb << "1 " << names_and_ids_tracker().pb_file_string_for(eqvar) << " ";
            ++_imp->model_variables;

            visit(
                [&](const auto & id) {
                    names_and_ids_tracker().associate_condition_with_xliteral(id == v, eqvar);
                    names_and_ids_tracker().associate_condition_with_xliteral(id != v, ! eqvar);
                },
                id);
        }
        _imp->opb << ">= 1 ;\n";
        names_and_ids_tracker().track_variable_takes_at_least_one_value(id, advance_constraint_counter());

        for (auto v = lower; v <= upper; ++v) {
            _imp->opb << "-1 " << names_and_ids_tracker().pb_file_string_for(id == v) << " ";
        }
        _imp->opb << ">= -1 ;\n";
        // The at-most-one row is part of this variable's encoding closure.
        names_and_ids_tracker().note_rup_hint_line_for(id, advance_constraint_counter());
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
    _imp->model_variables += bits.size();

    // @i[name][lb]/[ub] labels match cake_pb_cp, for a real variable; a vector
    // name like box[0] is fine (veripb's @label parser accepts the nested
    // brackets). Proof-only variables are not in cake's OPB, so their bounds stay
    // unlabelled (nothing references them, and there is no cake label to match).
    bool labelled = std::holds_alternative<SimpleIntegerVariableID>(id);

    // lower bound
    if (labelled)
        _imp->opb << ProofLineLabel{"i[" + name + "][lb]"} << " ";
    for (auto & [coeff, var] : bits)
        _imp->opb << coeff << " " << names_and_ids_tracker().pb_file_string_for(var) << " ";
    _imp->opb << ">= " << lower << " ;\n";
    // The bit-vector lower/upper bound rows are part of this variable's encoding
    // closure (they relate its bits to its numeric bounds).
    names_and_ids_tracker().note_rup_hint_line_for(id, advance_constraint_counter());

    // upper bound
    if (labelled)
        _imp->opb << ProofLineLabel{"i[" + name + "][ub]"} << " ";
    for (auto & [coeff, var] : bits)
        _imp->opb << -coeff << " " << names_and_ids_tracker().pb_file_string_for(var) << " ";
    _imp->opb << ">= " << -upper << " ;\n";
    names_and_ids_tracker().note_rup_hint_line_for(id, advance_constraint_counter());

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

auto ProofModel::finalise() -> void
{
    _imp->finalised = true;
    try {
        ofstream full_opb;
        full_opb.exceptions(ios::failbit | ios::badbit);
        full_opb.open(_imp->opb_file);
        full_opb << "* #variable= " << _imp->model_variables << " #constraint= " << _imp->number_of_constraints.number << '\n';

        if (_imp->optional_minimise_variable) {
            full_opb << "min: ";
            overloaded{
                [&](const SimpleIntegerVariableID & v) {
                    for (const auto & [bit_value, bit_name] : names_and_ids_tracker().each_bit(v))
                        full_opb << bit_value << " " << names_and_ids_tracker().pb_file_string_for(bit_name) << " ";
                },                                                                          //
                [&](const ConstantIntegerVariableID &) { throw UnimplementedException{}; }, //
                [&](const ViewOfIntegerVariableID & v) {
                    // If the view's been registered (used in a constraint
                    // body during model writing), emit V's own bits.
                    // Otherwise fall back to deviewing through the underlying
                    // (objective constant offset still doesn't matter for
                    // optimisation order).
                    if (auto v_id = names_and_ids_tracker().find_view(v)) {
                        for (const auto & [bit_value, bit_name] : names_and_ids_tracker().each_bit(*v_id))
                            full_opb << bit_value << " " << names_and_ids_tracker().pb_file_string_for(bit_name) << " ";
                    }
                    else {
                        for (const auto & [bit_value, bit_name] : names_and_ids_tracker().each_bit(v.actual_variable))
                            full_opb << (v.negate_first ? -bit_value : bit_value) << " " << names_and_ids_tracker().pb_file_string_for(bit_name)
                                     << " ";
                    }
                } //
            }
                .visit(*_imp->optional_minimise_variable);

            full_opb << ";\n";
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
            full_opb << "preserved: ";
            std::set<SimpleIntegerVariableID> already_emitted;
            auto emit_underlying = [&](const SimpleIntegerVariableID & v) {
                if (already_emitted.insert(v).second)
                    for (const auto & [bit_value, bit_name] : names_and_ids_tracker().each_bit(v))
                        full_opb << names_and_ids_tracker().pb_file_string_for(bit_name) << " ";
            };
            for (const auto & var : *_imp->preserved_variables) {
                overloaded{
                    [&](const SimpleIntegerVariableID & v) { emit_underlying(v); },                //
                    [&](const ConstantIntegerVariableID &) {},                                     //
                    [&](const ViewOfIntegerVariableID & v) { emit_underlying(v.actual_variable); } //
                }
                    .visit(var);
            }

            full_opb << ";\n";
        }

        copy(istreambuf_iterator<char>{_imp->opb}, istreambuf_iterator<char>{}, ostreambuf_iterator<char>{full_opb});
        _imp->opb = stringstream{};
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
    _imp->optional_minimise_variable = var;
}

auto ProofModel::preserve(vector<IntegerVariableID> vars) -> void
{
    _imp->preserved_variables = move(vars);
}
