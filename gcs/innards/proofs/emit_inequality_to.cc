#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/simplify_literal.hh>

#include <util/overloaded.hh>

#include <ostream>

using std::ostream;
using std::string;

using namespace gcs;
using namespace gcs::innards;

namespace
{
    auto append_term_to(string & out, Integer w, const string & name) -> void
    {
        append_number_to(out, w);
        out += ' ';
        out += name;
        out += ' ';
    }

    // Render one weighted term of a PB inequality being emitted in >= form:
    // append its literal rendering(s) to `out` with negated weight, or fold a
    // constant term into `rhs`. Shared by the plain and reified renderers so
    // there is exactly one spelling of every term.
    auto append_or_fold_term_to(NamesAndIDsTracker & names_and_ids_tracker, Integer w, const PseudoBooleanTerm & v, string & out, Integer & rhs,
        EnsureNames ensure_names) -> void
    {
        overloaded{
            [&](const ProofLiteral & lit) {
                overloaded{
                    [&](const TrueLiteral &) { rhs += w; }, //
                    [&](const FalseLiteral &) {},           //
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) {
                        append_term_to(out, -w,
                            EnsureNames::Yes == ensure_names ? names_and_ids_tracker.pb_file_string_for_ensuring(cond)
                                                             : names_and_ids_tracker.pb_file_string_for(cond));
                    } //
                }
                    .visit(simplify_literal(names_and_ids_tracker, lit));
            },                                                                                                        //
            [&](const ProofFlag & flag) { append_term_to(out, -w, names_and_ids_tracker.pb_file_string_for(flag)); }, //
            [&](const IntegerVariableID & var) {
                overloaded{
                    [&](const SimpleIntegerVariableID & var) {
                        for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(var))
                            append_term_to(out, -w * bit_value, names_and_ids_tracker.pb_file_string_for(bit_lit));
                    },
                    [&](const ViewOfIntegerVariableID & view) {
                        // Emit V's own bits when the view is registered (the
                        // typical case — views in constraint bodies are
                        // registered during model writing via
                        // need_all_proof_names_in). Falls back to deviewing
                        // through the underlying for views first seen during
                        // proof logging, which the registry doesn't support.
                        if (auto v_id = names_and_ids_tracker.find_view(view)) {
                            for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(*v_id))
                                append_term_to(out, -w * bit_value, names_and_ids_tracker.pb_file_string_for(bit_lit));
                        }
                        else if (! view.negate_first) {
                            for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(view.actual_variable))
                                append_term_to(out, -w * bit_value, names_and_ids_tracker.pb_file_string_for(bit_lit));
                            rhs += w * view.then_add;
                        }
                        else {
                            for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(view.actual_variable))
                                append_term_to(out, w * bit_value, names_and_ids_tracker.pb_file_string_for(bit_lit));
                            rhs += w * view.then_add;
                        }
                    },
                    [&](const ConstantIntegerVariableID & cvar) { rhs += w * cvar.const_value; } //
                }
                    .visit(var);
            }, //
            [&](const ProofOnlySimpleIntegerVariableID & var) {
                for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(var))
                    append_term_to(out, -w * bit_value, names_and_ids_tracker.pb_file_string_for(bit_lit));
            }, //
            [&](const ProofBitVariable & bit) {
                auto [_, bit_name] = names_and_ids_tracker.get_bit(bit);
                append_term_to(out, -w, names_and_ids_tracker.pb_file_string_for(bit_name));
            }, //
        }
            .visit(v);
    }
}

auto gcs::innards::emit_inequality_to(NamesAndIDsTracker & names_and_ids_tracker, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq,
    string & out, EnsureNames ensure_names) -> void
{
    // build up the inequality, adjusting as we go for constant terms,
    // and converting from <= to >=.
    Integer rhs = -ineq.rhs;
    for (auto & [w, v] : ineq.lhs.terms) {
        if (0_i == w)
            continue;
        append_or_fold_term_to(names_and_ids_tracker, w, v, out, rhs, ensure_names);
    }

    out += ">= ";
    append_number_to(out, rhs);
}

auto gcs::innards::emit_reified_inequality_to(NamesAndIDsTracker & names_and_ids_tracker, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq,
    const HalfReifyOnConjunctionOf & half_reif, string & out, EnsureNames ensure_names) -> void
{
    // Renders exactly what emit_inequality_to would produce for
    // reify(ineq, half_reif), without materialising the reified sum: the
    // base terms, then each negated reifying term with the reification
    // coefficient, converted from <= to >= as usual.
    auto shape = names_and_ids_tracker.reification_shape(ineq, half_reif);

    Integer rhs = -shape.effective_rhs;
    for (auto & [w, v] : ineq.lhs.terms) {
        if (0_i == w)
            continue;
        append_or_fold_term_to(names_and_ids_tracker, w, v, out, rhs, ensure_names);
    }

    for (auto & r : half_reif)
        overloaded{
            [&](const ProofFlag & f) { append_or_fold_term_to(names_and_ids_tracker, shape.reif_coefficient, ! f, out, rhs, ensure_names); }, //
            [&](const ProofLiteral & lit) {
                append_or_fold_term_to(names_and_ids_tracker, shape.reif_coefficient, ! lit, out, rhs, ensure_names);
            }, //
            [&](const ProofBitVariable & bit) {
                append_or_fold_term_to(names_and_ids_tracker, shape.reif_coefficient, ! bit, out, rhs, ensure_names);
            } //
        }
            .visit(r);

    out += ">= ";
    append_number_to(out, rhs);
}

auto gcs::innards::emit_inequality_to(
    NamesAndIDsTracker & names_and_ids_tracker, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ostream & stream) -> void
{
    string out;
    emit_inequality_to(names_and_ids_tracker, ineq, out, EnsureNames::No);
    stream << out;
}
