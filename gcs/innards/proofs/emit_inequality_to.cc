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
}

auto gcs::innards::emit_inequality_to(
    NamesAndIDsTracker & names_and_ids_tracker, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, string & out) -> void
{
    // build up the inequality, adjusting as we go for constant terms,
    // and converting from <= to >=.
    Integer rhs = -ineq.rhs;
    for (auto & [w, v] : ineq.lhs.terms) {
        if (0_i == w)
            continue;

        overloaded{
            [&, w = w](const ProofLiteral & lit) {
                overloaded{
                    [&](const TrueLiteral &) { rhs += w; }, //
                    [&](const FalseLiteral &) {},           //
                    [&]<typename T_>(
                        const VariableConditionFrom<T_> & cond) { append_term_to(out, -w, names_and_ids_tracker.pb_file_string_for(cond)); } //
                }
                    .visit(simplify_literal(names_and_ids_tracker, lit));
            },                                                                                                               //
            [&, w = w](const ProofFlag & flag) { append_term_to(out, -w, names_and_ids_tracker.pb_file_string_for(flag)); }, //
            [&, w = w](const IntegerVariableID & var) {
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
            [&, w = w](const ProofOnlySimpleIntegerVariableID & var) {
                for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(var))
                    append_term_to(out, -w * bit_value, names_and_ids_tracker.pb_file_string_for(bit_lit));
            }, //
            [&, w = w](const ProofBitVariable & bit) {
                auto [_, bit_name] = names_and_ids_tracker.get_bit(bit);
                append_term_to(out, -w, names_and_ids_tracker.pb_file_string_for(bit_name));
            }, //
        }
            .visit(v);
    }

    out += ">= ";
    append_number_to(out, rhs);
}

auto gcs::innards::emit_inequality_to(
    NamesAndIDsTracker & names_and_ids_tracker, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ostream & stream) -> void
{
    string out;
    emit_inequality_to(names_and_ids_tracker, ineq, out);
    stream << out;
}
