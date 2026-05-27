#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/simplify_literal.hh>

#include <util/overloaded.hh>

using std::ostream;
using std::string;

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::emit_inequality_to(
    NamesAndIDsTracker & names_and_ids_tracker,
    const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq,
    ostream & stream) -> void
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
                    [&](const TrueLiteral &) {
                        rhs += w;
                    },
                    [&](const FalseLiteral &) {},
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) {
                        stream << -w << " " << names_and_ids_tracker.pb_file_string_for(cond) << " ";
                    }}
                    .visit(simplify_literal(names_and_ids_tracker, lit));
            },
            [&, w = w](const ProofFlag & flag) {
                stream << -w << " " << names_and_ids_tracker.pb_file_string_for(flag) << " ";
            },
            [&, w = w](const IntegerVariableID & var) {
                overloaded{
                    [&](const SimpleIntegerVariableID & var) {
                        for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(var))
                            stream << -w * bit_value << " " << names_and_ids_tracker.pb_file_string_for(bit_lit) << " ";
                    },
                    [&](const ViewOfIntegerVariableID & view) {
                        // Emit underlying-form bits with sign flip (for
                        // negate_first views) and RHS adjustment for the
                        // constant offset. The view's extension exists in
                        // the model (see preallocate_extensions_for_views_in)
                        // and the bridges in need_gevar / need_direct_encoding_for
                        // tie its atomic literals to the underlying's, but
                        // host-level constraints stay in underlying-form for
                        // verifier-side simplicity.
                        if (! view.negate_first) {
                            for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(view.actual_variable))
                                stream << -w * bit_value << " " << names_and_ids_tracker.pb_file_string_for(bit_lit) << " ";
                            rhs += w * view.then_add;
                        }
                        else {
                            for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(view.actual_variable))
                                stream << w * bit_value << " " << names_and_ids_tracker.pb_file_string_for(bit_lit) << " ";
                            rhs += w * view.then_add;
                        }
                    },
                    [&](const ConstantIntegerVariableID & cvar) {
                        rhs += w * cvar.const_value;
                    }}
                    .visit(var);
            },
            [&, w = w](const ProofOnlySimpleIntegerVariableID & var) {
                for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(var))
                    stream << -w * bit_value << " " << names_and_ids_tracker.pb_file_string_for(bit_lit) << " ";
            },
            [&, w = w](const ProofBitVariable & bit) {
                auto [_, bit_name] = names_and_ids_tracker.get_bit(bit);
                stream << -w << " " << names_and_ids_tracker.pb_file_string_for(bit_name) << " ";
            },
        }
            .visit(v);
    }

    stream << ">= " << rhs;
}
