#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>

using std::max;
using std::optional;
using std::ostream;
using std::string;

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::emit_inequality_to(
    VariableConstraintsTracker & variable_constraints_tracker,
    const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
    const optional<HalfReifyOnConjunctionOf> & half_reif, ostream & stream) -> void
{
    // build up the inequality, adjusting as we go for constant terms,
    // and converting from <= to >=.
    Integer rhs = -ineq.rhs;
    Integer reif_const = 0_i;
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
                        stream << -w << " " << variable_constraints_tracker.pb_file_string_for(cond) << " ";
                        reif_const += max(0_i, w);
                    }}
                    .visit(simplify_literal(lit));
            },
            [&, w = w](const ProofFlag & flag) {
                stream << -w << " " << variable_constraints_tracker.pb_file_string_for(flag) << " ";
                reif_const += max(0_i, w);
            },
            [&, w = w](const IntegerVariableID & var) {
                overloaded{
                    [&](const SimpleIntegerVariableID & var) {
                        variable_constraints_tracker.for_each_bit(var, [&](Integer bit_value, const XLiteral & bit_lit) {
                            stream << -w * bit_value << " " << variable_constraints_tracker.pb_file_string_for(bit_lit) << " ";
                            reif_const += max(0_i, w * bit_value);
                        });
                    },
                    [&](const ViewOfIntegerVariableID & view) {
                        if (! view.negate_first) {
                            variable_constraints_tracker.for_each_bit(view.actual_variable,
                                [&](Integer bit_value, const XLiteral & bit_lit) {
                                    stream << -w * bit_value << " " << variable_constraints_tracker.pb_file_string_for(bit_lit) << " ";
                                    reif_const += max(0_i, w * bit_value);
                                });
                            rhs += w * view.then_add;
                            reif_const += max(0_i, -w * view.then_add);
                        }
                        else {
                            variable_constraints_tracker.for_each_bit(view.actual_variable,
                                [&](Integer bit_value, const XLiteral & bit_lit) {
                                    stream << w * bit_value << " " << variable_constraints_tracker.pb_file_string_for(bit_lit) << " ";
                                    reif_const += max(0_i, -w * bit_value);
                                });
                            rhs += w * view.then_add;
                            reif_const += max(0_i, -w * view.then_add);
                        }
                    },
                    [&](const ConstantIntegerVariableID & cvar) {
                        rhs += w * cvar.const_value;
                    }}
                    .visit(var);
            },
            [&, w = w](const ProofOnlySimpleIntegerVariableID & var) {
                variable_constraints_tracker.for_each_bit(var, [&](Integer bit_value, const XLiteral & bit_lit) {
                    stream << -w * bit_value << " " << variable_constraints_tracker.pb_file_string_for(bit_lit) << " ";
                    reif_const += max(0_i, w * bit_value);
                });
            }}
            .visit(v);
    }

    if (half_reif) {
        reif_const += rhs;
        for (auto & r : *half_reif)
            overloaded{
                [&](const ProofFlag & f) {
                    stream << reif_const << " " << variable_constraints_tracker.pb_file_string_for(! f) << " ";
                },
                [&](const ProofLiteral & lit) {
                    overloaded{
                        [&](const TrueLiteral &) {
                        },
                        [&](const FalseLiteral &) {
                            throw UnimplementedException{};
                        },
                        [&]<typename T_>(const VariableConditionFrom<T_> & cond) {
                            stream << reif_const << " " << variable_constraints_tracker.pb_file_string_for(! cond) << " ";
                        }}
                        .visit(simplify_literal(lit));
                }}
                .visit(r);
    }

    stream << ">= " << rhs << " ;";
}
