#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/simplify_literal.hh>

#include <algorithm>

using std::any_of;
using std::max;
using std::optional;
using std::ostream;
using std::string;

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::emit_inequality_to(
    NamesAndIDsTracker & names_and_ids_tracker,
    const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
    const optional<HalfReifyOnConjunctionOf> & half_reif, ostream & stream) -> void
{
    // so what happens if there's a false literal in the left hand term? conceptually,
    // this means the constraint will always hold, but it's probably useful to have
    // something that syntactically contains all the right variables. so, we can just
    // make the degree of falsity be very low so the constraint always holds.
    auto contains_false_literal = false;
    if (half_reif) {
        contains_false_literal = any_of(half_reif->begin(), half_reif->end(),
            [&](const auto & flag) {
                return overloaded{
                    [&](const ProofFlag &) { return false; },
                    [&](const ProofLiteral & pl) {
                        return overloaded{
                            [&](Literal lit) { return is_literally_false(lit); },
                            [&](const ProofVariableCondition &) { return false; },
                        }
                            .visit(pl);
                    },
                    [&](const ProofBitVariable &) { return false; }}
                    .visit(flag);
            });
    }

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
                        stream << -w << " " << names_and_ids_tracker.pb_file_string_for(cond) << " ";
                        reif_const += max(0_i, w);
                    }}
                    .visit(simplify_literal(lit));
            },
            [&, w = w](const ProofFlag & flag) {
                stream << -w << " " << names_and_ids_tracker.pb_file_string_for(flag) << " ";
                reif_const += max(0_i, w);
            },
            [&, w = w](const IntegerVariableID & var) {
                overloaded{
                    [&](const SimpleIntegerVariableID & var) {
                        names_and_ids_tracker.for_each_bit(var, [&](Integer bit_value, const XLiteral & bit_lit) {
                            stream << -w * bit_value << " " << names_and_ids_tracker.pb_file_string_for(bit_lit) << " ";
                            reif_const += max(0_i, w * bit_value);
                        });
                    },
                    [&](const ViewOfIntegerVariableID & view) {
                        if (! view.negate_first) {
                            names_and_ids_tracker.for_each_bit(view.actual_variable,
                                [&](Integer bit_value, const XLiteral & bit_lit) {
                                    stream << -w * bit_value << " " << names_and_ids_tracker.pb_file_string_for(bit_lit) << " ";
                                    reif_const += max(0_i, w * bit_value);
                                });
                            rhs += w * view.then_add;
                            reif_const += max(0_i, -w * view.then_add);
                        }
                        else {
                            names_and_ids_tracker.for_each_bit(view.actual_variable,
                                [&](Integer bit_value, const XLiteral & bit_lit) {
                                    stream << w * bit_value << " " << names_and_ids_tracker.pb_file_string_for(bit_lit) << " ";
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
                names_and_ids_tracker.for_each_bit(var, [&](Integer bit_value, const XLiteral & bit_lit) {
                    stream << -w * bit_value << " " << names_and_ids_tracker.pb_file_string_for(bit_lit) << " ";
                    reif_const += max(0_i, w * bit_value);
                });
            },
            [&, w = w](const ProofBitVariable & bit) {
                auto [_, bit_name] = names_and_ids_tracker.get_bit(bit);
                stream << -w << " " << names_and_ids_tracker.pb_file_string_for(bit_name) << " ";
                reif_const += max(0_i, w);
            },
        }
            .visit(v);
    }

    if (half_reif) {
        reif_const += rhs;
        reif_const = max(reif_const, 1_i);
        for (auto & r : *half_reif)
            overloaded{
                [&](const ProofFlag & f) {
                    stream << reif_const << " " << names_and_ids_tracker.pb_file_string_for(! f) << " ";
                },
                [&](const ProofLiteral & lit) {
                    overloaded{
                        [&](const TrueLiteral &) {
                        },
                        [&](const FalseLiteral &) {
                            //    throw UnimplementedException{};
                        },
                        [&]<typename T_>(const VariableConditionFrom<T_> & cond) {
                            stream << reif_const << " " << names_and_ids_tracker.pb_file_string_for(! cond) << " ";
                        }}
                        .visit(simplify_literal(lit));
                },
                [&](const ProofBitVariable & bit) {
                    stream << reif_const << " " << names_and_ids_tracker.pb_file_string_for(names_and_ids_tracker.get_bit(! bit).second) << " ";
                }}
                .visit(r);
    }

    // if we have a false literal on the left hand side, adjusting the degree of falsity
    // down by reif_const is enough that it will be trivially true.
    stream << ">= " << (contains_false_literal ? rhs - reif_const : rhs) << " ;";
}
