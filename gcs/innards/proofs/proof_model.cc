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

    string opb_file;
    stringstream opb;

    bool always_use_full_encoding = false;
    bool finalised = false;

    explicit Imp(NamesAndIDsTracker & t) :
        tracker(t)
    {
    }
};

ProofModel::ProofModel(const ProofOptions & proof_options, NamesAndIDsTracker & t) :
    _imp(new Imp{t})
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

namespace
{
    // Build a pol line that, starting from the extension-form constraint at
    // `ext_line`, adds e-def lines to cancel each view operand's `e` term
    // and recover the underlying-form constraint.
    //
    // `which_half` is which half (LE or GE) of the just-emitted equality the
    // ext_line corresponds to. For each view operand with weight w:
    //  - LE half OPB coef on e is -w; cancel by adding e-def with +w on e
    //    (e-def-GE for w > 0, e-def-LE for w < 0).
    //  - GE half OPB coef on e is +w; cancel using the opposite e-def.
    //
    // Only ±1 weights are handled here; chains across multiple views in one
    // constraint are emitted as a single pol with successive additions.
    enum class ConstraintHalf
    {
        LE,
        GE
    };

    auto emit_view_bridge_pol_lines(NamesAndIDsTracker & tracker,
        const WPBSum & original_lhs, optional<ProofLine> ext_line, ConstraintHalf which_half) -> void
    {
        if (! ext_line)
            return;

        std::vector<ProofLine> defs_to_add;
        bool any_view = false;
        for (const auto & [w, term] : original_lhs.terms) {
            if (! std::holds_alternative<IntegerVariableID>(term))
                continue;
            const auto & var_id = std::get<IntegerVariableID>(term);
            if (! std::holds_alternative<ViewOfIntegerVariableID>(var_id))
                continue;
            const auto & view = std::get<ViewOfIntegerVariableID>(var_id);
            auto def_lines = tracker.extension_def_lines_for(view);
            if (! def_lines || ! def_lines->first || ! def_lines->second)
                continue;
            if (w != 1_i && w != -1_i)
                continue; // multi-coef bridges not handled yet
            any_view = true;

            ProofLine line_to_add;
            if (which_half == ConstraintHalf::LE)
                line_to_add = (w > 0_i) ? *def_lines->second : *def_lines->first;
            else
                line_to_add = (w > 0_i) ? *def_lines->first : *def_lines->second;
            defs_to_add.push_back(line_to_add);
        }

        if (! any_view)
            return;

        std::stringstream pol_str;
        pol_str << "pol " << *ext_line;
        for (const auto & d : defs_to_add)
            pol_str << " " << d << " +";
        pol_str << " s ;";
        tracker.schedule_pol_line_at_proof_start(pol_str.str());
    }

    // Substitute every ViewOfIntegerVariableID inside a PseudoBooleanTerm with
    // its extension. Other variants are passed through unchanged.
    auto substitute_views_in_term(const PseudoBooleanTerm & term, NamesAndIDsTracker & tracker) -> PseudoBooleanTerm
    {
        return overloaded{
            [&](const IntegerVariableID & var) -> PseudoBooleanTerm {
                return overloaded{
                    [&](const SimpleIntegerVariableID &) -> PseudoBooleanTerm { return var; },
                    [&](const ConstantIntegerVariableID &) -> PseudoBooleanTerm { return var; },
                    [&](const ViewOfIntegerVariableID & view) -> PseudoBooleanTerm {
                        return tracker.extension_for(view);
                    }}
                    .visit(var);
            },
            [&](const ProofLiteral & lit) -> PseudoBooleanTerm {
                return overloaded{
                    [&](const Literal & l) -> PseudoBooleanTerm {
                        return overloaded{
                            [&](const TrueLiteral &) -> PseudoBooleanTerm { return lit; },
                            [&](const FalseLiteral &) -> PseudoBooleanTerm { return lit; },
                            [&](const IntegerVariableCondition & cond) -> PseudoBooleanTerm {
                                return overloaded{
                                    [&](const SimpleIntegerVariableID &) -> PseudoBooleanTerm { return lit; },
                                    [&](const ConstantIntegerVariableID &) -> PseudoBooleanTerm { return lit; },
                                    [&](const ViewOfIntegerVariableID & view) -> PseudoBooleanTerm {
                                        auto ext = tracker.extension_for(view);
                                        return ProofLiteral{ProofVariableCondition{ext, cond.op, cond.value}};
                                    }}
                                    .visit(cond.var);
                            }}
                            .visit(l);
                    },
                    [&](const ProofVariableCondition &) -> PseudoBooleanTerm { return lit; }}
                    .visit(lit);
            },
            [&](const ProofFlag &) -> PseudoBooleanTerm { return term; },
            [&](const ProofOnlySimpleIntegerVariableID &) -> PseudoBooleanTerm { return term; },
            [&](const ProofBitVariable &) -> PseudoBooleanTerm { return term; }}
            .visit(term);
    }

    template <typename Sum_>
    auto substitute_views(const Sum_ & sum, NamesAndIDsTracker & tracker) -> Sum_
    {
        Sum_ result = sum;
        for (auto & [w, term] : result.lhs.terms)
            term = substitute_views_in_term(term, tracker);
        return result;
    }
}

auto ProofModel::add_constraint(const StringLiteral & constraint_name, const StringLiteral & rule, const Literals & lits) -> std::optional<ProofLine>
{
    WPBSum sum;

    for (auto & lit : lits) {
        if (overloaded{
                [&](const TrueLiteral &) { return true; },
                [&](const FalseLiteral &) { return false; },
                [&]<typename T_>(const VariableConditionFrom<T_> & cond) -> bool {
                    sum += 1_i * cond;
                    return false;
                }}
                .visit(simplify_literal(names_and_ids_tracker(), lit)))
            return nullopt;
    }

    // put these in some kind of order
    sort(sum.terms);

    // remove duplicates
    sum.terms.erase(unique(sum.terms).begin(), sum.terms.end());

    return add_constraint(constraint_name, rule, move(sum) >= 1_i, nullopt);
}

auto ProofModel::add_constraint(const Literals & lits) -> std::optional<ProofLine>
{
    return add_constraint("?", "?", lits);
}

auto ProofModel::add_constraint(const StringLiteral & constraint_name, const StringLiteral & rule,
    const WPBSumLE & ineq, const optional<HalfReifyOnConjunctionOf> & half_reif) -> optional<ProofLine>
{
    // Substitute views with their extension variables before the rest of the
    // pipeline sees the constraint. This keeps emit_inequality_to / reify
    // working on bit-clean (view-free) sums.
    auto substituted = substitute_views(ineq, names_and_ids_tracker());

    names_and_ids_tracker().need_all_proof_names_in(substituted.lhs);
    if (half_reif)
        names_and_ids_tracker().need_all_proof_names_in(*half_reif);

    _imp->opb << "* constraint " << constraint_name.value << ' ' << rule.value << '\n';
    emit_inequality_to(names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(substituted, *half_reif) : substituted, _imp->opb);
    _imp->opb << ";\n";
    auto ext_line = advance_constraint_counter();
    if (! half_reif)
        emit_view_bridge_pol_lines(names_and_ids_tracker(), ineq.lhs, ext_line, ConstraintHalf::LE);
    return ext_line;
}

auto ProofModel::add_constraint(const WPBSumLE & ineq, const optional<HalfReifyOnConjunctionOf> & half_reif) -> optional<ProofLine>
{
    return add_constraint("?", "?", ineq, half_reif);
}

auto ProofModel::add_constraint(const StringLiteral & constraint_name, const StringLiteral & rule,
    const WPBSumEq & eq, const optional<HalfReifyOnConjunctionOf> & half_reif)
    -> pair<optional<ProofLine>, optional<ProofLine>>
{
    auto substituted = substitute_views(eq, names_and_ids_tracker());

    names_and_ids_tracker().need_all_proof_names_in(substituted.lhs);
    if (half_reif)
        names_and_ids_tracker().need_all_proof_names_in(*half_reif);

    _imp->opb << "* constraint " << constraint_name.value << ' ' << rule.value << '\n';
    emit_inequality_to(names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(substituted.lhs <= substituted.rhs, *half_reif) : substituted.lhs <= substituted.rhs, _imp->opb);
    _imp->opb << ";\n";
    auto first = advance_constraint_counter();

    emit_inequality_to(names_and_ids_tracker(), half_reif ? names_and_ids_tracker().reify(substituted.lhs >= substituted.rhs, *half_reif) : substituted.lhs >= substituted.rhs, _imp->opb);
    _imp->opb << ";\n";
    auto second = advance_constraint_counter();

    if (! half_reif) {
        emit_view_bridge_pol_lines(names_and_ids_tracker(), eq.lhs, first, ConstraintHalf::LE);
        emit_view_bridge_pol_lines(names_and_ids_tracker(), eq.lhs, second, ConstraintHalf::GE);
    }

    return pair{first, second};
}

auto ProofModel::add_constraint(const WPBSumEq & eq, const optional<HalfReifyOnConjunctionOf> & half_reif)
    -> pair<optional<ProofLine>, optional<ProofLine>>
{
    return add_constraint("?", "?", eq, half_reif);
}

auto ProofModel::add_two_way_reified_constraint(const StringLiteral & constraint_name, const StringLiteral & rule,
    const WPBSumLE & ineq, const ProofFlag & flag) -> pair<optional<ProofLine>, optional<ProofLine>>
{
    auto forward = add_constraint(constraint_name, rule, ineq, HalfReifyOnConjunctionOf{{flag}});
    auto reverse = add_constraint(constraint_name, rule, negate_inequality(ineq), HalfReifyOnConjunctionOf{{! flag}});
    return {forward, reverse};
}

auto ProofModel::create_proof_flag_fully_reifying(const string & flag_name,
    const StringLiteral & constraint_name, const StringLiteral & rule, const WPBSumLE & ineq) -> ProofFlag
{
    auto flag = create_proof_flag(flag_name);
    add_two_way_reified_constraint(constraint_name, rule, ineq, flag);
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

auto ProofModel::allocate_extension_for_view(const ViewOfIntegerVariableID & view)
    -> std::tuple<ProofOnlySimpleIntegerVariableID, optional<ProofLine>, optional<ProofLine>>
{
    // Visible domain of the view, derived from the underlying's definition
    // bounds. Negation swaps the endpoint roles.
    auto [actual_lo, actual_hi] = names_and_ids_tracker().bounds_for(view.actual_variable);
    Integer visible_lo = view.negate_first ? (-actual_hi + view.then_add) : (actual_lo + view.then_add);
    Integer visible_hi = view.negate_first ? (-actual_lo + view.then_add) : (actual_hi + view.then_add);

    auto name = "extension_v" + std::to_string(_imp->proof_only_integer_variable_nr) + (view.negate_first ? "_neg" : "")
        + (view.then_add == 0_i ? "" : ("_p" + std::to_string(view.then_add.raw_value)));

    auto ext_id = create_proof_only_integer_variable(visible_lo, visible_hi, name, IntegerVariableProofRepresentation::Bits);

    // Definitional: e == (negate_first ? -actual : actual) + then_add, emitted
    // as two halves. The constraint's LHS terms reference the extension
    // (ProofOnlySimpleIntegerVariableID) and the underlying (SimpleIntegerVariableID
    // wrapped in IntegerVariableID); neither is a view, so the recursive call
    // to add_constraint won't trigger another extension lookup.
    auto actual_coeff = view.negate_first ? 1_i : -1_i;
    auto [le_line, ge_line] = add_constraint("ViewExtension", "definitional",
        WPBSum{} + 1_i * ext_id + actual_coeff * IntegerVariableID{view.actual_variable} == view.then_add);

    return {ext_id, le_line, ge_line};
}

auto ProofModel::create_proof_only_integer_variable(Integer lower, Integer upper, const string & name,
    const IntegerVariableProofRepresentation rep) -> ProofOnlySimpleIntegerVariableID
{
    ProofOnlySimpleIntegerVariableID id{_imp->proof_only_integer_variable_nr++};
    switch (rep) {
    case IntegerVariableProofRepresentation::DirectOnly:
        set_up_direct_only_variable_encoding(id, lower, upper, name);
        break;
    case IntegerVariableProofRepresentation::Bits:
        set_up_bits_variable_encoding(id, lower, upper, name);
        break;
    }

    return id;
}

auto ProofModel::set_up_direct_only_variable_encoding(SimpleOrProofOnlyIntegerVariableID id, Integer lower, Integer upper,
    const string & name) -> void
{
    names_and_ids_tracker().track_bounds(id, lower, upper);

    if (0_i == lower && 1_i == upper) {
        names_and_ids_tracker().track_variable_name(id, name);
        auto eqvar = names_and_ids_tracker().allocate_xliteral_meaning(id, EqualsOrGreaterEqual::Equals, 1_i);
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
            },
            [](const ProofOnlySimpleIntegerVariableID &) {
                // currently there's no API for asking for literals for these
            }}
            .visit(id);

        names_and_ids_tracker().track_bits(id, 0_i, {{1_i, eqvar}});

        overloaded{
            [&](const SimpleIntegerVariableID & id) {
                names_and_ids_tracker().associate_condition_with_xliteral(id >= 1_i, eqvar);
                names_and_ids_tracker().associate_condition_with_xliteral(id < 1_i, ! eqvar);
                pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>> names{eqvar, ! eqvar};
                names_and_ids_tracker().track_gevar(id, 1_i, names);
            },
            [](const ProofOnlySimpleIntegerVariableID &) {
                // currently there's no API for asking for literals for these
            }}
            .visit(id);
    }
    else {
        for (auto v = lower; v <= upper; ++v) {
            names_and_ids_tracker().track_variable_name(id, name);
            auto eqvar = names_and_ids_tracker().allocate_xliteral_meaning(id, EqualsOrGreaterEqual::Equals, v);
            _imp->opb << "1 " << names_and_ids_tracker().pb_file_string_for(eqvar) << " ";
            ++_imp->model_variables;

            visit([&](const auto & id) {
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
        advance_constraint_counter();
    }
}

auto ProofModel::set_up_integer_variable(SimpleIntegerVariableID id, Integer lower, Integer upper,
    const string & name, const optional<IntegerVariableProofRepresentation> & rep) -> void
{
    if (! rep) {
        if (lower == 0_i && upper == 1_i)
            set_up_direct_only_variable_encoding(id, lower, upper, name);
        else
            set_up_bits_variable_encoding(id, lower, upper, name);
    }
    else {
        switch (*rep) {
        case IntegerVariableProofRepresentation::Bits:
            set_up_bits_variable_encoding(id, lower, upper, name);
            break;
        case IntegerVariableProofRepresentation::DirectOnly:
            set_up_direct_only_variable_encoding(id, lower, upper, name);
            break;
        }
    }
}

auto ProofModel::set_up_bits_variable_encoding(SimpleOrProofOnlyIntegerVariableID id, Integer lower, Integer upper,
    const string & name) -> void
{
    auto [highest_bit_shift, highest_bit_coeff, negative_bit_coeff] = get_bits_encoding_coeffs(lower, upper);
    vector<pair<Integer, XLiteral>> bits;

    names_and_ids_tracker().track_variable_name(id, name);
    if (0_i != negative_bit_coeff)
        bits.emplace_back(negative_bit_coeff, names_and_ids_tracker().allocate_xliteral_meaning_negative_bit_of(id, negative_bit_coeff));
    for (Integer b = 0_i; b <= highest_bit_shift; ++b)
        bits.emplace_back(power2(b), names_and_ids_tracker().allocate_xliteral_meaning_bit_of(id, Integer{b}));

    names_and_ids_tracker().track_bits(id, negative_bit_coeff, bits);
    _imp->model_variables += bits.size();

    // lower bound
    for (auto & [coeff, var] : bits)
        _imp->opb << coeff << " " << names_and_ids_tracker().pb_file_string_for(var) << " ";
    _imp->opb << ">= " << lower << " ;\n";
    advance_constraint_counter();

    // upper bound
    for (auto & [coeff, var] : bits)
        _imp->opb << -coeff << " " << names_and_ids_tracker().pb_file_string_for(var) << " ";
    _imp->opb << ">= " << -upper << " ;\n";
    advance_constraint_counter();

    names_and_ids_tracker().track_bounds(id, lower, upper);

    if (_imp->always_use_full_encoding)
        overloaded{
            [&](const SimpleIntegerVariableID & id) {
                for (; lower <= upper; ++lower)
                    names_and_ids_tracker().need_direct_encoding_for(id, lower);
            },
            [&](const ProofOnlySimpleIntegerVariableID &) {
            }}
            .visit(id);
}

auto ProofModel::create_proof_flag(const string & name) -> ProofFlag
{
    return names_and_ids_tracker().create_proof_flag(name);
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
                },
                [&](const ConstantIntegerVariableID &) {
                    throw UnimplementedException{};
                },
                [&](const ViewOfIntegerVariableID & v) {
                    // the "then add" bit is irrelevant for the objective function
                    for (const auto & [bit_value, bit_name] : names_and_ids_tracker().each_bit(v.actual_variable))
                        full_opb << (v.negate_first ? -bit_value : bit_value) << " " << names_and_ids_tracker().pb_file_string_for(bit_name) << " ";
                }}
                .visit(*_imp->optional_minimise_variable);

            full_opb << ";\n";
        }

        if (_imp->preserved_variables) {
            full_opb << "preserved: ";
            for (const auto & var : *_imp->preserved_variables) {
                overloaded{
                    [&](const SimpleIntegerVariableID & v) {
                        for (const auto & [bit_value, bit_name] : names_and_ids_tracker().each_bit(v))
                            full_opb << names_and_ids_tracker().pb_file_string_for(bit_name) << " ";
                    },
                    [&](const ConstantIntegerVariableID &) {
                    },
                    [&](const ViewOfIntegerVariableID & v) {
                        // the "then add" bit is irrelevant for the objective function
                        for (const auto & [bit_value, bit_name] : names_and_ids_tracker().each_bit(v.actual_variable))
                            full_opb << names_and_ids_tracker().pb_file_string_for(bit_name) << " ";
                    }}
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
