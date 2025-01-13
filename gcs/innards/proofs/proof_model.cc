#include <gcs/innards/interval_set.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/bits_encoding.hh>
#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/simplify_literal.hh>

#include <algorithm>
#include <deque>
#include <fstream>
#include <iterator>
#include <map>
#include <sstream>
#include <unordered_map>

#include <fmt/core.h>

using namespace gcs;
using namespace gcs::innards;

using std::deque;
using std::fstream;
using std::istreambuf_iterator;
using std::map;
using std::nullopt;
using std::ofstream;
using std::optional;
using std::ostreambuf_iterator;
using std::pair;
using std::sort;
using std::string;
using std::stringstream;
using std::to_string;
using std::unique;
using std::unordered_map;
using std::variant;
using std::vector;

using fmt::format;

struct ProofModel::Imp
{
    NamesAndIDsTracker & tracker;

    unsigned long long model_variables = 0;
    ProofLine number_of_constraints = 0;
    ProofLine proof_line = 0;

    optional<IntegerVariableID> optional_minimise_variable;
    unsigned long long proof_only_integer_variable_nr = 0;

    string opb_file;
    stringstream opb;

    bool always_use_full_encoding = false;

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

ProofModel::~ProofModel() = default;

auto ProofModel::add_constraint(const StringLiteral & constraint_name, const StringLiteral & rule, const Literals & lits) -> std::optional<ProofLine>
{
    WeightedPseudoBooleanSum sum;

    for (auto & lit : lits) {
        if (overloaded{
                [&](const TrueLiteral &) { return true; },
                [&](const FalseLiteral &) { return false; },
                [&]<typename T_>(const VariableConditionFrom<T_> & cond) -> bool {
                    sum += 1_i * cond;
                    return false;
                }}
                .visit(simplify_literal(lit)))
            return nullopt;
    }

    // put these in some kind of order
    sort(sum.terms.begin(), sum.terms.end());

    // remove duplicates
    sum.terms.erase(unique(sum.terms.begin(), sum.terms.end()), sum.terms.end());

    return add_constraint(constraint_name, rule, move(sum) >= 1_i, nullopt);
}

auto ProofModel::add_constraint(const Literals & lits) -> std::optional<ProofLine>
{
    return add_constraint("?", "?", lits);
}

auto ProofModel::add_constraint(const StringLiteral & constraint_name, const StringLiteral & rule,
    const WeightedPseudoBooleanLessEqual & ineq, const optional<HalfReifyOnConjunctionOf> & half_reif) -> optional<ProofLine>
{
    names_and_ids_tracker().need_all_proof_names_in(ineq.lhs);
    if (half_reif)
        for (auto & r : *half_reif)
            overloaded{
                [&](const ProofFlag &) {},
                [&](const ProofLiteral & lit) {
                    overloaded{
                        [&](const TrueLiteral &) {},
                        [&](const FalseLiteral &) {},
                        [&]<typename T_>(const VariableConditionFrom<T_> & cond) { names_and_ids_tracker().need_proof_name(cond); }}
                        .visit(simplify_literal(lit));
                },
                [&](ProofBitVariable) {}}
                .visit(r);

    _imp->opb << "* constraint " << constraint_name.value << ' ' << rule.value << '\n';
    emit_inequality_to(names_and_ids_tracker(), ineq, half_reif, _imp->opb);
    _imp->opb << '\n';
    return ++_imp->number_of_constraints;
}

auto ProofModel::add_constraint(const WeightedPseudoBooleanLessEqual & ineq, const optional<HalfReifyOnConjunctionOf> & half_reif) -> optional<ProofLine>
{
    return add_constraint("?", "?", ineq, half_reif);
}

auto ProofModel::add_constraint(const StringLiteral & constraint_name, const StringLiteral & rule,
    const WeightedPseudoBooleanEquality & eq, const optional<HalfReifyOnConjunctionOf> & half_reif)
    -> pair<optional<ProofLine>, optional<ProofLine>>
{
    names_and_ids_tracker().need_all_proof_names_in(eq.lhs);
    if (half_reif)
        for (auto & r : *half_reif)
            overloaded{
                [&](const ProofFlag &) {},
                [&](const ProofLiteral & lit) {
                    overloaded{
                        [&](const TrueLiteral &) {},
                        [&](const FalseLiteral &) {},
                        [&]<typename T_>(const VariableConditionFrom<T_> & cond) { names_and_ids_tracker().need_proof_name(cond); }}
                        .visit(simplify_literal(lit));
                },
                [&](const ProofBitVariable &) {}}
                .visit(r);

    _imp->opb << "* constraint " << constraint_name.value << ' ' << rule.value << '\n';
    emit_inequality_to(names_and_ids_tracker(), eq.lhs <= eq.rhs, half_reif, _imp->opb);
    _imp->opb << '\n';
    auto first = ++_imp->number_of_constraints;

    emit_inequality_to(names_and_ids_tracker(), eq.lhs >= eq.rhs, half_reif, _imp->opb);
    _imp->opb << '\n';
    auto second = ++_imp->number_of_constraints;

    return pair{first, second};
}

auto ProofModel::add_constraint(const WeightedPseudoBooleanEquality & eq, const optional<HalfReifyOnConjunctionOf> & half_reif)
    -> pair<optional<ProofLine>, optional<ProofLine>>
{
    return add_constraint("?", "?", eq, half_reif);
}

auto ProofModel::names_and_ids_tracker() -> NamesAndIDsTracker &
{
    return _imp->tracker;
}

auto ProofModel::create_proof_only_integer_variable(Integer lower, Integer upper, const optional<string> & name,
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

auto ProofModel::set_up_direct_only_variable_encoding(SimpleOrProofOnlyIntegerVariableID id, Integer lower, Integer upper, const optional<string> & name) -> void
{
    if (0_i == lower && 1_i == upper) {
        names_and_ids_tracker().track_variable_name(id, name);
        auto eqvar = names_and_ids_tracker().allocate_xliteral_meaning(id, EqualsOrGreaterEqual::Equals, 1_i);
        _imp->opb << "1 " << names_and_ids_tracker().pb_file_string_for(eqvar) << " >= 0 ;\n";
        ++_imp->model_variables;
        ++_imp->number_of_constraints;

        overloaded{
            [&](const SimpleIntegerVariableID & id) {
                names_and_ids_tracker().associate_condition_with_xliteral(id == 1_i, eqvar);
                names_and_ids_tracker().associate_condition_with_xliteral(id != 1_i, ! eqvar);
                names_and_ids_tracker().associate_condition_with_xliteral(id == 0_i, ! eqvar);
                names_and_ids_tracker().associate_condition_with_xliteral(id != 0_i, eqvar);
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
        names_and_ids_tracker().track_variable_takes_at_least_one_value(id, ++_imp->number_of_constraints);

        for (auto v = lower; v <= upper; ++v) {
            _imp->opb << "-1 " << names_and_ids_tracker().pb_file_string_for(id == v) << " ";
        }
        _imp->opb << ">= -1 ;\n";
        ++_imp->number_of_constraints;
    }
}

auto ProofModel::set_up_integer_variable(SimpleIntegerVariableID id, Integer lower, Integer upper,
    const optional<string> & optional_name, const optional<IntegerVariableProofRepresentation> & rep) -> void
{
    if (! rep) {
        if (lower == 0_i && upper == 1_i)
            set_up_direct_only_variable_encoding(id, lower, upper, optional_name);
        else
            set_up_bits_variable_encoding(id, lower, upper, optional_name);
    }
    else {
        switch (*rep) {
        case IntegerVariableProofRepresentation::Bits:
            set_up_bits_variable_encoding(id, lower, upper, optional_name);
            break;
        case IntegerVariableProofRepresentation::DirectOnly:
            set_up_direct_only_variable_encoding(id, lower, upper, optional_name);
            break;
        }
    }
}

auto ProofModel::set_up_bits_variable_encoding(SimpleOrProofOnlyIntegerVariableID id, Integer lower, Integer upper, const optional<string> & name) -> void
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
    ++_imp->number_of_constraints;

    // upper bound
    for (auto & [coeff, var] : bits)
        _imp->opb << -coeff << " " << names_and_ids_tracker().pb_file_string_for(var) << " ";
    _imp->opb << ">= " << -upper << " ;\n";
    ++_imp->number_of_constraints;

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
    ofstream full_opb{_imp->opb_file};
    full_opb << "* #variable= " << _imp->model_variables << " #constraint= " << _imp->number_of_constraints << '\n';

    if (_imp->optional_minimise_variable) {
        full_opb << "min: ";
        overloaded{
            [&](const SimpleIntegerVariableID & v) {
                names_and_ids_tracker().for_each_bit(v, [&](Integer bit_value, const XLiteral & bit_name) {
                    full_opb << bit_value << " " << names_and_ids_tracker().pb_file_string_for(bit_name) << " ";
                });
            },
            [&](const ConstantIntegerVariableID &) {
                throw UnimplementedException{};
            },
            [&](const ViewOfIntegerVariableID & v) {
                // the "then add" bit is irrelevant for the objective function
                names_and_ids_tracker().for_each_bit(v.actual_variable, [&](Integer bit_value, const XLiteral & bit_name) {
                    full_opb << (v.negate_first ? -bit_value : bit_value) << " " << names_and_ids_tracker().pb_file_string_for(bit_name) << " ";
                });
            }}
            .visit(*_imp->optional_minimise_variable);

        full_opb << " ;\n";
    }

    copy(istreambuf_iterator<char>{_imp->opb}, istreambuf_iterator<char>{}, ostreambuf_iterator<char>{full_opb});
    _imp->opb = stringstream{};

    if (! full_opb)
        throw ProofError{"Error writing opb file to '" + _imp->opb_file + "'"};
    full_opb.close();
}

auto ProofModel::number_of_constraints() const -> ProofLine
{
    return _imp->number_of_constraints;
}

auto ProofModel::minimise(const IntegerVariableID & var) -> void
{
    _imp->optional_minimise_variable = var;
}
