#include <gcs/exception.hh>
#include <gcs/innards/bits_encoding.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/opb_utils.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/state.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <iterator>
#include <list>
#include <map>
#include <set>
#include <sstream>
#include <tuple>
#include <unordered_map>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::copy;
using std::flush;
using std::fstream;
using std::ios;
using std::istreambuf_iterator;
using std::list;
using std::map;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::ofstream;
using std::optional;
using std::ostream;
using std::ostreambuf_iterator;
using std::pair;
using std::set;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unordered_map;
using std::variant;
using std::vector;
using std::visit;

namespace
{
    auto value_name(Integer v) -> string
    {
        return to_string(v.raw_value);
    }

    using FlattenedProofLiteral = variant<IntegerVariableCondition, TrueLiteral, FalseLiteral, ProofVariableCondition>;

    auto flatten(const ProofLiteral & lit) -> FlattenedProofLiteral
    {
        return overloaded{
            [&](const Literal & lit) {
                return visit([&](const auto & v) -> FlattenedProofLiteral { return v; }, lit);
            },
            [&](const ProofVariableCondition & cond) -> FlattenedProofLiteral {
                return cond;
            }}
            .visit(lit);
    }

    [[nodiscard]] auto deview(const VariableConditionFrom<ViewOfIntegerVariableID> & cond) -> VariableConditionFrom<SimpleIntegerVariableID>
    {
        switch (cond.op) {
        case VariableConditionOperator::NotEqual:
            return cond.var.actual_variable != (cond.var.negate_first ? -cond.value + cond.var.then_add : cond.value - cond.var.then_add);
        case VariableConditionOperator::Equal:
            return cond.var.actual_variable == (cond.var.negate_first ? -cond.value + cond.var.then_add : cond.value - cond.var.then_add);
        case VariableConditionOperator::Less:
            if (cond.var.negate_first)
                return cond.var.actual_variable >= cond.value - cond.var.then_add + 1_i;
            else
                return cond.var.actual_variable < (cond.value - cond.var.then_add);
        case VariableConditionOperator::GreaterEqual:
            if (cond.var.negate_first)
                return cond.var.actual_variable < cond.value - cond.var.then_add + 1_i;
            else
                return cond.var.actual_variable >= (cond.value - cond.var.then_add);
        }
        throw NonExhaustiveSwitch{};
    }
}

ProofError::ProofError(const string & w) :
    _wat("unexpected problem: " + w)
{
}

auto ProofError::what() const noexcept -> const char *
{
    return _wat.c_str();
}

auto gcs::innards::operator!(const ProofFlag & f) -> ProofFlag
{
    return ProofFlag{f.index, ! f.positive};
}

struct Proof::Imp
{
    unsigned long long model_variables = 0;
    ProofLine model_constraints = 0;
    ProofLine proof_line = 0;
    int active_proof_level = 0;

    map<SimpleOrProofOnlyIntegerVariableID, ProofLine> variable_at_least_one_constraints;
    map<VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID>, string> direct_integer_variables;
    map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, vector<pair<Integer, string>>>> integer_variable_bits;
    map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, Integer>> bounds_for_gevars;
    map<SimpleOrProofOnlyIntegerVariableID, set<Integer>> gevars_that_exist;
    list<SimpleIntegerVariableID> solution_variables;
    map<pair<unsigned long long, bool>, string> flags;
    map<unsigned long long, string> proof_only_integer_variables;

    list<map<tuple<bool, SimpleIntegerVariableID, Integer>, variant<ProofLine, string>>> line_for_bound_in_bits;

    string opb_file, proof_file;
    stringstream opb;
    fstream proof;
    bool opb_done = false;

    bool use_friendly_names;
    bool always_use_full_encoding;
    unordered_map<string, string> xification;
};

Proof::Proof(const ProofOptions & proof_options) :
    _imp(new Imp)
{
    _imp->opb_file = proof_options.opb_file;
    _imp->proof_file = proof_options.proof_file;
    _imp->use_friendly_names = proof_options.use_friendly_names;
    _imp->always_use_full_encoding = proof_options.always_use_full_encoding;
    _imp->line_for_bound_in_bits.emplace_back();
}

Proof::~Proof() = default;

Proof::Proof(Proof && other) noexcept :
    _imp(move(other._imp))
{
}

auto Proof::operator=(Proof && other) noexcept -> Proof &
{
    _imp = move(other._imp);
    return *this;
}

[[nodiscard]] auto Proof::xify(std::string && s) -> std::string
{
    if (_imp->use_friendly_names)
        return s;
    else
        return _imp->xification.try_emplace(s, "x" + to_string(_imp->xification.size() + 1)).first->second;
}

auto Proof::set_up_bits_variable_encoding(SimpleOrProofOnlyIntegerVariableID id, Integer lower, Integer upper, const string & name) -> void
{
    if (_imp->opb_done)
        throw UnexpectedException{"proof has already started"};

    _imp->opb << "* variable " << name << " " << lower.raw_value << " .. " << upper.raw_value << " bits encoding\n";
    auto [highest_bit_shift, highest_bit_coeff, negative_bit_coeff] = get_bits_encoding_coeffs(lower, upper);
    auto & bit_vars = _imp->integer_variable_bits.emplace(id, pair{negative_bit_coeff, vector<pair<Integer, string>>{}}).first->second.second;
    if (0_i != negative_bit_coeff)
        bit_vars.emplace_back(negative_bit_coeff, xify(name + "_bn_" + to_string(highest_bit_shift + 1)));
    for (int b = 0; b <= highest_bit_shift; ++b)
        bit_vars.emplace_back(Integer{1ll << b}, xify(name + "_b_" + to_string(b)));
    _imp->model_variables += bit_vars.size();

    // lower bound
    for (auto & [coeff, var] : bit_vars)
        _imp->opb << coeff << " " << var << " ";
    _imp->opb << ">= " << lower << " ;\n";
    ++_imp->model_constraints;

    overloaded{
        [&](const SimpleIntegerVariableID & id) {
            _imp->line_for_bound_in_bits.back().emplace(tuple{false, id, lower}, ProofLine{_imp->model_constraints});
        },
        [&](const ProofOnlySimpleIntegerVariableID &) {
        }}
        .visit(id);

    // upper bound
    for (auto & [coeff, var] : bit_vars)
        _imp->opb << -coeff << " " << var << " ";
    _imp->opb << ">= " << -upper << " ;\n";
    ++_imp->model_constraints;

    overloaded{
        [&](const SimpleIntegerVariableID & id) {
            _imp->line_for_bound_in_bits.back().emplace(tuple{true, id, upper}, ProofLine{_imp->model_constraints});
        },
        [&](const ProofOnlySimpleIntegerVariableID &) {
        }}
        .visit(id);

    _imp->bounds_for_gevars.emplace(id, pair{lower, upper});

    if (_imp->always_use_full_encoding)
        overloaded{
            [&](const SimpleIntegerVariableID & id) {
                for (; lower <= upper; ++lower)
                    need_direct_encoding_for(id, lower);
            },
            [&](const ProofOnlySimpleIntegerVariableID &) {
            }}
            .visit(id);
}

auto Proof::set_up_direct_only_variable_encoding(SimpleOrProofOnlyIntegerVariableID id, Integer lower, Integer upper, const string & name) -> void
{
    if (_imp->opb_done)
        throw UnexpectedException{"proof has already started"};

    _imp->opb << "* variable " << name << " " << lower.raw_value << " .. " << upper.raw_value << " direct encoding\n";

    if (0_i == lower && 1_i == upper) {
        auto eqvar = xify(name + "_t");
        _imp->opb << "1 " << eqvar << " >= 0 ;\n";
        ++_imp->model_variables;
        ++_imp->model_constraints;

        overloaded{
            [&](const SimpleIntegerVariableID & id) {
                _imp->line_for_bound_in_bits.back().emplace(tuple{false, id, lower}, eqvar);
                _imp->line_for_bound_in_bits.back().emplace(tuple{true, id, upper}, "~" + eqvar);

                _imp->direct_integer_variables.emplace(id == 1_i, eqvar);
                _imp->direct_integer_variables.emplace(id != 1_i, "~" + eqvar);
                _imp->direct_integer_variables.emplace(id == 0_i, "~" + eqvar);
                _imp->direct_integer_variables.emplace(id != 0_i, eqvar);
            },
            [](const ProofOnlySimpleIntegerVariableID &) {
                // currently there's no API for asking for literals for these
            }}
            .visit(id);

        auto & bit_vars = _imp->integer_variable_bits.emplace(id, pair{0_i, vector<pair<Integer, string>>{}}).first->second.second;
        bit_vars.emplace_back(1_i, eqvar);

        overloaded{
            [&](const SimpleIntegerVariableID & id) {
                _imp->direct_integer_variables.emplace(id >= 1_i, eqvar);
                _imp->direct_integer_variables.emplace(id < 1_i, "~" + eqvar);
            },
            [](const ProofOnlySimpleIntegerVariableID &) {
                // currently there's no API for asking for literals for these
            }}
            .visit(id);
    }
    else {
        for (auto v = lower; v <= upper; ++v) {
            auto eqvar = xify(name + "_eq_" + value_name(v));
            _imp->opb << "1 " << eqvar << " ";
            ++_imp->model_variables;

            visit([&](const auto & id) {
                _imp->direct_integer_variables.emplace(id == v, eqvar);
                _imp->direct_integer_variables.emplace(id != v, "~" + eqvar);
            },
                id);
        }
        _imp->opb << ">= 1 ;\n";
        _imp->variable_at_least_one_constraints.emplace(id, ++_imp->model_constraints);

        for (auto v = lower; v <= upper; ++v) {
            auto eqvar = xify(name + "_eq_" + value_name(v));
            _imp->opb << "-1 " << eqvar << " ";
        }
        _imp->opb << ">= -1 ;\n";
        ++_imp->model_constraints;
    }
}

auto Proof::set_up_integer_variable(SimpleIntegerVariableID id, Integer lower, Integer upper,
    const optional<string> & optional_name, const optional<IntegerVariableProofRepresentation> & rep) -> void
{
    string name = "iv" + to_string(id.index);
    if (optional_name)
        name.append("_" + *optional_name);
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
    _imp->solution_variables.push_back(id);
}

auto Proof::create_proof_flag(const string & n) -> ProofFlag
{
    ProofFlag result{_imp->flags.size() / 2, true};

    string name = xify("flag" + to_string(result.index) + "_" + n);
    _imp->flags.emplace(pair{result.index, true}, name);
    _imp->flags.emplace(pair{result.index, false}, "~" + name);
    return result;
}

auto Proof::create_proof_integer_variable(Integer lower, Integer upper, const std::string & s,
    const IntegerVariableProofRepresentation rep) -> ProofOnlySimpleIntegerVariableID
{
    ProofOnlySimpleIntegerVariableID id{_imp->proof_only_integer_variables.size()};
    _imp->proof_only_integer_variables.emplace(id.index, s);
    string name = "poiv" + to_string(id.index) + "_" + s;
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

auto Proof::need_gevar(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> void
{
    using namespace gcs::innards::opb_utils;

    if (_imp->direct_integer_variables.contains(id >= v))
        return;

    string name = "iv" + to_string(visit([&](const auto & var) { return var.index; }, id));
    auto gevar = xify(name + "_ge_" + value_name(v));
    _imp->direct_integer_variables.emplace(id >= v, gevar);
    _imp->direct_integer_variables.emplace(id < v, "~" + gevar);
    _imp->gevars_that_exist[id].insert(v);

    if (_imp->opb_done)
        _imp->proof << "* need " << gevar << std::endl;
    else
        _imp->opb << "* need " << gevar << '\n';

    auto & [_, bit_vars] = _imp->integer_variable_bits.at(id);

    if (_imp->opb_done)
        _imp->proof << "# 0\n";

    // gevar -> bits
    auto gevar_implies_bits = implied_by(opb_sum(bit_vars) >= v, gevar);
    if (_imp->opb_done) {
        _imp->proof << "red " << gevar_implies_bits << " ; " << gevar << " 0\n";
        ++_imp->proof_line;
    }
    else {
        _imp->opb << gevar_implies_bits << " ;\n";
        ++_imp->model_constraints;
        ++_imp->model_variables;
    }

    // !gevar -> bits
    auto not_gevar_implies_bits = implied_by(opb_sum(bit_vars) < v, negate_opb_var_name(gevar));
    if (_imp->opb_done) {
        _imp->proof << "red " << not_gevar_implies_bits << " ; " << gevar << " 1\n";
        ++_imp->proof_line;
    }
    else {
        _imp->opb << not_gevar_implies_bits << " ;\n";
        ++_imp->model_constraints;
    }

    // is it a bound?
    auto bounds = _imp->bounds_for_gevars.find(id);

    // lower?
    if (bounds != _imp->bounds_for_gevars.end() && bounds->second.first == v) {
        if (_imp->opb_done) {
            _imp->proof << "u 1 " << gevar << " >= 1 ;\n";
            ++_imp->proof_line;
        }
        else {
            _imp->opb << "1 " << gevar << " >= 1 ;\n";
            ++_imp->model_constraints;
        }
    }

    // upper?
    if (bounds != _imp->bounds_for_gevars.end() && bounds->second.second < v) {
        if (_imp->opb_done) {
            _imp->proof << "u 1 ~" << gevar << " >= 1 ;\n";
            ++_imp->proof_line;
        }
        else {
            _imp->opb << "1 ~" << gevar << " >= 1 ;\n";
            ++_imp->model_constraints;
        }
    }

    auto & other_gevars = _imp->gevars_that_exist.at(id);
    auto this_gevar = other_gevars.find(v);
    auto higher_gevar = next(this_gevar);

    // implied by the next highest gevar, if there is one?
    if (higher_gevar != other_gevars.end()) {
        auto implies_higher = implies(opb_var_as_sum(proof_name(id >= *higher_gevar)), proof_name(id >= v));
        if (_imp->opb_done) {
            _imp->proof << "u " << implies_higher << " ;\n";
            ++_imp->proof_line;
        }
        else {
            _imp->opb << implies_higher << " ;\n";
            ++_imp->model_constraints;
        }
    }

    // implies the next lowest gevar, if there is one?
    if (this_gevar != other_gevars.begin()) {
        auto implies_lower = implies(opb_var_as_sum(proof_name(id >= v)), proof_name(id >= *prev(this_gevar)));
        if (_imp->opb_done) {
            _imp->proof << "u " << implies_lower << " ;\n";
            ++_imp->proof_line;
        }
        else {
            _imp->opb << implies_lower << " ;\n";
            ++_imp->model_constraints;
        }
    }

    if (_imp->opb_done)
        _imp->proof << "# " << _imp->active_proof_level << "\n";
}

auto Proof::need_direct_encoding_for(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> void
{
    using namespace gcs::innards::opb_utils;

    if (_imp->direct_integer_variables.contains(id == v))
        return;

    string name = overloaded{
        [&](const SimpleIntegerVariableID & id) { return "iv" + to_string(id.index); },
        [&](const ProofOnlySimpleIntegerVariableID & id) { return "poiv" + to_string(id.index); }}
                      .visit(id);

    auto eqvar = xify(name + "_eq_" + value_name(v));
    _imp->direct_integer_variables.emplace(id == v, eqvar);
    _imp->direct_integer_variables.emplace(id != v, "~" + eqvar);

    auto bounds = _imp->bounds_for_gevars.find(id);
    if (bounds != _imp->bounds_for_gevars.end() && bounds->second.first == v) {
        // it's a lower bound
        need_gevar(id, v + 1_i);

        if (_imp->opb_done)
            _imp->proof << "* need lower bound " << eqvar << '\n';
        else
            _imp->opb << "* need lower bound " << eqvar << '\n';

        if (_imp->opb_done)
            _imp->proof << "# 0\n";

        auto not_ge_v_plus_one = opb_sum({pair{1_i, negate_opb_var_name(proof_name(id >= v + 1_i))}}) >= 1_i;

        // eqvar -> ! ge_v+1
        auto eqvar_true = implied_by(not_ge_v_plus_one, eqvar);

        // ge_v+1 -> eqvar
        auto eqvar_false = implies(not_ge_v_plus_one, eqvar);

        if (_imp->opb_done) {
            _imp->proof << "red " << eqvar_true << " ; " << eqvar << " 0\n";
            ++_imp->proof_line;
            _imp->proof << "red " << eqvar_false << " ; " << eqvar << " 1\n";
            ++_imp->proof_line;
        }
        else {
            _imp->opb << eqvar_true << " ;\n";
            _imp->opb << eqvar_false << " ;\n";
            _imp->model_constraints += 2;
            ++_imp->model_variables;
        }

        if (_imp->opb_done)
            _imp->proof << "# " << _imp->active_proof_level << "\n";
    }
    else if (bounds != _imp->bounds_for_gevars.end() && bounds->second.second == v) {
        // it's an upper bound
        need_gevar(id, v);

        if (_imp->opb_done)
            _imp->proof << "* need upper bound " << eqvar << '\n';
        else
            _imp->opb << "* need upper bound " << eqvar << '\n';

        if (_imp->opb_done)
            _imp->proof << "# 0\n";

        auto ge_v = opb_sum({pair{1_i, proof_name(id >= v)}}) >= 1_i;

        // eqvar -> ge_v
        auto eqvar_true = implied_by(ge_v, eqvar);

        // ge_v -> eqvar
        auto eqvar_false = implies(ge_v, eqvar);

        if (_imp->opb_done) {
            _imp->proof << "red " << eqvar_true << " ; " << eqvar << " 0\n";
            ++_imp->proof_line;
            _imp->proof << "red " << eqvar_false << " ; " << eqvar << " 1\n";
            ++_imp->proof_line;
        }
        else {
            _imp->opb << eqvar_true << " ;\n";
            _imp->opb << eqvar_false << " ;\n";
            _imp->model_constraints += 2;
            ++_imp->model_variables;
        }

        if (_imp->opb_done)
            _imp->proof << "# " << _imp->active_proof_level << "\n";
    }
    else {
        // neither a lower nor an upper bound
        need_gevar(id, v);
        need_gevar(id, v + 1_i);

        if (_imp->opb_done)
            _imp->proof << "* need " << eqvar << '\n';
        else
            _imp->opb << "* need " << eqvar << '\n';

        if (_imp->opb_done)
            _imp->proof << "# 0\n";

        auto ge_v_but_not_v_plus_one = opb_sum({pair{1_i, proof_name(id >= v)},
                                           pair{1_i, negate_opb_var_name(proof_name(id >= v + 1_i))}}) >= 2_i;

        // eqvar -> ge_v && ! ge_v+1
        auto eqvar_true = implied_by(ge_v_but_not_v_plus_one, eqvar);

        // ge_v && ! ge_v+1 -> eqvar
        auto eqvar_false = implies(ge_v_but_not_v_plus_one, eqvar);

        if (_imp->opb_done) {
            _imp->proof << "red " << eqvar_true << " ; " << eqvar << " 0\n";
            ++_imp->proof_line;
            _imp->proof << "red " << eqvar_false << " ; " << eqvar << " 1\n";
            ++_imp->proof_line;
        }
        else {
            _imp->opb << eqvar_true << " ;\n";
            _imp->opb << eqvar_false << " ;\n";
            _imp->model_constraints += 2;
            ++_imp->model_variables;
        }

        if (_imp->opb_done)
            _imp->proof << "# " << _imp->active_proof_level << "\n";
    }
}

auto Proof::create_literals_for_introduced_variable_value(
    SimpleIntegerVariableID id, Integer val, const optional<string> & optional_name) -> void
{
    string name = "iv" + to_string(id.index);
    if (optional_name)
        name.append("_" + *optional_name);

    auto x = xify(name + "_eq_" + value_name(val));
    _imp->direct_integer_variables.emplace(id == val, x);
    _imp->direct_integer_variables.emplace(id != val, "~" + x);
}

auto Proof::start_proof(State & state) -> void
{
    ofstream full_opb{_imp->opb_file};
    full_opb << "* #variable= " << _imp->model_variables << " #constraint= " << _imp->model_constraints << '\n';

    if (state.optional_minimise_variable()) {
        full_opb << "min: ";
        overloaded{
            [&](const SimpleIntegerVariableID & v) {
                for (auto & [bit_value, bit_name] : _imp->integer_variable_bits.at(v).second)
                    full_opb << bit_value << " " << bit_name << " ";
            },
            [&](const ConstantIntegerVariableID &) {
                throw UnimplementedException{};
            },
            [&](const ViewOfIntegerVariableID & v) {
                // the "then add" bit is irrelevant for the objective function
                for (auto & [bit_value, bit_name] : _imp->integer_variable_bits.at(v.actual_variable).second)
                    full_opb << (v.negate_first ? -bit_value : bit_value) << " " << bit_name << " ";
            }}
            .visit(*state.optional_minimise_variable());

        full_opb << " ;\n";
    }

    copy(istreambuf_iterator<char>{_imp->opb}, istreambuf_iterator<char>{}, ostreambuf_iterator<char>{full_opb});
    _imp->opb = stringstream{};
    _imp->opb_done = true;

    if (! full_opb)
        throw ProofError{"Error writing opb file to '" + _imp->opb_file + "'"};
    full_opb.close();

    _imp->proof.open(_imp->proof_file, ios::out);

    _imp->proof << "pseudo-Boolean proof version 1.2\n";

    _imp->proof << "f " << _imp->model_constraints << " 0\n";
    _imp->proof_line += _imp->model_constraints;

    if (! _imp->proof)
        throw ProofError{"Error writing proof file to '" + _imp->proof_file + "'"};
}

auto Proof::proof_name(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) const -> const string &
{
    auto it = _imp->direct_integer_variables.find(cond);
    if (it == _imp->direct_integer_variables.end())
        throw ProofError("No variable exists for condition on " + visit([&](const auto & var) { return debug_string(var); }, cond.var));
    return it->second;
}

auto Proof::proof_name(const ProofFlag & flag) const -> const string &
{
    auto it = _imp->flags.find(pair{flag.index, flag.positive});
    if (it == _imp->flags.end())
        throw ProofError("Missing flag");
    return it->second;
}

auto Proof::simplify_literal(const ProofLiteral & lit) -> SimpleLiteral
{
    return overloaded{
        [&](const TrueLiteral & t) -> SimpleLiteral { return t; },
        [&](const FalseLiteral & f) -> SimpleLiteral { return f; },
        [&](const IntegerVariableCondition & lit) -> SimpleLiteral {
            return overloaded{
                [&](const SimpleIntegerVariableID & var) -> SimpleLiteral {
                    return VariableConditionFrom<SimpleIntegerVariableID>{var, lit.op, lit.value};
                },
                [&](const ViewOfIntegerVariableID & view) -> SimpleLiteral {
                    switch (lit.op) {
                    case VariableConditionOperator::NotEqual:
                        return VariableConditionFrom<SimpleIntegerVariableID>{view.actual_variable, VariableConditionOperator::NotEqual,
                            (view.negate_first ? -lit.value + view.then_add : lit.value - view.then_add)};
                        break;
                    case VariableConditionOperator::Equal:
                        return VariableConditionFrom<SimpleIntegerVariableID>{view.actual_variable, VariableConditionOperator::Equal,
                            view.negate_first ? -lit.value + view.then_add : lit.value - view.then_add};
                        break;
                    case VariableConditionOperator::Less:
                        if (view.negate_first)
                            return VariableConditionFrom<SimpleIntegerVariableID>{view.actual_variable, VariableConditionOperator::GreaterEqual,
                                lit.value - view.then_add + 1_i};
                        else
                            return VariableConditionFrom<SimpleIntegerVariableID>{view.actual_variable, VariableConditionOperator::Less,
                                (lit.value - view.then_add)};
                        break;
                    case VariableConditionOperator::GreaterEqual:
                        if (view.negate_first)
                            return VariableConditionFrom<SimpleIntegerVariableID>{view.actual_variable, VariableConditionOperator::Less,
                                lit.value - view.then_add + 1_i};
                        else
                            return VariableConditionFrom<SimpleIntegerVariableID>{view.actual_variable, VariableConditionOperator::GreaterEqual,
                                lit.value - view.then_add};
                        break;
                    }
                    throw NonExhaustiveSwitch{};
                },
                [&](const ConstantIntegerVariableID &) -> SimpleLiteral {
                    throw UnimplementedException{};
                }}
                .visit(lit.var);
        },
        [&](const ProofVariableCondition & cond) -> SimpleLiteral {
            return VariableConditionFrom<ProofOnlySimpleIntegerVariableID>{cond.var, cond.op, cond.value};
        }}
        .visit(flatten(lit));
}

auto Proof::need_proof_name(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) -> void
{
    switch (cond.op) {
    case VariableConditionOperator::Equal:
    case VariableConditionOperator::NotEqual:
        need_direct_encoding_for(cond.var, cond.value);
        break;
    case VariableConditionOperator::Less:
    case VariableConditionOperator::GreaterEqual:
        need_gevar(cond.var, cond.value);
        break;
    }
}

auto Proof::add_cnf_to_model(const Literals & lits) -> std::optional<ProofLine>
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

    return add_to_model(move(sum) >= 1_i, nullopt);
}

auto Proof::add_to_model(const WeightedPseudoBooleanLessEqual & ineq, optional<ReificationTerm> half_reif) -> optional<ProofLine>
{
    if (_imp->opb_done)
        throw UnexpectedException{"proof has already started"};

    need_all_proof_names_in(ineq.lhs);
    if (half_reif)
        overloaded{
            [&](const ProofFlag &) {},
            [&](const ProofLiteral & lit) {
                overloaded{
                    [&](const TrueLiteral &) {},
                    [&](const FalseLiteral &) {},
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) { need_proof_name(cond); }}
                    .visit(simplify_literal(lit));
            }}
            .visit(*half_reif);

    emit_inequality_to(ineq, half_reif, _imp->opb);
    _imp->opb << '\n';
    return ++_imp->model_constraints;
}

auto Proof::add_to_model(const WeightedPseudoBooleanEquality & eq, optional<ReificationTerm> half_reif) -> pair<optional<ProofLine>, optional<ProofLine>>
{
    if (_imp->opb_done)
        throw UnexpectedException{"proof has already started"};

    need_all_proof_names_in(eq.lhs);
    if (half_reif)
        overloaded{
            [&](const ProofFlag &) {},
            [&](const ProofLiteral & lit) {
                overloaded{
                    [&](const TrueLiteral &) {},
                    [&](const FalseLiteral &) {},
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) { need_proof_name(cond); }}
                    .visit(simplify_literal(lit));
            }}
            .visit(*half_reif);

    emit_inequality_to(eq.lhs <= eq.rhs, half_reif, _imp->opb);
    _imp->opb << '\n';
    auto first = ++_imp->model_constraints;

    emit_inequality_to(eq.lhs >= eq.rhs, half_reif, _imp->opb);
    _imp->opb << '\n';
    auto second = ++_imp->model_constraints;

    return pair{first, second};
}

auto Proof::posting(const std::string & s) -> void
{
    if (_imp->opb_done)
        throw UnexpectedException{"proof has already started"};
    _imp->opb << "* constraint " << s << '\n';
}

auto Proof::solution(const State & state) -> void
{
    _imp->proof << "* solution\n";

    for (auto & var : _imp->solution_variables)
        need_proof_name(var == state(var));

    if (auto obj = state.optional_minimise_variable()) {
        Integer obj_val = state(*obj);
        overloaded{
            [&](const ConstantIntegerVariableID &) {
            },
            [&](const SimpleIntegerVariableID & var) {
                need_proof_name(var == obj_val);
                need_proof_name(var < obj_val);
            },
            [&](const ViewOfIntegerVariableID & var) {
                need_proof_name(deview(var == obj_val));
                need_proof_name(deview(var < obj_val));
            }}
            .visit(*obj);
    }

    _imp->proof << "# 0\n";

    _imp->proof << (state.optional_minimise_variable() ? "o" : "v");

    for (auto & var : _imp->solution_variables)
        if ((! state.optional_minimise_variable()) || (IntegerVariableID{var} != *state.optional_minimise_variable()))
            _imp->proof << " " << proof_name(var == state(var));

    if (! state.optional_minimise_variable()) {
        _imp->proof << '\n';
        ++_imp->proof_line;
    }
    else {
        auto do_it = [&](const SimpleIntegerVariableID & var, Integer val) {
            _imp->proof << " " << proof_name(var == val);

            auto & [negative_bit_coeff, bit_vars] = _imp->integer_variable_bits.at(var);
            if (val.raw_value < 0) {
                for (auto & [coeff, var] : bit_vars) {
                    if (coeff < 0_i)
                        _imp->proof << " " << var;
                    else
                        _imp->proof << " " << (((val + negative_bit_coeff).raw_value & coeff.raw_value) ? "" : "~") << var;
                }
            }
            else {
                for (auto & [coeff, var] : bit_vars) {
                    if (coeff < 0_i)
                        _imp->proof << " ~" << var;
                    else
                        _imp->proof << " " << ((val.raw_value & coeff.raw_value) ? "" : "~") << var;
                }
            }

            _imp->proof << '\n';
            ++_imp->proof_line;
        };

        overloaded{
            [&](const SimpleIntegerVariableID & var) {
                Integer obj_val = state(*state.optional_minimise_variable());
                do_it(var, obj_val);
                need_proof_name(var < obj_val);
                _imp->proof << "# 0\n";
                _imp->proof << "u 1 " << proof_name(var < obj_val) << " >= 1 ;\n";
                ++_imp->proof_line;
            },
            [&](const ConstantIntegerVariableID &) {
                throw UnimplementedException{};
            },
            [&](const ViewOfIntegerVariableID & var) {
                Integer obj_val = state(var.actual_variable);
                do_it(var.actual_variable, obj_val);
                auto lit = deview(var < state(var));
                need_proof_name(lit);
                _imp->proof << "# 0\n";
                _imp->proof << "u 1 " << proof_name(lit) << " >= 1 ;\n";
                ++_imp->proof_line;
            }}
            .visit(*state.optional_minimise_variable());
    }

    _imp->proof << "# " << _imp->active_proof_level << "\n";
}

auto Proof::backtrack(const State & state) -> void
{
    _imp->proof << "* backtracking\n";
    WeightedPseudoBooleanSum backtrack;
    state.for_each_guess([&](const Literal & lit) {
        backtrack += 1_i * ! lit;
    });
    emit_rup_proof_line(move(backtrack) >= 1_i);
}

auto Proof::assert_contradiction() -> void
{
    _imp->proof << "* asserting contradiction\n";
    _imp->proof << "u >= 1 ;\n";
    ++_imp->proof_line;
    _imp->proof << "c " << _imp->proof_line << " 0\n";

    // this is mostly for tests: we haven't necessarily destroyed the
    // Problem before running the verifier.
    _imp->proof << flush;
}

auto Proof::infer(const State & state, const Literal & lit, const Justification & why) -> void
{
    auto output_it = [&](const string & rule) {
        if (! is_literally_true(lit)) {
            auto terms = trail_variables_as_sum(state, 1_i);
            terms += 1_i * lit;
            _imp->proof << rule << " ";
            emit_inequality_to(move(terms) >= 1_i, nullopt, _imp->proof);
            _imp->proof << '\n';
            ++_imp->proof_line;
        }
    };

    auto need_lit = [&]() {
        overloaded{
            [&](const TrueLiteral &) {},
            [&](const FalseLiteral &) {},
            [&]<typename T_>(const VariableConditionFrom<T_> & cond) { need_proof_name(cond); }}
            .visit(simplify_literal(lit));
    };

    overloaded{
        [&]([[maybe_unused]] const JustifyUsingRUP & j) {
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            _imp->proof << "* RUP from " << j.where.file_name() << ":"
                        << j.where.line() << " in " << j.where.function_name() << '\n';
#endif
            need_lit();
            output_it("u");
        },
        [&](const JustifyUsingAssertion &) {
            need_lit();
            output_it("a");
        },
        [&](const JustifyExplicitly & x) {
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            _imp->proof << "* explicit from " << x.where.file_name() << ":"
                        << x.where.line() << " in " << x.where.function_name() << '\n';
#endif
            need_lit();
            vector<ProofLine> to_delete;
            add_proof_steps(x, to_delete);
            infer(state, lit, JustifyUsingRUP{});
            delete_proof_lines(to_delete);
        },
        [&](const Guess &) {
            need_lit();
            if (! is_literally_true(lit)) {
                // we need this because it'll show up in the trail later
                _imp->proof << "* guessing " << debug_string(lit) << ", decision stack is [";
                state.for_each_guess([&](const Literal & lit) {
                    _imp->proof << " " << debug_string(lit);
                });
                _imp->proof << " ]\n";
            }
        },
        [&](const NoJustificationNeeded &) {
        }}
        .visit(why);
}

auto Proof::emit_proof_line(const string & s) -> ProofLine
{
    _imp->proof << s << '\n';
    return ++_imp->proof_line;
}

auto Proof::emit_proof_comment(const string & s) -> void
{
    _imp->proof << "* " << s << '\n';
}

auto Proof::need_all_proof_names_in(const SumOf<Weighted<PseudoBooleanTerm>> & sum) -> void
{
    // make sure we have any definitions for things that show up
    for (auto & [_, v] : sum.terms)
        overloaded{
            [&](const ProofLiteral & lit) {
                overloaded{
                    [&](const TrueLiteral &) {},
                    [&](const FalseLiteral &) {},
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) {
                        need_proof_name(cond);
                    }}
                    .visit(simplify_literal(lit));
            },
            [&](const ProofFlag &) {},
            [&](const IntegerVariableID &) {},
            [&](const ProofOnlySimpleIntegerVariableID &) {}}
            .visit(v);
}

auto Proof::emit_inequality_to(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
    const optional<ReificationTerm> & half_reif, ostream & stream) -> void
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
                        stream << -w << " " << proof_name(cond) << " ";
                        reif_const += max(0_i, w);
                    }}
                    .visit(simplify_literal(lit));
            },
            [&, w = w](const ProofFlag & flag) {
                stream << -w << " " << proof_name(flag) << " ";
                reif_const += max(0_i, w);
            },
            [&, w = w](const IntegerVariableID & var) {
                overloaded{
                    [&](const SimpleIntegerVariableID & var) {
                        auto & [_, bit_vars] = _imp->integer_variable_bits.at(var);
                        for (auto & [bit_value, bit_name] : bit_vars) {
                            stream << -w * bit_value << " " << bit_name << " ";
                            reif_const += max(0_i, w * bit_value);
                        }
                    },
                    [&](const ViewOfIntegerVariableID & view) {
                        if (! view.negate_first) {
                            auto & [_, bit_vars] = _imp->integer_variable_bits.at(view.actual_variable);
                            for (auto & [bit_value, bit_name] : bit_vars) {
                                stream << -w * bit_value << " " << bit_name << " ";
                                reif_const += max(0_i, w * bit_value);
                            }
                            rhs += w * view.then_add;
                            reif_const += max(0_i, -w * view.then_add);
                        }
                        else {
                            auto & [_, bit_vars] = _imp->integer_variable_bits.at(view.actual_variable);
                            for (auto & [bit_value, bit_name] : bit_vars) {
                                stream << w * bit_value << " " << bit_name << " ";
                                reif_const += max(0_i, -w * bit_value);
                            }
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
                auto & [_, bit_vars] = _imp->integer_variable_bits.at(var);
                for (auto & [bit_value, bit_name] : bit_vars) {
                    stream << -w * bit_value << " " << bit_name << " ";
                    reif_const += max(0_i, w * bit_value);
                }
            }}
            .visit(v);
    }

    if (half_reif) {
        reif_const += rhs;
        overloaded{
            [&](const ProofFlag & f) {
                stream << reif_const << " " << proof_name(! f) << " ";
            },
            [&](const ProofLiteral & lit) {
                overloaded{
                    [&](const TrueLiteral &) {
                    },
                    [&](const FalseLiteral &) {
                        throw UnimplementedException{};
                    },
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) {
                        stream << reif_const << " " << proof_name(! cond) << " ";
                    }}
                    .visit(simplify_literal(lit));
            }}
            .visit(*half_reif);
    }

    stream << ">= " << rhs << " ;";
}

auto Proof::emit_rup_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq) -> ProofLine
{
    need_all_proof_names_in(ineq.lhs);

    _imp->proof << "u ";
    emit_inequality_to(ineq, nullopt, _imp->proof);
    _imp->proof << '\n';
    return ++_imp->proof_line;
}

auto Proof::emit_rup_proof_line_under_trail(const State & state, const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq) -> ProofLine
{
    auto terms = trail_variables_as_sum(state, ineq.rhs);
    for (auto & t : ineq.lhs.terms)
        terms += t;
    return emit_rup_proof_line(terms <= ineq.rhs);
}

auto Proof::emit_red_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
    const std::vector<std::pair<ProofLiteral, ProofLiteral>> & witness) -> ProofLine
{
    need_all_proof_names_in(ineq.lhs);

    _imp->proof << "red ";
    emit_inequality_to(ineq, nullopt, _imp->proof);

    auto witness_literal = [this](const ProofLiteral & lit) -> string {
        return overloaded{
            [](const TrueLiteral &) -> string { return "1"; },
            [](const FalseLiteral &) -> string { return "0"; },
            [this]<typename T_>(const VariableConditionFrom<T_> & var) -> string { return proof_name(var); }}
            .visit(simplify_literal(lit));
    };

    for (auto & [f, t] : witness)
        _imp->proof << " " << witness_literal(f) << " -> " << witness_literal(t);
    _imp->proof << " ;\n";

    return ++_imp->proof_line;
}

auto Proof::need_constraint_saying_variable_takes_at_least_one_value(IntegerVariableID var) -> ProofLine
{
    return overloaded{
        [&](const ConstantIntegerVariableID &) -> ProofLine {
            throw UnimplementedException{};
        },
        [&](const SimpleIntegerVariableID & var) -> ProofLine {
            auto result = _imp->variable_at_least_one_constraints.find(var);
            if (result == _imp->variable_at_least_one_constraints.end()) {
                auto [lower, upper] = _imp->bounds_for_gevars.at(var);
                for (Integer v = lower; v <= upper; ++v)
                    need_proof_name(var == v);

                _imp->proof << "# 0\n";

                _imp->proof << "u ";
                for (Integer v = lower; v <= upper; ++v)
                    _imp->proof << "1 " << proof_name(var == v) << " ";

                _imp->proof << ">= 1 ;\n";
                _imp->variable_at_least_one_constraints.emplace(var, ++_imp->proof_line);

                _imp->proof << "# " << _imp->active_proof_level << "\n";
                result = _imp->variable_at_least_one_constraints.emplace(var, _imp->proof_line).first;
            }
            return result->second;
        },
        [&](const ViewOfIntegerVariableID & var) -> ProofLine {
            return need_constraint_saying_variable_takes_at_least_one_value(var.actual_variable);
        }}
        .visit(var);
}

auto Proof::enter_proof_level(int depth) -> void
{
    _imp->proof << "# " << depth << '\n';
    _imp->active_proof_level = depth;
}

auto Proof::forget_proof_level(int depth) -> void
{
    _imp->proof << "w " << depth << '\n';
}

auto Proof::trail_variables_as_sum(const State & state, Integer coeff) -> WeightedPseudoBooleanSum
{
    WeightedPseudoBooleanSum result;
    state.for_each_guess([&](const Literal & lit) {
        if (! is_literally_true(lit))
            result += coeff * ! lit;
    });

    return result;
}

auto Proof::add_proof_steps(const JustifyExplicitly & x, vector<ProofLine> & to_delete) -> void
{
    x.add_proof_steps(*this, to_delete);
}

auto Proof::delete_proof_lines(const vector<ProofLine> & to_delete) -> void
{
    if (! to_delete.empty()) {
        stringstream line;
        line << "d";
        for (const auto & l : to_delete)
            line << " " << l;
        _imp->proof << line.str() << '\n';
    }
}

auto Proof::has_bit_representation(const SimpleIntegerVariableID & var) const -> bool
{
    return _imp->integer_variable_bits.contains(var);
}

auto Proof::get_or_emit_pol_term_for_bound_in_bits(State & state, bool upper,
    const SimpleIntegerVariableID & var, Integer val) -> variant<ProofLine, string>
{
    if (! has_bit_representation(var))
        throw UnexpectedException{"variable does not have a bit representation"};

    auto it = _imp->line_for_bound_in_bits.back().find(tuple{upper, var, val});
    if (it != _imp->line_for_bound_in_bits.back().end())
        return it->second;

    stringstream step;
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    step << "* need line for bound in bits " << (upper ? debug_string(var < val + 1_i) : debug_string(var >= val)) << "\n";
#endif
    step << "u";
    Integer big_number = 0_i;

    auto & [_, bit_vars] = _imp->integer_variable_bits.at(var);
    for (auto & [bit_coeff, bit_name] : bit_vars) {
        step << " " << (upper ? -bit_coeff : bit_coeff) << " " << bit_name;
        big_number += Integer{abs(bit_coeff)};
    }

    big_number += max(1_i, abs(val));
    state.for_each_guess([&](const Literal & lit) {
        overloaded{
            [&](const TrueLiteral &) {},
            [&](const FalseLiteral &) { throw UnimplementedException{}; },
            [&]<typename T_>(const VariableConditionFrom<T_> & cond) { step << " " << big_number << " " << proof_name(! cond); }}
            .visit(simplify_literal(lit));
    });

    if (upper)
        step << " >= " << -val << " ";
    else
        step << " >= " << val << " ";

    step << ";";

    auto line = emit_proof_line(step.str());
    _imp->line_for_bound_in_bits.back().emplace(tuple{upper, var, val}, line);
    return line;
}

auto Proof::new_guess() -> void
{
    _imp->line_for_bound_in_bits.emplace_back(_imp->line_for_bound_in_bits.back());
}

auto Proof::undo_guess() -> void
{
    _imp->line_for_bound_in_bits.pop_back();
}

auto gcs::innards::debug_string(const ProofOnlySimpleIntegerVariableID & var) -> string
{
    return "proofvaridx " + to_string(var.index);
}
