/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/exception.hh>
#include <gcs/innards/literal_utils.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/state.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <bit>
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

using std::bit_ceil;
using std::copy;
using std::countr_zero;
using std::flush;
using std::fstream;
using std::ios;
using std::istreambuf_iterator;
using std::list;
using std::map;
using std::max;
using std::nullopt;
using std::ofstream;
using std::optional;
using std::ostreambuf_iterator;
using std::pair;
using std::set;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unordered_map;
using std::vector;
using std::visit;

namespace
{
    auto value_name(Integer v) -> string
    {
        return to_string(v.raw_value);
    }
}

auto gcs::innards::sanitise_literals(Literals & lits) -> bool
{
    // if we've got a literal that is definitely true, the clause is always satisfied,
    // so we can discard the clause
    if (lits.end() != find_if(lits.begin(), lits.end(), [](const Literal & lit) -> bool { return is_literally_true(lit); }))
        return false;

    // remove any literals that are definitely false. this might remove everything, in
    // which case we get the empty clause which is false so it's fine.
    lits.erase(remove_if(lits.begin(), lits.end(), [&](const Literal & lit) -> bool { return is_literally_false(lit); }), lits.end());

    // put these in some kind of order
    sort(lits.begin(), lits.end());

    // remove duplicates
    lits.erase(unique(lits.begin(), lits.end()), lits.end());

    return true;
}

namespace
{
    [[nodiscard]] auto is_literally_true_or_false(const ProofFlag &) -> optional<bool>
    {
        return nullopt;
    }

    [[nodiscard]] auto is_literally_true_or_false(const IntegerVariableID &) -> optional<bool>
    {
        return nullopt;
    }
}

auto gcs::innards::sanitise_pseudoboolean_terms(WeightedPseudoBooleanTerms & lits, Integer & val) -> bool
{
    using ::is_literally_true_or_false; // because C++

    // adjust coefficients down for true and false literals
    for (const auto & l : lits) {
        auto t_or_f = visit([&](const auto & t) { return is_literally_true_or_false(t); }, l.second);
        if (t_or_f && *t_or_f)
            val -= l.first;
        else if (t_or_f && ! *t_or_f)
            val += l.first;
    }

    // now actually remove true and false literals
    lits.erase(remove_if(lits.begin(), lits.end(), [&](const auto & wlit) -> bool {
        return nullopt != visit([&](const auto & t) { return is_literally_true_or_false(t); }, wlit.second);
    }),
        lits.end());

    return true;
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

    map<SimpleIntegerVariableID, ProofLine> variable_at_least_one_constraints;
    map<LiteralFromIntegerVariable, string> direct_integer_variables;
    map<SimpleIntegerVariableID, pair<Integer, vector<pair<Integer, string>>>> integer_variable_bits;
    map<SimpleIntegerVariableID, pair<Integer, Integer>> bounds_for_gevars;
    map<SimpleIntegerVariableID, set<Integer>> gevars_that_exist;
    list<IntegerVariableID> solution_variables;
    optional<IntegerVariableID> objective_variable;
    map<pair<unsigned long long, bool>, string> flags;

    list<map<tuple<bool, SimpleIntegerVariableID, Integer>, ProofLine>> line_for_bound_in_bits;

    string opb_file, proof_file;
    stringstream opb;
    fstream proof;
    bool opb_done = false;

    bool use_friendly_names;
    unordered_map<string, string> xification;
};

Proof::Proof(const ProofOptions & proof_options) :
    _imp(new Imp)
{
    _imp->opb_file = proof_options.opb_file;
    _imp->proof_file = proof_options.proof_file;
    _imp->use_friendly_names = proof_options.use_friendly_names;
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

auto Proof::create_integer_variable(SimpleIntegerVariableID id, Integer lower, Integer upper, const optional<string> & optional_name) -> void
{
    string name = "iv" + to_string(id.index);
    if (optional_name)
        name.append("_" + *optional_name);

    _imp->opb << "* variable " << name << " " << lower.raw_value << " .. " << upper.raw_value << " binary encoding\n";
    Integer highest_abs_value = max(abs(lower), upper);
    int highest_bit_shift = countr_zero(bit_ceil(static_cast<unsigned long long>(highest_abs_value.raw_value)));
    Integer highest_bit_coeff = Integer{1ll << highest_bit_shift};

    auto negative_bit_coeff = lower < 0_i ? (-highest_bit_coeff * 2_i) : 0_i;
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

    // upper bound
    for (auto & [coeff, var] : bit_vars)
        _imp->opb << -coeff << " " << var << " ";
    _imp->opb << ">= " << -upper << " ;\n";
    ++_imp->model_constraints;

    _imp->solution_variables.push_back(id);
    _imp->bounds_for_gevars.emplace(id, pair{lower, upper});
}

auto Proof::create_proof_flag(const string & n) -> ProofFlag
{
    ProofFlag result{_imp->flags.size() / 2, true};

    string name = xify("flag" + to_string(result.index) + "_" + n);
    _imp->flags.emplace(pair{result.index, true}, name);
    _imp->flags.emplace(pair{result.index, false}, "~" + name);
    return result;
}

auto Proof::need_gevar(SimpleIntegerVariableID id, Integer v) -> void
{
    if (_imp->direct_integer_variables.contains(id >= v))
        return;

    string name = "iv" + to_string(id.index);
    auto gevar = xify(name + "_ge_" + value_name(v));
    _imp->direct_integer_variables.emplace(id >= v, gevar);
    _imp->direct_integer_variables.emplace(id < v, "~" + gevar);
    _imp->gevars_that_exist[id].insert(v);

    auto & [_, bit_vars] = _imp->integer_variable_bits.find(id)->second;

    if (_imp->opb_done) {
        _imp->proof << "# 0\n";

        // gevar -> bits
        _imp->proof << "red ";
        for (auto & [coeff, var] : bit_vars)
            _imp->proof << coeff << " " << var << " ";
        _imp->proof << ">= " << v << " <== " << gevar << " ; " << gevar << " 0\n";
        ++_imp->proof_line;

        // !gevar -> bits
        _imp->proof << "red ";
        for (auto & [coeff, var] : bit_vars)
            _imp->proof << -coeff << " " << var << " ";
        _imp->proof << ">= " << (-v + 1_i) << " <== ~" << gevar << " ; " << gevar << " 1\n";
        ++_imp->proof_line;

        // is it a lower bound?
        auto bounds = _imp->bounds_for_gevars.find(id);
        if (bounds != _imp->bounds_for_gevars.end() && bounds->second.first == v) {
            _imp->proof << "u 1 " << gevar << " >= 1 ;\n";
            ++_imp->proof_line;
        }

        // is it an lower bound?
        if (bounds != _imp->bounds_for_gevars.end() && bounds->second.second < v) {
            _imp->proof << "u 1 ~" << gevar << " >= 1 ;\n";
            ++_imp->proof_line;
        }

        auto & other_gevars = _imp->gevars_that_exist.find(id)->second;
        auto this_gevar = other_gevars.find(v);
        auto higher_gevar = next(this_gevar);

        // implied by the next highest gevar, if there is one
        if (higher_gevar != other_gevars.end()) {
            _imp->proof << "u 1 " << proof_variable(id >= *higher_gevar) << " >= 1 ==> " << proof_variable(id >= v) << " ;\n";
            ++_imp->proof_line;
        }

        // implies the next lowest gevar, if there is one
        if (this_gevar != other_gevars.begin()) {
            _imp->proof << "u 1 " << proof_variable(id >= v) << " >= 1 ==> " << proof_variable(id >= *prev(this_gevar)) << " ;\n";
            ++_imp->proof_line;
        }

        _imp->proof << "# " << _imp->active_proof_level << "\n";
    }
    else {
        // gevar -> bits
        for (auto & [coeff, var] : bit_vars)
            _imp->opb << coeff << " " << var << " ";
        _imp->opb << ">= " << v << " <== " << gevar << " ;\n";
        ++_imp->model_constraints;
        ++_imp->model_variables;

        // !gevar -> bits
        for (auto & [coeff, var] : bit_vars)
            _imp->opb << -coeff << " " << var << " ";
        _imp->opb << ">= " << (-v + 1_i) << " <== ~" << gevar << " ;\n";
        ++_imp->model_constraints;

        // is it a lower bound?
        auto bounds = _imp->bounds_for_gevars.find(id);
        if (bounds != _imp->bounds_for_gevars.end() && bounds->second.first == v) {
            _imp->opb << "1 " << gevar << " >= 1 ;\n";
            ++_imp->model_constraints;
        }

        // is it an upper bound?
        if (bounds != _imp->bounds_for_gevars.end() && bounds->second.second < v) {
            _imp->opb << "1 ~" << gevar << " >= 1 ;\n";
            ++_imp->model_constraints;
        }

        auto & other_gevars = _imp->gevars_that_exist.find(id)->second;
        auto this_gevar = other_gevars.find(v);
        auto higher_gevar = next(this_gevar);

        // implied by the next highest gevar, if there is one
        if (higher_gevar != other_gevars.end()) {
            _imp->opb << "1 " << proof_variable(id >= *higher_gevar) << " >= 1 ==> " << proof_variable(id >= v) << " ;\n";
            ++_imp->model_constraints;
        }

        // implies the next lowest gevar, if there is one
        if (this_gevar != other_gevars.begin()) {
            _imp->opb << "1 " << proof_variable(id >= v) << " >= 1 ==> " << proof_variable(id >= *prev(this_gevar)) << " ;\n";
            ++_imp->model_constraints;
        }
    }
}

auto Proof::need_direct_encoding_for(SimpleIntegerVariableID id, Integer v) -> void
{
    if (_imp->direct_integer_variables.contains(id == v))
        return;

    need_gevar(id, v);
    need_gevar(id, v + 1_i);

    string name = "iv" + to_string(id.index);
    auto eqvar = xify(name + "_eq_" + value_name(v));
    _imp->direct_integer_variables.emplace(id == v, eqvar);
    _imp->direct_integer_variables.emplace(id != v, "~" + eqvar);

    if (_imp->opb_done) {
        _imp->proof << "# 0\n";

        // eqvar -> ge_v && ! ge_v+1
        _imp->proof << "red 1 " << proof_variable(id >= v) << " 1 ~" << proof_variable(id >= v + 1_i)
                    << " >= 2 <== " << eqvar << " ; " << eqvar << " 0\n";
        ++_imp->proof_line;

        // ge_v && ! ge_v+1 -> eqvar
        _imp->proof << "red 1 " << proof_variable(id >= v) << " 1 ~" << proof_variable(id >= v + 1_i)
                    << " >= 1 ==> " << eqvar << " ; " << eqvar << " 1\n";
        ++_imp->proof_line;

        _imp->proof << "# " << _imp->active_proof_level << "\n";
    }
    else {
        ++_imp->model_variables;
        _imp->model_constraints += 2;

        // eqvar -> ge_v && ! ge_v+1
        _imp->opb << "1 " << proof_variable(id >= v) << " 1 ~" << proof_variable(id >= v + 1_i)
                  << " >= 2 <== " << eqvar << " ;\n";

        // ge_v && ! ge_v+1 -> eqvar
        _imp->opb << "1 " << proof_variable(id >= v) << " 1 ~" << proof_variable(id >= v + 1_i)
                  << " >= 1 ==> " << eqvar << " ;\n";
    }
}

auto Proof::create_pseudovariable(SimpleIntegerVariableID id, Integer lower, Integer upper, const optional<string> & optional_name) -> void
{
    string name = "iv" + to_string(id.index);
    if (optional_name)
        name.append("_" + *optional_name);

    for (Integer v = lower; v <= upper; ++v) {
        auto x = xify(name + "_eq_" + value_name(v));
        _imp->direct_integer_variables.emplace(id == v, x);
        _imp->direct_integer_variables.emplace(id != v, "~" + x);
    }
}

auto Proof::start_proof(State &) -> void
{
    ofstream full_opb{_imp->opb_file};
    full_opb << "* #variable= " << _imp->model_variables << " #constraint= " << _imp->model_constraints << '\n';

    if (_imp->objective_variable) {
        full_opb << "min: ";
        overloaded{
            [&](const SimpleIntegerVariableID & v) {
                for (auto & [bit_value, bit_name] : _imp->integer_variable_bits.find(v)->second.second)
                    full_opb << bit_value << " " << bit_name << " ";
            },
            [&](const ConstantIntegerVariableID &) {
                throw UnimplementedException{};
            },
            [&](const ViewOfIntegerVariableID & v) {
                // the "then add" bit is irrelevant for the objective function
                for (auto & [bit_value, bit_name] : _imp->integer_variable_bits.find(v.actual_variable)->second.second)
                    full_opb << (v.negate_first ? -bit_value : bit_value) << " " << bit_name << " ";
            }}
            .visit(*_imp->objective_variable);

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

auto Proof::cnf(const Literals & lits) -> ProofLine
{
    for (const auto & lit : lits)
        need_proof_variable(lit);

    for (const auto & lit : lits) {
        visit([&](const auto & lit) {
            _imp->opb << "1 " << proof_variable(lit) << " ";
        },
            lit);
    }
    _imp->opb << ">= 1 ;\n";
    return ++_imp->model_constraints;
}

auto Proof::at_most_one(const Literals & lits) -> ProofLine
{
    for (const auto & lit : lits)
        need_proof_variable(lit);

    for (const auto & lit : lits) {
        visit([&](const auto & lit) {
            _imp->opb << "-1 " << proof_variable(lit) << " ";
        },
            lit);
    }
    _imp->opb << ">= -1 ;\n";
    return ++_imp->model_constraints;
}

auto Proof::pseudoboolean_ge(const WeightedPseudoBooleanTerms & lits, Integer val) -> ProofLine
{
    for (const auto & [_, lit] : lits)
        overloaded{
            [&](const Literal & lit) { need_proof_variable(lit); },
            [&](const IntegerVariableID &) {},
            [&](const ProofFlag &) {}}
            .visit(lit);

    for (const auto & [w, lit] : lits) {
        overloaded{
            [&, w = w](const Literal & lit) {
                _imp->opb << w << " " << proof_variable(lit) << " ";
            },
            [&, w = w](const ProofFlag & flag) {
                _imp->opb << w << " " << proof_variable(flag) << " ";
            },
            [&, w = w](const IntegerVariableID & var) {
                overloaded{
                    [&](const SimpleIntegerVariableID & ivar) {
                        auto & [_, bit_vars] = _imp->integer_variable_bits.find(ivar)->second;
                        for (auto & [bit_value, bit_name] : bit_vars)
                            _imp->opb << w * bit_value << " " << bit_name << " ";
                    },
                    [&](const ConstantIntegerVariableID &) {
                        throw UnimplementedException{};
                    },
                    [&](const ViewOfIntegerVariableID &) {
                        throw UnimplementedException{};
                    }}
                    .visit(var);
            }}
            .visit(lit);
    }
    _imp->opb << ">= " << val << " ;\n";
    return ++_imp->model_constraints;
}

auto Proof::integer_linear_le(const State &, const SimpleLinear & lin, Integer val,
    optional<ReificationTerm> half_reif, bool equality) -> ProofLine
{
    if (half_reif)
        overloaded{
            [&](const Literal & lit) { need_proof_variable(lit); },
            [&](const IntegerVariableID &) {},
            [&](const ProofFlag &) {}}
            .visit(*half_reif);

    _imp->opb << (equality ? "* linear eq" : "* linear le");

    for (const auto & [coeff, var] : lin)
        _imp->opb << " " << coeff << "*" << debug_string(IntegerVariableID{var});
    _imp->opb << " <= " << val << '\n';

    auto output = [&](Integer multiplier) {
        Integer big_number = 0_i;
        for (const auto & [coeff, var] : lin)
            for (auto & [bit_value, bit_name] : _imp->integer_variable_bits.find(var)->second.second) {
                big_number += abs(multiplier * coeff * bit_value);
                _imp->opb << (multiplier * coeff * bit_value) << " " << bit_name << " ";
            }

        if (half_reif)
            visit([&](const auto & h) {
                _imp->opb << (big_number + 1_i) << " " << proof_variable(! h) << " ";
            },
                *half_reif);

        _imp->opb << ">= " << (multiplier * val) << " ;\n";
        ++_imp->model_constraints;
    };

    if (equality)
        output(1_i);
    output(-1_i);
    return _imp->model_constraints;
}

auto Proof::minimise(IntegerVariableID var) -> void
{
    _imp->objective_variable = var;
}

auto Proof::proof_variable(const Literal & lit) const -> const string &
{
    // This might need a design rethink: if we get a constant variable, turn it into either
    // true or false based upon its condition
    return overloaded{
        [&](const LiteralFromIntegerVariable & ilit) -> const string & {
            return overloaded{
                [&](const SimpleIntegerVariableID &) -> const string & {
                    auto it = _imp->direct_integer_variables.find(ilit);
                    if (it == _imp->direct_integer_variables.end())
                        throw ProofError("No variable exists for literal " + debug_string(lit));
                    return it->second;
                },
                [&](const ViewOfIntegerVariableID & view) -> const string & {
                    switch (ilit.op) {
                    case LiteralFromIntegerVariable::Operator::NotEqual:
                        return proof_variable(view.actual_variable != (view.negate_first ? -1_i : 1_i) * (ilit.value - view.then_add));
                    case LiteralFromIntegerVariable::Operator::Equal:
                        return proof_variable(view.actual_variable == (view.negate_first ? -1_i : 1_i) * (ilit.value - view.then_add));
                    case LiteralFromIntegerVariable::Operator::Less:
                        if (view.negate_first)
                            return proof_variable(view.actual_variable >= ilit.value - view.then_add + 1_i);
                        else
                            return proof_variable(view.actual_variable < (ilit.value - view.then_add));
                    case LiteralFromIntegerVariable::Operator::GreaterEqual:
                        if (view.negate_first)
                            return proof_variable(view.actual_variable < ilit.value - view.then_add + 1_i);
                        else
                            return proof_variable(view.actual_variable >= (ilit.value - view.then_add));
                    }
                    throw NonExhaustiveSwitch{};
                },
                [&](const ConstantIntegerVariableID &) -> const string & {
                    throw UnimplementedException{};
                }}
                .visit(ilit.var);
        },
        [&](const TrueLiteral &) -> const string & {
            throw UnimplementedException{};
        },
        [&](const FalseLiteral &) -> const string & {
            throw UnimplementedException{};
        }}
        .visit(lit);
}

auto Proof::proof_variable(const ProofFlag & flag) const -> const string &
{
    auto it = _imp->flags.find(pair{flag.index, flag.positive});
    if (it == _imp->flags.end())
        throw ProofError("Missing flag");
    return it->second;
}

auto Proof::need_proof_variable(const Literal & lit) -> void
{
    return overloaded{
        [&](const LiteralFromIntegerVariable & ilit) {
            return overloaded{
                [&](const SimpleIntegerVariableID & var) {
                    need_direct_encoding_for(var, ilit.value);
                },
                [&](const ViewOfIntegerVariableID & view) {
                    switch (ilit.op) {
                    case LiteralFromIntegerVariable::Operator::NotEqual:
                        need_proof_variable(view.actual_variable != (view.negate_first ? -1_i : 1_i) * (ilit.value - view.then_add));
                        break;
                    case LiteralFromIntegerVariable::Operator::Equal:
                        need_proof_variable(view.actual_variable == (view.negate_first ? -1_i : 1_i) * (ilit.value - view.then_add));
                        break;
                    case LiteralFromIntegerVariable::Operator::Less:
                        if (view.negate_first)
                            need_proof_variable(view.actual_variable >= ilit.value - view.then_add + 1_i);
                        else
                            need_proof_variable(view.actual_variable < (ilit.value - view.then_add));
                        break;
                    case LiteralFromIntegerVariable::Operator::GreaterEqual:
                        if (view.negate_first)
                            need_proof_variable(view.actual_variable < ilit.value - view.then_add + 1_i);
                        else
                            need_proof_variable(view.actual_variable >= (ilit.value - view.then_add));
                        break;
                    }
                },
                [&](const ConstantIntegerVariableID &) {
                    throw UnimplementedException{};
                }}
                .visit(ilit.var);
        },
        [&](const TrueLiteral &) {
        },
        [&](const FalseLiteral &) {
        }}
        .visit(lit);
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
        need_proof_variable(var == state(var));

    if (_imp->objective_variable) {
        Integer obj_val = state(*_imp->objective_variable);
        need_proof_variable(*_imp->objective_variable == obj_val);
        need_proof_variable(*_imp->objective_variable < obj_val);
    }

    _imp->proof << "# 0\n";

    _imp->proof << (_imp->objective_variable ? "o" : "v");

    for (auto & var : _imp->solution_variables)
        if ((! _imp->objective_variable) || (var != *_imp->objective_variable))
            _imp->proof << " " << proof_variable(var == state(var));

    if (! _imp->objective_variable) {
        _imp->proof << '\n';
        ++_imp->proof_line;
    }
    else {
        auto do_it = [&](const SimpleIntegerVariableID & var, Integer val) {
            _imp->proof << " " << proof_variable(var == val);

            auto & [negative_bit_coeff, bit_vars] = _imp->integer_variable_bits.find(var)->second;
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
                Integer obj_val = state(*_imp->objective_variable);
                do_it(var, obj_val);
                need_proof_variable(var < obj_val);
                _imp->proof << "# 0\n";
                _imp->proof << "u 1 " << proof_variable(var < obj_val) << " >= 1 ;\n";
                ++_imp->proof_line;
            },
            [&](const ConstantIntegerVariableID &) {
                throw UnimplementedException{};
            },
            [&](const ViewOfIntegerVariableID & var) {
                Integer obj_val = state(var.actual_variable);
                do_it(var.actual_variable, obj_val);
                auto lit = var < state(var);
                need_proof_variable(lit);
                _imp->proof << "# 0\n";
                _imp->proof << "u 1 " << proof_variable(lit) << " >= 1 ;\n";
                ++_imp->proof_line;
            }}
            .visit(*_imp->objective_variable);
    }

    _imp->proof << "# " << _imp->active_proof_level << "\n";
}

auto Proof::backtrack(const State & state) -> void
{
    _imp->proof << "* backtracking\n";
    _imp->proof << "u";
    state.for_each_guess([&](const Literal & lit) {
        _imp->proof << " 1 " << proof_variable(! lit);
    });
    _imp->proof << " >= 1 ;\n";
    ++_imp->proof_line;
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
        _imp->proof << rule;
        state.for_each_guess([&](const Literal & lit) {
            _imp->proof << " 1 " << proof_variable(! lit);
        });
        if (! is_literally_false(lit))
            _imp->proof << " 1 " << proof_variable(lit);
        _imp->proof << " >= 1 ;\n";
        ++_imp->proof_line;
    };

    overloaded{
        [&]([[maybe_unused]] const JustifyUsingRUP & j) {
            need_proof_variable(lit);
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            _imp->proof << "* RUP from " << j.where.file_name() << ":"
                        << j.where.line() << " in " << j.where.function_name() << '\n';
#endif
            output_it("u");
        },
        [&](const JustifyUsingAssertion &) {
            need_proof_variable(lit);
            output_it("a");
        },
        [&](const JustifyExplicitly & x) {
            vector<ProofLine> to_delete;
            add_proof_steps(x, to_delete);
            infer(state, lit, JustifyUsingRUP{});
            delete_proof_lines(to_delete);
        },
        [&](const Guess &) {
            // we need this because it'll show up in the trail later
            need_proof_variable(lit);
            _imp->proof << "* guessing " << proof_variable(lit) << ", decision stack is [";
            state.for_each_guess([&](const Literal & lit) {
                _imp->proof << " " << proof_variable(lit);
            });
            _imp->proof << " ]\n";
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

auto Proof::need_constraint_saying_variable_takes_at_least_one_value(IntegerVariableID var) -> ProofLine
{
    return overloaded{
        [&](const ConstantIntegerVariableID &) -> ProofLine {
            throw UnimplementedException{};
        },
        [&](const SimpleIntegerVariableID & var) -> ProofLine {
            auto result = _imp->variable_at_least_one_constraints.find(var);
            if (result == _imp->variable_at_least_one_constraints.end()) {
                auto [lower, upper] = _imp->bounds_for_gevars.find(var)->second;
                for (Integer v = lower; v <= upper; ++v)
                    need_proof_variable(var == v);

                _imp->proof << "# 0\n";

                _imp->proof << "u ";
                for (Integer v = lower; v <= upper; ++v)
                    _imp->proof << "1 " << proof_variable(var == v) << " ";

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

auto Proof::trail_variables(const State & state, Integer coeff) -> string
{
    stringstream result;
    state.for_each_guess([&](const Literal & lit) {
        result << " " << coeff << " " << proof_variable(! lit);
    });

    return result.str();
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

auto Proof::get_or_emit_line_for_bound_in_bits(State & state, bool upper, const SimpleIntegerVariableID & var, Integer val) -> ProofLine
{
    auto it = _imp->line_for_bound_in_bits.back().find(tuple{upper, var, val});
    if (it != _imp->line_for_bound_in_bits.back().end())
        return it->second;

    stringstream step;
    step << "u";
    Integer big_number = 0_i;

    auto & [_, bit_vars] = _imp->integer_variable_bits.find(var)->second;
    for (auto & [bit_coeff, bit_name] : bit_vars) {
        step << " " << (upper ? -bit_coeff : bit_coeff) << " " << bit_name;
        big_number += Integer{abs(bit_coeff)};
    }

    big_number += max(1_i, abs(val));
    step << trail_variables(state, big_number);

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
