/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/proof.hh>
#include <gcs/state.hh>
#include <gcs/exception.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <iterator>
#include <list>
#include <map>
#include <fstream>
#include <sstream>
#include <unordered_map>

using namespace gcs;

using std::copy;
using std::endl;
using std::istreambuf_iterator;
using std::fstream;
using std::ios;
using std::list;
using std::map;
using std::ofstream;
using std::ostreambuf_iterator;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::to_string;
using std::unordered_map;
using std::visit;

ProofError::ProofError(const string & w) :
    _wat("unexpected problem: " + w)
{
}

auto ProofError::what() const noexcept -> const char *
{
    return _wat.c_str();
}

struct Proof::Imp
{
    unsigned long long model_variables = 0;
    ProofLine model_constraints = 0;
    ProofLine proof_line = 0;

    map<IntegerVariableID, ProofLine> variable_at_least_one_constraints, variable_at_most_one_constraints;
    map<LiteralFromIntegerVariable, string> integer_variables;
    map<LiteralFromBooleanVariable, string> boolean_variables;
    list<IntegerVariableID> solution_variables;
    optional<IntegerVariableID> objective_variable;
    optional<Integer> objective_variable_lower, objective_variable_upper;

    string opb_file, proof_file;
    stringstream opb;
    fstream proof;

    bool use_friendly_names;
    unordered_map<string, string> xification;
};

Proof::Proof(const string & opb_file, const string & proof_file, bool use_friendly_names) :
    _imp(new Imp)
{
    _imp->opb_file = opb_file;
    _imp->proof_file = proof_file;
    _imp->use_friendly_names = use_friendly_names;

    _imp->opb << "* convenience true and false variables" << endl;

    _imp->opb << "1 " << xify("btrue") << " >= 1 ;" << endl;
    _imp->boolean_variables.emplace(+constant_variable(true), xify("btrue"));
    _imp->boolean_variables.emplace(!constant_variable(true), "~" + xify("btrue"));
    ++_imp->model_constraints;
    ++_imp->model_variables;

    _imp->opb << "1 ~" << xify("bfalse") << " >= 1 ;" << endl;
    _imp->boolean_variables.emplace(+constant_variable(false), xify("bfalse"));
    _imp->boolean_variables.emplace(!constant_variable(false), "~" + xify("bfalse"));
    ++_imp->model_constraints;
    ++_imp->model_variables;
}

Proof::~Proof() = default;

Proof::Proof(Proof && other) :
    _imp(move(other._imp))
{
}

auto Proof::operator= (Proof && other) -> Proof &
{
    _imp = move(other._imp);
    return *this;
}

[[ nodiscard ]] auto Proof::xify(std::string && s) -> std::string
{
    if (_imp->use_friendly_names)
        return s;
    else
        return _imp->xification.try_emplace(s, "x" + to_string(_imp->xification.size() + 1)).first->second;
}

namespace
{
    auto value_name(Integer v) -> string
    {
        return to_string(v.raw_value);
    }
}

auto Proof::create_integer_variable(IntegerVariableID id, Integer lower, Integer upper, const optional<string> & optional_name, bool need_ge) -> void
{
    string name = visit(overloaded{
            [&] (unsigned long long x) { return "iv" + to_string(x); },
            [&] (Integer x) { return "ic" + to_string(x.raw_value); }
            }, id.index_or_const_value);
    if (optional_name)
        name.append("_" + *optional_name);

    _imp->opb << "* variable " << name << " domain" << endl;
    _imp->model_variables += (upper - lower + 1_i).raw_value;

    for (Integer v = lower ; v <= upper ; ++v) {
        auto x = xify(name + "_eq_" + value_name(v));
        _imp->opb << "1 " << x << " ";
        _imp->integer_variables.emplace(id == v, x);
        _imp->integer_variables.emplace(id != v, "~" + x);
    }

    _imp->opb << ">= 1 ;" << endl;
    _imp->variable_at_least_one_constraints.emplace(id, ++_imp->model_constraints);

    for (Integer v = lower ; v <= upper ; ++v)
        _imp->opb << "-1 " << xify(name + "_eq_" + value_name(v)) << " ";
    _imp->opb << ">= -1 ;" << endl;
    _imp->variable_at_most_one_constraints.emplace(id, ++_imp->model_constraints);

    if (need_ge) {
        _imp->opb << "* variable " << name << " greater or equal encoding" << endl;
        _imp->model_variables += (upper - lower + 1_i).raw_value;

        _imp->opb << "1 " << xify(name + "_ge_" + value_name(lower)) << " >= 1 ;" << endl;
        ++_imp->model_constraints;

        for (Integer v = lower ; v <= upper ; ++v) {
            // x >= v -> x >= v - 1
            if (v != lower) {
                _imp->opb << "1 ~" << xify(name + "_ge_" + value_name(v)) << " 1 " << xify(name + "_ge_" + value_name(v - 1_i)) << " >= 1 ;" << endl;
                ++_imp->model_constraints;
            }

            // x < v -> x < v + 1
            if (v != upper) {
                _imp->opb << "1 " << xify(name + "_ge_" + value_name(v)) << " 1 ~" << xify(name + "_ge_" + value_name(v + 1_i)) << " >= 1 ;" << endl;
                ++_imp->model_constraints;
            }

            // x == v -> x >= v
            _imp->opb << "1 ~" << xify(name + "_eq_" + value_name(v)) << " 1 " << xify(name + "_ge_" + value_name(v)) << " >= 1 ;" << endl;
            ++_imp->model_constraints;

            // x == v -> ! x >= v + 1
            if (v != upper) {
                _imp->opb << "1 ~" << xify(name + "_eq_" + value_name(v)) << " 1 ~" << xify(name + "_ge_" + value_name(v + 1_i)) << " >= 1 ;" << endl;
                ++_imp->model_constraints;
            }

            // x != v && x != v + 1 && ... -> x < v
            for (Integer v2 = v ; v2 <= upper ; ++v2)
                _imp->opb << "1 " << xify(name + "_eq_" + value_name(v2)) << " ";
            _imp->opb << "1 ~" << xify(name + "_ge_" + value_name(v)) << " >= 1 ;" << endl;
            ++_imp->model_constraints;

            // (x >= v && x < v + 1) -> x == v
            if (v != upper) {
                _imp->opb << "1 ~" << xify(name + "_ge_" + value_name(v))
                    << " 1 " << xify(name + "_ge_" + value_name(v + 1_i))
                    << " 1 " << xify(name + "_eq_" + value_name(v))
                    << " >= 1 ;" << endl;
                ++_imp->model_constraints;
            }

            _imp->integer_variables.emplace(id >= v, xify(name + "_ge_" + value_name(v)));
            _imp->integer_variables.emplace(id < v, "~" + xify(name + "_ge_" + value_name(v)));
        }
    }

    _imp->solution_variables.push_back(id);
}

auto Proof::start_proof(State & initial_state) -> void
{
    ofstream full_opb{ _imp->opb_file };
    full_opb << "* #variable= " << _imp->model_variables << " #constraint= " << _imp->model_constraints << endl;

    if (_imp->objective_variable) {
        full_opb << "min:";
        _imp->objective_variable_lower = initial_state.lower_bound(*_imp->objective_variable);
        _imp->objective_variable_upper = initial_state.upper_bound(*_imp->objective_variable);
        for (Integer lower = *_imp->objective_variable_lower ; lower <= *_imp->objective_variable_upper ; ++lower)
            full_opb << " 1 " << proof_variable(*_imp->objective_variable >= lower);
        full_opb << " ;" << endl;
    }

    copy(istreambuf_iterator<char>{ _imp->opb }, istreambuf_iterator<char>{}, ostreambuf_iterator<char>{ full_opb });
    _imp->opb.clear();

    if (! full_opb)
        throw ProofError{ "Error writing opb file to '" + _imp->opb_file + "'" };

    _imp->proof.open(_imp->proof_file, ios::out);

    _imp->proof << "pseudo-Boolean proof version 1.0" << endl;

    _imp->proof << "f " << _imp->model_constraints << " 0" << endl;
    _imp->proof_line += _imp->model_constraints;

    if (! _imp->proof)
        throw ProofError{ "Error writing proof file to '" + _imp->proof_file + "'" };
}

auto Proof::cnf(const Literals & lits) -> ProofLine
{
    for (auto & lit : lits) {
        visit([&] (const auto & lit) {
                _imp->opb << "1 " << proof_variable(lit) << " ";
                }, lit);
    }
    _imp->opb << ">= 1 ;" << endl;
    return ++_imp->model_constraints;
}

auto Proof::at_most_one(const Literals & lits) -> ProofLine
{
    for (auto & lit : lits) {
        visit([&] (const auto & lit) {
                _imp->opb << "-1 " << proof_variable(lit) << " ";
                }, lit);
    }
    _imp->opb << ">= -1 ;" << endl;
    return ++_imp->model_constraints;
}

auto Proof::pseudoboolean_ge(const WeightedLiterals & lits, Integer val) -> ProofLine
{
    for (auto & [ w, lit ] : lits) {
        visit([&] (const auto & lit) {
                _imp->opb << w << " " << proof_variable(lit) << " ";
                }, lit);
    }
    _imp->opb << ">= " << val << " ;" << endl;
    return ++_imp->model_constraints;
}

auto Proof::integer_linear_le(const State & state, const Linear & lin, Integer val) -> void
{
    _imp->opb << "* linear le";
    for (auto & [ coeff, var ] : lin)
        _imp->opb << " " << coeff << "*" << debug_string(var);
    _imp->opb << " <= " << val << endl;

    for (auto & [ coeff, var ] : lin) {
        if (0_i == coeff)
            continue;

        auto lower = state.lower_bound(var), upper = state.upper_bound(var);
        if (lower < 0_i || lower > 1_i)
            throw UnimplementedException{ };

        for ( ; lower <= upper ; ++lower)
            if (lower != 0_i)
                _imp->opb << -coeff << " " << proof_variable(var >= lower) << " ";
    }

    _imp->opb << ">= " << -val << " ;" << endl;
    ++_imp->model_constraints;
}

auto Proof::minimise(IntegerVariableID var) -> void
{
    _imp->objective_variable = var;
}

auto Proof::proof_variable(const LiteralFromIntegerVariable & lit) const -> const string &
{
    // This might need a design rethink: if we get a constant variable, turn it into either
    // true or false based upon its condition
    return visit(overloaded{
            [&] (unsigned long long) -> const string & {
                auto it = _imp->integer_variables.find(lit);
                if (it == _imp->integer_variables.end())
                    throw ProofError("No variable exists for literal " + debug_string(lit));
                return it->second;
            },
            [&] (Integer x) -> const string & {
                bool want_true = false;
                switch (lit.state) {
                    case LiteralFromIntegerVariable::Equal:        want_true = lit.value == x; break;
                    case LiteralFromIntegerVariable::NotEqual:     want_true = lit.value != x; break;
                    case LiteralFromIntegerVariable::GreaterEqual: want_true = lit.value >= x; break;
                    case LiteralFromIntegerVariable::Less:         want_true = lit.value < x; break;
                }
                return want_true ? proof_variable(+constant_variable(true)) : proof_variable(!constant_variable(true));
            }
            }, lit.var.index_or_const_value);
}

auto Proof::proof_variable(const LiteralFromBooleanVariable & lit) const -> const string &
{
    auto it = _imp->boolean_variables.find(lit);
    if (it == _imp->boolean_variables.end())
        throw ProofError("No variable exists for literal " + debug_string(lit));
    return it->second;
}

auto Proof::proof_variable(const Literal & lit) const -> const std::string &
{
    return visit([&] (const auto & l) -> const std::string & { return proof_variable(l); }, lit);
}

auto Proof::posting(const std::string & s) -> void
{
    _imp->opb << "* constraint " << s << endl;
}

auto Proof::solution(const State & state) -> void
{
    _imp->proof << "* solution" << endl;
    _imp->proof << (_imp->objective_variable ? "o" : "v");

    for (auto & var : _imp->solution_variables)
        if ((! _imp->objective_variable) || (var != *_imp->objective_variable))
            _imp->proof << " " << proof_variable(var == state(var));

    if (_imp->objective_variable) {
        Integer obj_val = state(*_imp->objective_variable);
        for (Integer lower = *_imp->objective_variable_lower ; lower <= *_imp->objective_variable_upper ; ++lower)
            _imp->proof << (obj_val < lower ? string(" ~") : string(" ")) << proof_variable(*_imp->objective_variable >= lower);

        _imp->proof << endl;
        ++_imp->proof_line;

        _imp->proof << "u 1 " << proof_variable(*_imp->objective_variable < obj_val) << " >= 1 ;" << endl;
    }

    _imp->proof << endl;
    ++_imp->proof_line;
}

auto Proof::backtrack(const State & state) -> void
{
    _imp->proof << "* backtracking" << endl;
    _imp->proof << "u";
    state.for_each_guess([&] (const Literal & lit) {
            _imp->proof << " 1 " << proof_variable(! lit);
            });
    _imp->proof << " >= 1 ;" << endl;
    ++_imp->proof_line;
}

auto Proof::assert_contradiction() -> void
{
    _imp->proof << "* asserting contradiction" << endl;
    _imp->proof << "u >= 1 ;" << endl;
    ++_imp->proof_line;
    _imp->proof << "c " << _imp->proof_line << " 0" << endl;
}

auto Proof::infer(const State & state, const Literal & lit, Justification why) -> void
{
    visit(overloaded {
            [&] (const JustifyUsingRUP &) {
                _imp->proof << "u";
                state.for_each_guess([&] (const Literal & lit) {
                        _imp->proof << " 1 " << proof_variable(! lit);
                        });
                _imp->proof << " 1 " << proof_variable(lit);
                _imp->proof << " >= 1 ;" << endl;
                ++_imp->proof_line;
            },
            [&] (const JustifyUsingAssertion &) {
                _imp->proof << "a";
                state.for_each_guess([&] (const Literal & lit) {
                        _imp->proof << " 1 " << proof_variable(! lit);
                        });
                _imp->proof << " 1 " << proof_variable(lit);
                _imp->proof << " >= 1 ;" << endl;
                ++_imp->proof_line;
            },
            [&] (const JustifyExplicitly & x) {
                x.add_proof_steps(*this);
                infer(state, lit, JustifyUsingRUP{ });
            },
            [&] (const Guess &) {
                _imp->proof << "* guessing " << proof_variable(lit) << ", decision stack is [";
                state.for_each_guess([&] (const Literal & lit) {
                        _imp->proof << " " << proof_variable(lit);
                        });
                _imp->proof << " ]" << endl;
            },
            [] (const NoJustificationNeeded &) {
            }
        }, why);
}

auto Proof::emit_proof_line(const string & s) -> void
{
    _imp->proof << s << endl;
    ++_imp->proof_line;
}

auto Proof::constraint_saying_variable_takes_at_least_one_value(IntegerVariableID var) const -> ProofLine
{
    auto result = _imp->variable_at_least_one_constraints.find(var);
    if (result == _imp->variable_at_least_one_constraints.end())
        throw ProofError("No at least one value constraint exists for " + debug_string(var));
    return result->second;
}

auto Proof::enter_proof_level(int depth) -> void
{
    _imp->proof << "# " << depth << endl;
}

auto Proof::forget_proof_level(int depth) -> void
{
    _imp->proof << "w " << depth << endl;
}

