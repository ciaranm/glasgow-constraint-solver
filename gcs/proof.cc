/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/proof.hh>
#include <gcs/state.hh>
#include <gcs/exception.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <bit>
#include <iterator>
#include <list>
#include <map>
#include <fstream>
#include <sstream>
#include <unordered_map>
#include <vector>

using namespace gcs;

using std::bit_ceil;
using std::copy;
using std::countr_zero;
using std::endl;
using std::istreambuf_iterator;
using std::fstream;
using std::ios;
using std::list;
using std::map;
using std::min;
using std::ofstream;
using std::ostreambuf_iterator;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::to_string;
using std::unordered_map;
using std::vector;
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

    map<DirectIntegerVariableID, ProofLine> variable_at_least_one_constraints, variable_at_most_one_constraints;
    map<LiteralFromIntegerVariable, string> integer_variables;
    list<IntegerVariableID> solution_variables;
    optional<IntegerVariableID> objective_variable;
    optional<Integer> objective_variable_lower, objective_variable_upper;

    string opb_file, proof_file;
    stringstream opb;
    fstream proof;
    bool opb_done = false;

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

auto Proof::create_integer_variable(SimpleIntegerVariableID id, Integer lower, Integer upper, const optional<string> & optional_name) -> void
{
    string name = "iv" + to_string(id.index);
    if (optional_name)
        name.append("_" + *optional_name);

    _imp->opb << "* variable " << name << " binary encoding" << endl;
    unsigned n_positive_bits = 0, n_negative_bits = 0;
    vector<pair<long long, string> > bit_vars;
    if (upper >= 0_i) {
        // including zero, just because it gets horrible otherwise
        // 8 == 1000
        n_positive_bits = countr_zero(bit_ceil(static_cast<unsigned long long>(upper.raw_value)));
        for (unsigned b = 0 ; b <= n_positive_bits ; ++b)
            bit_vars.emplace_back(1ll << b, xify(name + "_b_" + to_string(b)));
    }
    if (lower < 0_i) {
        n_negative_bits = countr_zero(bit_ceil(static_cast<unsigned long long>(-lower.raw_value)));
        for (unsigned b = 0 ; b <= n_negative_bits ; ++b)
            bit_vars.emplace_back(-(1ll << b), xify(name + "_b_-" + to_string(b)));
    }
    _imp->model_variables += bit_vars.size();

    // lower bound
    for (auto & [ coeff, var ] : bit_vars)
        _imp->opb << coeff << " " << var << " ";
    _imp->opb << ">= " << lower << " ;" << endl;
    ++_imp->model_constraints;

    // upper bound
    for (auto & [ coeff, var ] : bit_vars)
        _imp->opb << -coeff << " " << var << " ";
    _imp->opb << ">= " << -upper << " ;" << endl;
    ++_imp->model_constraints;

    // any negative bits set -> no positive bits set
    if (n_negative_bits != 0 && n_positive_bits != 0) {
        for (auto & [ coeff, var ] : bit_vars) {
            if (coeff < 0) {
                _imp->opb << n_positive_bits << " ~" << var;
                for (auto & [ other_coeff, other_var ] : bit_vars) {
                    if (other_coeff >= 0) {
                        // var -> ! other_var
                        _imp->opb << " 1 ~" << other_var;
                    }
                }
                _imp->opb << " >= " << n_positive_bits << " ;" << endl;
                ++_imp->model_constraints;
            }
        }
    }

    _imp->opb << "* variable " << name << " direct encoding" << endl;
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

    for (Integer v = lower ; v <= upper ; ++v) {
        auto x = xify(name + "_eq_" + value_name(v));
        // var -> bits
        _imp->opb << bit_vars.size() << " ~" << x;
        for (auto & [ coeff, var ] : bit_vars) {
            if (coeff < 0)
                _imp->opb << " 1 " << ((v.raw_value < 0 && (-v.raw_value & -coeff)) ? "" : "~") << var;
            else
                _imp->opb << " 1 " << ((v.raw_value >= 0 && (v.raw_value & coeff)) ? "" : "~") << var;
        }
        _imp->opb << " >= " << bit_vars.size() << " ;" << endl;
        ++_imp->model_constraints;
    }

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

    _imp->solution_variables.push_back(id);
}

auto Proof::create_pseudovariable(SimpleIntegerVariableID id, Integer lower, Integer upper, const optional<string> & optional_name) -> void
{
    string name = "iv" + to_string(id.index);
    if (optional_name)
        name.append("_" + *optional_name);

    for (Integer v = lower ; v <= upper ; ++v) {
        auto x = xify(name + "_eq_" + value_name(v));
        _imp->integer_variables.emplace(id == v, x);
        _imp->integer_variables.emplace(id != v, "~" + x);
    }
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
    _imp->opb_done = true;

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

auto Proof::integer_linear_le(const State & state, const Linear & lin, Integer val, bool equality) -> void
{
    _imp->opb << (equality ? "* linear eq" : "* linear le");

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

    if (equality) {
        for (auto & [ coeff, var ] : lin) {
            if (0_i == coeff)
                continue;

            auto lower = state.lower_bound(var), upper = state.upper_bound(var);
            if (lower < 0_i || lower > 1_i)
                throw UnimplementedException{ };

            for ( ; lower <= upper ; ++lower)
                if (lower != 0_i)
                    _imp->opb << coeff << " " << proof_variable(var >= lower) << " ";
        }

        _imp->opb << ">= " << val << " ;" << endl;
        ++_imp->model_constraints;
    }
}

auto Proof::minimise(IntegerVariableID var) -> void
{
    _imp->objective_variable = var;
}

auto Proof::proof_variable(const Literal & lit) const -> const string &
{
    // This might need a design rethink: if we get a constant variable, turn it into either
    // true or false based upon its condition
    return visit(overloaded{
            [&] (const LiteralFromIntegerVariable & ilit) -> const string & {
                return visit(overloaded{
                    [&] (const SimpleIntegerVariableID &) -> const string & {
                        auto it = _imp->integer_variables.find(ilit);
                        if (it == _imp->integer_variables.end())
                            throw ProofError("No variable exists for literal " + debug_string(lit));
                        return it->second;
                    },
                    [&] (const ViewOfIntegerVariableID & view) -> const string & {
                        LiteralFromIntegerVariable relit{ view.actual_variable, ilit.op, ilit.value - view.offset };
                        return proof_variable(relit);
                    },
                    [&] (const ConstantIntegerVariableID &) -> const string & {
                        throw UnimplementedException{ };
                    }
                    }, ilit.var);
            },
            [&] (const TrueLiteral &) -> const string & {
                throw UnimplementedException{ };
            },
            [&] (const FalseLiteral &) -> const string & {
                throw UnimplementedException{ };
            }
            }, lit);
}

auto Proof::posting(const std::string & s) -> void
{
    if (_imp->opb_done)
        throw UnexpectedException{ "proof has already started" };
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
                if (! is_literally_false(lit))
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
    auto [ actual_var, _ ] = underlying_direct_variable_and_offset(var);
    auto result = _imp->variable_at_least_one_constraints.find(actual_var);
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

