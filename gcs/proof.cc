/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/detail/state.hh>
#include <gcs/exception.hh>
#include <gcs/proof.hh>

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
#include <unordered_map>
#include <vector>

using namespace gcs;

using std::bit_ceil;
using std::copy;
using std::countr_zero;
using std::flush;
using std::fstream;
using std::function;
using std::ios;
using std::istreambuf_iterator;
using std::list;
using std::llabs;
using std::map;
using std::max;
using std::ofstream;
using std::optional;
using std::ostreambuf_iterator;
using std::pair;
using std::set;
using std::string;
using std::stringstream;
using std::to_string;
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
    int active_proof_level = 0;

    map<DirectIntegerVariableID, ProofLine> variable_at_least_one_constraints;
    map<LiteralFromIntegerVariable, string> direct_integer_variables;
    map<SimpleIntegerVariableID, pair<Integer, vector<pair<Integer, string>>>> integer_variable_bits;
    map<SimpleIntegerVariableID, pair<Integer, Integer>> bounds_for_gevars;
    map<SimpleIntegerVariableID, set<Integer>> gevars_that_exist;
    list<IntegerVariableID> solution_variables;
    optional<IntegerVariableID> objective_variable;

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
}

Proof::~Proof() = default;

Proof::Proof(Proof && other) :
    _imp(move(other._imp))
{
}

auto Proof::operator=(Proof && other) -> Proof &
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

auto Proof::create_integer_variable(SimpleIntegerVariableID id, Integer lower, Integer upper, const optional<string> & optional_name,
    bool direct_encoding) -> void
{
    string name = "iv" + to_string(id.index);
    if (optional_name)
        name.append("_" + *optional_name);

    _imp->opb << "* variable " << name << " " << lower.raw_value << " .. " << upper.raw_value << " binary encoding\n";
    Integer highest_abs_value = Integer{max(llabs(lower.raw_value), upper.raw_value)};
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

    if (direct_encoding) {
        _imp->opb << "* variable " << name << " direct encoding\n";

        for (Integer v = lower; v <= upper + 1_i; ++v) {
            auto gevar = xify(name + "_ge_" + value_name(v));
            _imp->direct_integer_variables.emplace(id >= v, gevar);
            _imp->direct_integer_variables.emplace(id < v, "~" + gevar);
            _imp->gevars_that_exist[id].insert(v);

            ++_imp->model_variables;
            _imp->model_constraints += 2;

            // gevar -> bits
            for (auto & [coeff, var] : bit_vars)
                _imp->opb << coeff << " " << var << " ";
            _imp->opb << ">= " << v << " <== " << gevar << " ;\n";

            // !gevar -> bits
            for (auto & [coeff, var] : bit_vars)
                _imp->opb << -coeff << " " << var << " ";
            _imp->opb << ">= " << (-v + 1_i) << " <== ~" << gevar << " ;\n";
        }

        for (Integer v = lower; v <= upper; ++v) {
            auto eqvar = xify(name + "_eq_" + value_name(v));
            _imp->direct_integer_variables.emplace(id == v, eqvar);
            _imp->direct_integer_variables.emplace(id != v, "~" + eqvar);

            ++_imp->model_variables;
            _imp->model_constraints += 2;

            // eqvar -> ge_v && ! ge_v+1
            _imp->opb << "1 " << proof_variable(id >= v) << " 1 ~" << proof_variable(id >= v + 1_i)
                      << " >= 2 <== " << eqvar << " ;\n";

            // ge_v && ! ge_v+1 -> eqvar
            _imp->opb << "1 " << proof_variable(id >= v) << " 1 ~" << proof_variable(id >= v + 1_i)
                      << " >= 1 ==> " << eqvar << " ;\n";
        }

        for (Integer v = lower; v <= upper; ++v) {
            _imp->opb << "1 " << proof_variable(id >= v + 1_i) << " >= 1 ==> " << proof_variable(id >= v) << " ;\n";
            ++_imp->model_constraints;
        }

        _imp->opb << "1 " << proof_variable(id >= lower) << " >= 1 ;\n";
        ++_imp->model_constraints;

        _imp->opb << "1 ~" << proof_variable(id >= upper + 1_i) << " >= 1 ;\n";
        ++_imp->model_constraints;
    }
}

auto Proof::need_gevar(SimpleIntegerVariableID id, Integer v) -> void
{
    if (_imp->direct_integer_variables.count(id >= v))
        return;

    _imp->proof << "# 0\n";

    string name = "iv" + to_string(id.index);
    auto gevar = xify(name + "_ge_" + value_name(v));
    _imp->direct_integer_variables.emplace(id >= v, gevar);
    _imp->direct_integer_variables.emplace(id < v, "~" + gevar);
    _imp->gevars_that_exist[id].insert(v);

    auto & [_, bit_vars] = _imp->integer_variable_bits.find(id)->second;

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

auto Proof::need_direct_encoding_for(SimpleIntegerVariableID id, Integer v) -> void
{
    if (_imp->direct_integer_variables.count(id == v))
        return;

    need_gevar(id, v);
    need_gevar(id, v + 1_i);

    _imp->proof << "# 0\n";

    string name = "iv" + to_string(id.index);

    auto eqvar = xify(name + "_eq_" + value_name(v));
    _imp->direct_integer_variables.emplace(id == v, eqvar);
    _imp->direct_integer_variables.emplace(id != v, "~" + eqvar);

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
            [&](const ViewOfIntegerVariableID &) {
                throw UnimplementedException{};
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
    for (auto & lit : lits) {
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
    for (auto & lit : lits) {
        visit([&](const auto & lit) {
            _imp->opb << "-1 " << proof_variable(lit) << " ";
        },
            lit);
    }
    _imp->opb << ">= -1 ;\n";
    return ++_imp->model_constraints;
}

auto Proof::pseudoboolean_ge(const WeightedLiterals & lits, Integer val) -> ProofLine
{
    for (auto & [w, lit] : lits) {
        visit([this, w = w](const auto & lit) {
            _imp->opb << w << " " << proof_variable(lit) << " ";
        },
            lit);
    }
    _imp->opb << ">= " << val << " ;\n";
    return ++_imp->model_constraints;
}

auto Proof::integer_linear_le(const State &, const Linear & lin, Integer val, bool equality) -> ProofLine
{
    _imp->opb << (equality ? "* linear eq" : "* linear le");

    for (auto & [coeff, var] : lin)
        _imp->opb << " " << coeff << "*" << debug_string(var);
    _imp->opb << " <= " << val << '\n';

    auto output = [&](Integer multiplier) {
        for (auto & [coeff, var] : lin)
            overloaded{
                [&, coeff = coeff](const SimpleIntegerVariableID & v) {
                    for (auto & [bit_value, bit_name] : _imp->integer_variable_bits.find(v)->second.second)
                        _imp->opb << (multiplier * coeff * bit_value) << " " << bit_name << " ";
                },
                [&](const ConstantIntegerVariableID &) {
                    throw UnimplementedException{};
                },
                [&](const ViewOfIntegerVariableID &) {
                    throw UnimplementedException{};
                }}
                .visit(var);

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
                    LiteralFromIntegerVariable relit{view.actual_variable, ilit.op, ilit.value - view.offset};
                    return proof_variable(relit);
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

auto Proof::need_proof_variable(const Literal & lit) -> void
{
    return overloaded{
        [&](const LiteralFromIntegerVariable & ilit) {
            return overloaded{
                [&](const SimpleIntegerVariableID & var) {
                    need_direct_encoding_for(var, ilit.value);
                },
                [&](const ViewOfIntegerVariableID & view) {
                    LiteralFromIntegerVariable relit{view.actual_variable, ilit.op, ilit.value - view.offset};
                    need_proof_variable(relit);
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

    _imp->proof << "# 0\n";

    if (_imp->objective_variable) {
        Integer obj_val = state(*_imp->objective_variable);
        need_proof_variable(*_imp->objective_variable == obj_val);
    }

    _imp->proof << (_imp->objective_variable ? "o" : "v");

    for (auto & var : _imp->solution_variables)
        if ((! _imp->objective_variable) || (var != *_imp->objective_variable))
            _imp->proof << " " << proof_variable(var == state(var));

    if (_imp->objective_variable) {
        Integer obj_val = state(*_imp->objective_variable);
        _imp->proof << " " << proof_variable(*_imp->objective_variable == obj_val);

        overloaded{
            [&](const SimpleIntegerVariableID & var) {
                auto & [negative_bit_coeff, bit_vars] = _imp->integer_variable_bits.find(var)->second;
                if (obj_val.raw_value < 0) {
                    for (auto & [coeff, var] : bit_vars) {
                        if (coeff < 0_i)
                            _imp->proof << " " << var;
                        else
                            _imp->proof << " " << (((obj_val + negative_bit_coeff).raw_value & coeff.raw_value) ? "" : "~") << var;
                    }
                }
                else {
                    for (auto & [coeff, var] : bit_vars) {
                        if (coeff < 0_i)
                            _imp->proof << " ~" << var;
                        else
                            _imp->proof << " " << ((obj_val.raw_value & coeff.raw_value) ? "" : "~") << var;
                    }
                }
            },
            [&](const ConstantIntegerVariableID &) {
                throw UnimplementedException{};
            },
            [&](const ViewOfIntegerVariableID &) {
                throw UnimplementedException{};
            }}
            .visit(*_imp->objective_variable);

        _imp->proof << '\n';
        ++_imp->proof_line;

        _imp->proof << "u 1 " << proof_variable(*_imp->objective_variable < obj_val) << " >= 1 ;\n";
        ++_imp->proof_line;
    }
    else {
        _imp->proof << '\n';
        ++_imp->proof_line;
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

auto Proof::infer(const State & state, const Literal & lit, Justification why) -> void
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
        [&](const JustifyUsingRUP &) {
            need_proof_variable(lit);
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
    auto [actual_var, _] = underlying_direct_variable_and_offset(var);
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
        }}
        .visit(actual_var);
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

auto Proof::for_each_bit_defining_var(IntegerVariableID var, const function<auto(Integer, const string &)->void> & callback) -> void
{
    overloaded{
        [&](const ConstantIntegerVariableID &) {
            throw UnimplementedException{};
        },
        [&](const ViewOfIntegerVariableID &) {
            throw UnimplementedException{};
        },
        [&](const SimpleIntegerVariableID & var) {
            auto & [_, bit_vars] = _imp->integer_variable_bits.find(var)->second;
            for (auto & [coeff, var] : bit_vars)
                callback(coeff, var);
        }}
        .visit(var);
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
        for (auto & l : to_delete)
            line << " " << l;
        _imp->proof << line.str() << '\n';
    }
}
