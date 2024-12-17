#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <fstream>
#include <list>
#include <map>
#include <unordered_map>
#include <utility>
#include <vector>

#include <nlohmann/json.hpp>

using namespace gcs;
using namespace gcs::innards;

using std::fstream;
using std::function;
using std::ios;
using std::list;
using std::map;
using std::max;
using std::min;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::to_string;
using std::unordered_map;
using std::variant;
using std::vector;
using std::visit;

struct VariableConstraintsTracker::Imp
{
    ProofModel * model = nullptr;
    ProofLogger * logger = nullptr;

    map<SimpleOrProofOnlyIntegerVariableID, ProofLine> variable_at_least_one_constraints;
    map<VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID>, XLiteral> variable_conditions_to_x;
    map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, vector<pair<Integer, XLiteral>>>> integer_variable_bits_to_size_and_proof_vars;
    map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, Integer>> integer_variable_definition_bounds;
    map<SimpleOrProofOnlyIntegerVariableID, map<Integer, pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>>>> gevars_that_exist;
    map<ProofFlag, XLiteral> flags;

    map<SimpleOrProofOnlyIntegerVariableID, string> id_names;
    map<XLiteral, string> xlits_to_verbose_names;
    map<ProofFlag, string> flag_names;
    string unknown_name = "unnamed";

    list<function<auto(ProofLogger * const)->void>> delayed_proof_steps;

    bool use_friendly_names = true;
    unsigned model_variables = 0;
    long long next_xliteral_nr = 0;

    optional<fstream> variables_map_file;
    bool first_varmap_entry = true;
    bool verbose_names;
};

VariableConstraintsTracker::VariableConstraintsTracker(const ProofOptions & proof_options) :
    _imp(new Imp{})
{
    _imp->verbose_names = proof_options.verbose_names;

    if (proof_options.proof_file_names.variables_map_file) {
        _imp->variables_map_file.emplace();
        _imp->variables_map_file->open(*proof_options.proof_file_names.variables_map_file, ios::out);
        if (! *_imp->variables_map_file)
            throw ProofError{"Error writing proof variables mapping file to '" + *proof_options.proof_file_names.variables_map_file + "'"};
        *_imp->variables_map_file << "{\n";
    }
}

VariableConstraintsTracker::~VariableConstraintsTracker()
{
    if (_imp->variables_map_file && *_imp->variables_map_file) {
        *_imp->variables_map_file << "\n}\n";
    }
}

auto VariableConstraintsTracker::emit_proof_line_now_or_at_start(const function<auto(ProofLogger * const)->void> & func) -> void
{
    if (_imp->logger)
        func(_imp->logger);
    else
        _imp->delayed_proof_steps.push_back(func);
}

auto VariableConstraintsTracker::switch_from_model_to_proof(ProofLogger * const logger) -> void
{
    _imp->model = nullptr;
    _imp->logger = logger;
}

auto VariableConstraintsTracker::emit_delayed_proof_steps() -> void
{
    for (const auto & step : _imp->delayed_proof_steps)
        step(_imp->logger);
    _imp->delayed_proof_steps.clear();
}

auto VariableConstraintsTracker::start_writing_model(ProofModel * const model) -> void
{
    _imp->model = model;
}

auto VariableConstraintsTracker::associate_condition_with_xliteral(
    const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond, const XLiteral & x) -> void
{
    _imp->variable_conditions_to_x.emplace(cond, x);
}

auto VariableConstraintsTracker::track_variable_takes_at_least_one_value(const SimpleOrProofOnlyIntegerVariableID & id, ProofLine line) -> void
{
    _imp->variable_at_least_one_constraints.emplace(id, line);
}

auto VariableConstraintsTracker::need_constraint_saying_variable_takes_at_least_one_value(IntegerVariableID var) -> ProofLine
{
    return overloaded{
        [&](const ConstantIntegerVariableID &) -> ProofLine {
            throw UnimplementedException{};
        },
        [&](const SimpleIntegerVariableID & var) -> ProofLine {
            auto result = _imp->variable_at_least_one_constraints.find(var);
            if (result == _imp->variable_at_least_one_constraints.end()) {
                WeightedPseudoBooleanSum al1s;
                auto [lower, upper] = _imp->integer_variable_definition_bounds.at(var);
                for (Integer v = lower; v <= upper; ++v)
                    al1s += 1_i * (var == v);

                auto line = _imp->logger->emit_rup_proof_line(al1s >= 1_i, ProofLevel::Top);
                result = _imp->variable_at_least_one_constraints.emplace(var, line).first;
            }
            return result->second;
        },
        [&](const ViewOfIntegerVariableID & var) -> ProofLine {
            return need_constraint_saying_variable_takes_at_least_one_value(var.actual_variable);
        }}
        .visit(var);
}

auto VariableConstraintsTracker::need_pol_item_defining_literal(const IntegerVariableCondition & cond) -> variant<ProofLine, XLiteral>
{
    return overloaded{
        [&](const ConstantIntegerVariableID &) -> variant<ProofLine, XLiteral> {
            throw UnimplementedException{};
        },
        [&](const SimpleIntegerVariableID & var) -> variant<ProofLine, XLiteral> {
            switch (cond.op) {
                using enum VariableConditionOperator;
            case GreaterEqual:
                need_gevar(var, cond.value);
                return _imp->gevars_that_exist.at(var).at(cond.value).first;
            case Less:
                need_gevar(var, cond.value);
                return _imp->gevars_that_exist.at(var).at(cond.value).second;
            case Equal:
                throw UnimplementedException{};
            case NotEqual:
                throw UnimplementedException{};
            }
            throw NonExhaustiveSwitch{};
        },
        [&](const ViewOfIntegerVariableID &) -> variant<ProofLine, XLiteral> {
            throw UnimplementedException{};
        }}
        .visit(cond.var);
}

auto VariableConstraintsTracker::create_literals_for_introduced_variable_value(
    SimpleIntegerVariableID id, Integer val, const optional<string> & optional_name) -> void
{
    if (optional_name)
        track_variable_name(id, *optional_name);
    auto x = allocate_xliteral_meaning(id, EqualsOrGreaterEqual::Equals, val);
    _imp->variable_conditions_to_x.emplace(id == val, x);
    _imp->variable_conditions_to_x.emplace(id != val, ! x);
}

auto VariableConstraintsTracker::need_proof_name(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) -> void
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

auto VariableConstraintsTracker::need_all_proof_names_in(const SumOf<Weighted<PseudoBooleanTerm>> & sum) -> void
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

auto VariableConstraintsTracker::negative_bit_coefficient(const SimpleOrProofOnlyIntegerVariableID & id) -> Integer
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(id);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");
    return it->second.first;
}

auto VariableConstraintsTracker::for_each_bit(const SimpleOrProofOnlyIntegerVariableID & id,
    const std::function<auto(Integer, const XLiteral &)->void> & f) -> void
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(id);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");
    for (auto & [c, n] : it->second.second)
        f(c, n);
}

auto VariableConstraintsTracker::track_bits(const SimpleOrProofOnlyIntegerVariableID & id, Integer negative_coeff,
    const std::vector<std::pair<Integer, XLiteral>> & bit_vars) -> void
{
    _imp->integer_variable_bits_to_size_and_proof_vars.emplace(id, pair{negative_coeff, bit_vars});
}

auto VariableConstraintsTracker::allocate_flag_index() -> unsigned long long
{
    return _imp->flags.size() / 2;
}

auto VariableConstraintsTracker::track_gevar(SimpleIntegerVariableID id, Integer val,
    const std::pair<std::variant<ProofLine, XLiteral>, std::variant<ProofLine, XLiteral>> & names) -> void
{
    _imp->gevars_that_exist[id].emplace(val, names);
}

auto VariableConstraintsTracker::need_direct_encoding_for(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> void
{
    if (_imp->variable_conditions_to_x.contains(id == v))
        return;

    auto eqvar = allocate_xliteral_meaning(id, EqualsOrGreaterEqual::Equals, v);
    _imp->variable_conditions_to_x.emplace(id == v, eqvar);
    _imp->variable_conditions_to_x.emplace(id != v, ! eqvar);

    auto bounds = _imp->integer_variable_definition_bounds.find(id);
    if (bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.first == v) {
        // it's a lower bound
        if (_imp->logger) {
            visit([&](const auto & id) {
                _imp->logger->emit_red_proof_lines_reifying(WeightedPseudoBooleanSum{} + 1_i * ! (id >= (v + 1_i)) >= 1_i,
                    id == v, ProofLevel::Top);
            },
                id);
        }
        else {
            visit([&](const auto & id) {
                _imp->model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! (id >= (v + 1_i)) >= 1_i, {{id == v}});
                _imp->model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * (id >= (v + 1_i)) >= 1_i, {{id != v}});
            },
                id);
            ++_imp->model_variables;
        }
    }
    else if (bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.second == v) {
        // it's an upper bound
        if (_imp->logger) {
            visit([&](const auto & id) {
                _imp->logger->emit_red_proof_lines_reifying(WeightedPseudoBooleanSum{} + 1_i * (id >= v) >= 1_i, id == v, ProofLevel::Top);
            },
                id);
        }
        else {
            visit([&](const auto & id) {
                _imp->model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * (id >= v) >= 1_i, {{id == v}});
                _imp->model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! (id >= v) >= 1_i, {{id != v}});
            },
                id);
            ++_imp->model_variables;
        }
    }
    else {
        // neither a lower nor an upper bound
        if (_imp->logger)
            visit([&](const auto & id) {
                _imp->logger->emit_red_proof_lines_reifying(
                    WeightedPseudoBooleanSum{} + (1_i * (id >= v)) + (1_i * ! (id >= (v + 1_i))) >= 2_i,
                    id == v, ProofLevel::Top);
            },
                id);
        else {
            visit([&](const auto & id) {
                _imp->model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * (id >= v) + 1_i * ! (id >= v + 1_i) >= 2_i, {{id == v}});
                _imp->model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! (id >= v) + 1_i * (id >= v + 1_i) >= 1_i, {{id != v}});
            },
                id);
            ++_imp->model_variables;
        }
    }
}

auto VariableConstraintsTracker::need_gevar(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> void
{
    if (_imp->variable_conditions_to_x.contains(id >= v))
        return;

    auto gevar = allocate_xliteral_meaning(id, EqualsOrGreaterEqual::GreaterEqual, v);
    _imp->variable_conditions_to_x.emplace(id >= v, gevar);
    _imp->variable_conditions_to_x.emplace(id < v, ! gevar);

    // gevar -> bits
    if (_imp->logger) {
        _imp->gevars_that_exist[id].emplace(v, visit([&](const auto & id) {
            return _imp->logger->emit_red_proof_lines_reifying(WeightedPseudoBooleanSum{} + (1_i * id) >= v, id >= v, ProofLevel::Top);
        },
                                                   id));
    }
    else {
        _imp->gevars_that_exist[id].emplace(v, visit([&](const auto & id) {
            return pair{
                _imp->model->add_constraint(WeightedPseudoBooleanSum{} + (1_i * id) >= v, {{id >= v}}).value(),
                _imp->model->add_constraint(WeightedPseudoBooleanSum{} + (-1_i * id) >= -v + 1_i, {{id < v}}).value()};
        },
                                                   id));
        ++_imp->model_variables;
    }

    // is it a bound?
    auto bounds = _imp->integer_variable_definition_bounds.find(id);

    // lower?
    if (bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.first >= v) {
        if (_imp->logger)
            visit([&](auto id) { _imp->logger->emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * (id >= v) >= 1_i, ProofLevel::Top); }, id);
        else
            visit([&](auto id) { _imp->model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * (id >= v) >= 1_i); }, id);
    }

    // upper?
    if (bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.second < v) {
        if (_imp->logger)
            visit([&](auto id) { _imp->logger->emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * ! (id >= v) >= 1_i, ProofLevel::Top); }, id);
        else
            visit([&](auto id) { _imp->model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! (id >= v) >= 1_i); }, id);
    }

    auto & other_gevars = _imp->gevars_that_exist.at(id);
    auto this_gevar = other_gevars.find(v);
    auto higher_gevar = next(this_gevar);

    // implied by the next highest gevar, if there is one?
    if (higher_gevar != other_gevars.end())
        visit([&](auto id) { emit_proof_line_now_or_at_start([c = WeightedPseudoBooleanSum{} + (1_i * (id >= v)) + (1_i * ! (id >= higher_gevar->first)) >= 1_i](ProofLogger * const logger) {
                                 logger->emit_rup_proof_line(c, ProofLevel::Top);
                             }); }, id);

    // implies the next lowest gevar, if there is one?
    if (this_gevar != other_gevars.begin())
        visit([&](auto id) { emit_proof_line_now_or_at_start([c = WeightedPseudoBooleanSum{} + (1_i * (id >= prev(this_gevar)->first)) + (1_i * ! (id >= v)) >= 1_i](ProofLogger * const logger) {
                                 logger->emit_rup_proof_line(c, ProofLevel::Top);
                             }); }, id);
}

auto VariableConstraintsTracker::track_bounds(const SimpleOrProofOnlyIntegerVariableID & id, Integer lower, Integer upper) -> void
{
    _imp->integer_variable_definition_bounds.emplace(id, pair{lower, upper});
}

auto VariableConstraintsTracker::create_proof_flag(const string & name) -> ProofFlag
{
    ProofFlag result{allocate_flag_index(), true};
    track_variable_name(result, name);
    auto flagvar = allocate_xliteral_meaning(result);
    _imp->flags.emplace(result, flagvar);
    _imp->flags.emplace(! result, ! flagvar);
    return result;
}

auto VariableConstraintsTracker::pb_file_string_for(const XLiteral & lit) const -> string
{
    if (_imp->verbose_names) {
        auto it = _imp->xlits_to_verbose_names.find(lit);
        if (it == _imp->xlits_to_verbose_names.end())
            throw ProofError("missing verbose name for xliteral " + to_string(lit.id) + " " + to_string(lit.negated));
        return it->second;
    }
    else {
        if (lit.negated)
            return "~x" + to_string(lit.id);
        else
            return "x" + to_string(lit.id);
    }
}

auto VariableConstraintsTracker::pb_file_string_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) const -> string
{
    return pb_file_string_for(xliteral_for(cond));
}

auto VariableConstraintsTracker::xliteral_for(const ProofFlag & flag) const -> const XLiteral
{
    auto f = _imp->flags.find(flag);
    if (f == _imp->flags.end())
        throw ProofError{"can't find literals for flag"};
    return f->second;
}

auto VariableConstraintsTracker::xliteral_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) const -> const XLiteral
{
    auto f = _imp->variable_conditions_to_x.find(cond);
    if (f == _imp->variable_conditions_to_x.end())
        throw ProofError{"can't find literals for cond"};
    return f->second;
}

auto VariableConstraintsTracker::pb_file_string_for(const ProofFlag & flag) const -> string
{
    return pb_file_string_for(xliteral_for(flag));
}

namespace
{
    auto write_vardata(fstream & stream, bool & first, const string & name, const nlohmann::json & json) -> void
    {
        if (! first)
            stream << ",\n";
        else
            first = false;

        nlohmann::json name_json = name;
        stream << name_json << ": " << json;
    }
}

auto VariableConstraintsTracker::allocate_xliteral_meaning(SimpleOrProofOnlyIntegerVariableID id,
    const EqualsOrGreaterEqual & op, Integer value) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        overloaded{
            [&](const SimpleIntegerVariableID & id) -> void {
                string name = "i" + to_string(id.index) + "_" + name_of(id) + (op == EqualsOrGreaterEqual::Equals ? "_e" : "_g") + to_string(value.raw_value);
                _imp->xlits_to_verbose_names.emplace(result, name);
                _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
            },
            [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                string name = "p" + to_string(id.index) + "_" + name_of(id) + (op == EqualsOrGreaterEqual::Equals ? "_e" : "_g") + to_string(value.raw_value);
                _imp->xlits_to_verbose_names.emplace(result, name);
                _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
            }}
            .visit(id);
    }

    if (_imp->variables_map_file) {
        nlohmann::json data;
        data["type"] = "condition";
        overloaded{
            [&](const SimpleIntegerVariableID & id) -> void {
                data["cpvartype"] = "intvar";
                data["cpvarid"] = id.index;
            },
            [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                data["cpvartype"] = "proofintvar";
                data["cpvarid"] = id.index;
            }}
            .visit(id);

        data["name"] = name_of(id);
        data["operator"] = (op == EqualsOrGreaterEqual::Equals ? "=" : ">=");
        data["value"] = value.raw_value;

        write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
    }

    return result;
}

auto VariableConstraintsTracker::allocate_xliteral_meaning(ProofFlag flag) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        string name = "f" + to_string(flag.index) + "_" + name_of(flag);
        _imp->xlits_to_verbose_names.emplace(result, name);
        _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
    }

    if (_imp->variables_map_file) {
        nlohmann::json data;
        data["type"] = "proofflag";
        data["name"] = name_of(flag);

        write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
    }

    return result;
}

auto VariableConstraintsTracker::allocate_xliteral_meaning_negative_bit_of(SimpleOrProofOnlyIntegerVariableID id, Integer power) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        overloaded{
            [&](const SimpleIntegerVariableID & id) -> void {
                string name = "i" + to_string(id.index) + "_" + name_of(id) + "_n";
                _imp->xlits_to_verbose_names.emplace(result, name);
                _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
            },
            [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                string name = "p" + to_string(id.index) + "_" + name_of(id) + "_n";
                _imp->xlits_to_verbose_names.emplace(result, name);
                _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
            }}
            .visit(id);
    }

    if (_imp->variables_map_file) {
        nlohmann::json data;
        data["type"] = "intvarnegbit";
        overloaded{
            [&](const SimpleIntegerVariableID & id) -> void {
                data["cpvartype"] = "intvar";
                data["cpvarid"] = id.index;
            },
            [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                data["cpvartype"] = "proofintvar";
                data["cpvarid"] = id.index;
            }}
            .visit(id);
        data["name"] = name_of(id);
        data["power"] = power.raw_value;

        write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
    }

    return result;
}

auto VariableConstraintsTracker::allocate_xliteral_meaning_bit_of(SimpleOrProofOnlyIntegerVariableID id, Integer power) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        overloaded{
            [&](const SimpleIntegerVariableID & id) -> void {
                string name = "i" + to_string(id.index) + "_" + name_of(id) + "_b" + to_string(power.raw_value);
                _imp->xlits_to_verbose_names.emplace(result, name);
                _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
            },
            [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                string name = "p" + to_string(id.index) + "_" + name_of(id) + "_b" + to_string(power.raw_value);
                _imp->xlits_to_verbose_names.emplace(result, name);
                _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
            }}
            .visit(id);
    }

    if (_imp->variables_map_file) {
        nlohmann::json data;
        data["type"] = "intvarbit";
        overloaded{
            [&](const SimpleIntegerVariableID & id) -> void {
                data["cpvartype"] = "intvar";
                data["cpvarid"] = id.index;
            },
            [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                data["cpvartype"] = "proofintvar";
                data["cpvarid"] = id.index;
            }}
            .visit(id);

        data["name"] = name_of(id);
        data["power"] = power.raw_value;

        write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
    }

    return result;
}

auto VariableConstraintsTracker::track_variable_name(SimpleOrProofOnlyIntegerVariableID id, const optional<string> & name) -> void
{
    if (name)
        _imp->id_names.emplace(id, *name);
}

auto VariableConstraintsTracker::track_variable_name(ProofFlag id, const optional<string> & name) -> void
{
    if (name)
        _imp->flag_names.emplace(id, *name);
}

auto VariableConstraintsTracker::name_of(SimpleOrProofOnlyIntegerVariableID id) -> const string &
{
    auto it = _imp->id_names.find(id);
    if (_imp->id_names.end() == it)
        return _imp->unknown_name;
    else
        return it->second;
}

auto VariableConstraintsTracker::name_of(ProofFlag id) -> const string &
{
    auto it = _imp->flag_names.find(id);
    if (_imp->flag_names.end() == it)
        return _imp->unknown_name;
    else
        return it->second;
}

auto VariableConstraintsTracker::reify(const WeightedPseudoBooleanLessEqual & ineq, const HalfReifyOnConjunctionOf & half_reif) -> WeightedPseudoBooleanLessEqual
{
    //    auto contains_false_literal = false;
    //    for (const auto & l : half_reif) {
    //
    //        contains_false_literal |= overloaded{
    //            [&](const ProofFlag &) { return false; },
    //            [&](const ProofLiteral & pl) {
    //                return overloaded{
    //                    [&](Literal lit) {
    //                        return is_literally_false(lit);
    //                    },
    //                    [&](const ProofVariableCondition &) { return false; },
    //                }
    //                    .visit(pl);
    //            }}.visit(l);
    //    }

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
                    [&]<typename T_>(const VariableConditionFrom<T_> &) {
                        reif_const += max(0_i, w);
                    }}
                    .visit(simplify_literal(lit));
            },
            [&, w = w](const ProofFlag &) {
                reif_const += max(0_i, w);
            },
            [&, w = w](const IntegerVariableID & var) {
                overloaded{
                    [&](const SimpleIntegerVariableID & var) {
                        for_each_bit(var, [&](Integer bit_value, const XLiteral &) {
                            reif_const += max(0_i, w * bit_value);
                        });
                    },
                    [&](const ViewOfIntegerVariableID & view) {
                        if (! view.negate_first) {
                            for_each_bit(view.actual_variable,
                                [&](Integer bit_value, const XLiteral &) {
                                    reif_const += max(0_i, w * bit_value);
                                });
                            rhs += w * view.then_add;
                            reif_const += max(0_i, -w * view.then_add);
                        }
                        else {
                            for_each_bit(view.actual_variable,
                                [&](Integer bit_value, const XLiteral &) {
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
                for_each_bit(var, [&](Integer bit_value, const XLiteral &) {
                    reif_const += max(0_i, w * bit_value);
                });
            },
        }
            .visit(v);
    }

    reif_const += rhs;
    reif_const = max(reif_const, 1_i);
    WeightedPseudoBooleanSum new_lhs = ineq.lhs;
    for (auto & r : half_reif)
        overloaded{
            [&](const ProofFlag & f) {
                new_lhs += -Integer{reif_const} * ! f;
            },
            [&](const ProofLiteral & lit) {
                new_lhs += -Integer{reif_const} * ! lit;
            }}
            .visit(r);

    //    if (contains_false_literal) {
    //        // This might be a bad idea...
    //        return new_lhs >= -rhs + reif_const;
    //    }
    //    else {
    return new_lhs <= -rhs;
    //    }
}
