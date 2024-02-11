#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <map>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::map;
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
    map<VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID>, string> direct_integer_variables;
    map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, vector<pair<Integer, string>>>> integer_variable_bits;
    map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, Integer>> bounds_for_gevars;
    map<SimpleOrProofOnlyIntegerVariableID, map<Integer, pair<variant<ProofLine, string>, variant<ProofLine, string>>>> gevars_that_exist;
    map<pair<unsigned long long, bool>, string> flags;

    unordered_map<string, string> xification;

    bool use_friendly_names = true;
    unsigned model_variables = 0;
};

VariableConstraintsTracker::VariableConstraintsTracker(const ProofOptions & proof_options) :
    _imp(new Imp{})
{
    _imp->use_friendly_names = proof_options.use_friendly_names;
}

VariableConstraintsTracker::~VariableConstraintsTracker() = default;

auto VariableConstraintsTracker::switch_from_model_to_proof(ProofLogger * const logger) -> void
{
    _imp->model = nullptr;
    _imp->logger = logger;
}

auto VariableConstraintsTracker::start_writing_model(ProofModel * const model) -> void
{
    _imp->model = model;
}

auto VariableConstraintsTracker::track_condition_name(
    const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond, const std::string & name) -> void
{
    _imp->direct_integer_variables.emplace(cond, name);
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
                auto [lower, upper] = _imp->bounds_for_gevars.at(var);
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

auto VariableConstraintsTracker::need_pol_item_defining_literal(const IntegerVariableCondition & cond) -> variant<ProofLine, string>
{
    return overloaded{
        [&](const ConstantIntegerVariableID &) -> variant<ProofLine, string> {
            throw UnimplementedException{};
        },
        [&](const SimpleIntegerVariableID & var) -> variant<ProofLine, string> {
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
        [&](const ViewOfIntegerVariableID &) -> variant<ProofLine, string> {
            throw UnimplementedException{};
        }}
        .visit(cond.var);
}

auto VariableConstraintsTracker::create_literals_for_introduced_variable_value(
    SimpleIntegerVariableID id, Integer val, const optional<string> & optional_name) -> void
{
    string name = "i" + to_string(id.index);
    if (optional_name)
        name.append("_" + *optional_name);

    auto x = rewrite_variable_name(name + "e" + to_string(val.raw_value));
    _imp->direct_integer_variables.emplace(id == val, x);
    _imp->direct_integer_variables.emplace(id != val, "~" + x);
}

auto VariableConstraintsTracker::rewrite_variable_name(string && s) -> string
{
    if (_imp->use_friendly_names)
        return s;
    else
        return _imp->xification.try_emplace(s, "x" + to_string(_imp->xification.size() + 1)).first->second;
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

auto VariableConstraintsTracker::proof_name(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) const -> const string &
{
    auto it = _imp->direct_integer_variables.find(cond);
    if (it == _imp->direct_integer_variables.end())
        throw ProofError("No variable exists for condition on " + visit([&](const auto & v) { return debug_string(v); }, cond.var));
    return it->second;
}

auto VariableConstraintsTracker::track_flag(const ProofFlag & flag, const string & name) -> void
{
    _imp->flags.emplace(pair{flag.index, true}, name);
    _imp->flags.emplace(pair{flag.index, false}, "~" + name);
}

auto VariableConstraintsTracker::proof_name(const ProofFlag & flag) const -> const string &
{
    auto it = _imp->flags.find(pair{flag.index, flag.positive});
    if (it == _imp->flags.end())
        throw ProofError("Missing flag");
    return it->second;
}

auto VariableConstraintsTracker::negative_bit_coefficient(const SimpleOrProofOnlyIntegerVariableID & id) -> Integer
{
    auto it = _imp->integer_variable_bits.find(id);
    if (it == _imp->integer_variable_bits.end())
        throw ProofError("missing bits");
    return it->second.first;
}

auto VariableConstraintsTracker::for_each_bit(const SimpleOrProofOnlyIntegerVariableID & id,
    const std::function<auto(Integer, const std::string &)->void> & f) -> void
{
    auto it = _imp->integer_variable_bits.find(id);
    if (it == _imp->integer_variable_bits.end())
        throw ProofError("missing bits");
    for (auto & [c, n] : it->second.second)
        f(c, n);
}

auto VariableConstraintsTracker::track_bits(const SimpleOrProofOnlyIntegerVariableID & id, Integer negative_coeff,
    const std::vector<std::pair<Integer, std::string>> & bit_vars) -> void
{
    _imp->integer_variable_bits.emplace(id, pair{negative_coeff, bit_vars});
}

auto VariableConstraintsTracker::allocate_flag_index() -> unsigned long long
{
    return _imp->flags.size() / 2;
}

auto VariableConstraintsTracker::track_gevar(SimpleIntegerVariableID id, Integer val,
    const std::pair<std::variant<ProofLine, std::string>, std::variant<ProofLine, std::string>> & names) -> void
{
    _imp->gevars_that_exist[id].emplace(val, names);
}

auto VariableConstraintsTracker::need_direct_encoding_for(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> void
{
    if (_imp->direct_integer_variables.contains(id == v))
        return;

    string name = overloaded{
        [&](const SimpleIntegerVariableID & id) { return "i" + to_string(id.index); },
        [&](const ProofOnlySimpleIntegerVariableID & id) { return "p" + to_string(id.index); }}
                      .visit(id);

    auto eqvar = rewrite_variable_name(name + "e" + to_string(v.raw_value));
    _imp->direct_integer_variables.emplace(id == v, eqvar);
    _imp->direct_integer_variables.emplace(id != v, "~" + eqvar);

    auto bounds = _imp->bounds_for_gevars.find(id);
    if (bounds != _imp->bounds_for_gevars.end() && bounds->second.first == v) {
        // it's a lower bound
        if (_imp->logger)
            _imp->logger->emit_proof_comment("need lower bound for " + eqvar);
        else
            _imp->model->emit_model_comment("need lower bound for " + eqvar);

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
    else if (bounds != _imp->bounds_for_gevars.end() && bounds->second.second == v) {
        // it's an upper bound
        if (_imp->logger)
            _imp->logger->emit_proof_comment("need upper bound for " + eqvar);
        else
            _imp->model->emit_model_comment("need upper bound for " + eqvar);

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
            _imp->logger->emit_proof_comment("need " + eqvar);
        else
            _imp->model->emit_model_comment("need " + eqvar);

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
    if (_imp->direct_integer_variables.contains(id >= v))
        return;

    string name = overloaded{
        [&](const SimpleIntegerVariableID & id) { return "i" + to_string(id.index); },
        [&](const ProofOnlySimpleIntegerVariableID & id) { return "p" + to_string(id.index); }}
                      .visit(id);

    auto gevar = rewrite_variable_name(name + "g" + to_string(v.raw_value));
    _imp->direct_integer_variables.emplace(id >= v, gevar);
    _imp->direct_integer_variables.emplace(id < v, "~" + gevar);

    if (_imp->logger)
        _imp->logger->emit_proof_comment("need " + gevar);
    else
        _imp->model->emit_model_comment("need " + gevar);

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
    auto bounds = _imp->bounds_for_gevars.find(id);

    // lower?
    if (bounds != _imp->bounds_for_gevars.end() && bounds->second.first == v) {
        if (_imp->logger)
            visit([&](auto id) { _imp->logger->emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * (id >= v) >= 1_i, ProofLevel::Top); }, id);
        else
            visit([&](auto id) { _imp->model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * (id >= v) >= 1_i); }, id);
    }

    // upper?
    if (bounds != _imp->bounds_for_gevars.end() && bounds->second.second < v) {
        if (_imp->logger)
            visit([&](auto id) { _imp->logger->emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * ! (id >= v) >= 1_i, ProofLevel::Top); }, id);
        else
            visit([&](auto id) { _imp->model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! (id >= v) >= 1_i); }, id);
    }

    auto & other_gevars = _imp->gevars_that_exist.at(id);
    auto this_gevar = other_gevars.find(v);
    auto higher_gevar = next(this_gevar);

    // implied by the next highest gevar, if there is one?
    if (higher_gevar != other_gevars.end()) {
        if (_imp->logger)
            visit([&](auto id) { _imp->logger->emit_rup_proof_line(WeightedPseudoBooleanSum{} + (1_i * (id >= v)) + (1_i * ! (id >= higher_gevar->first)) >= 1_i, ProofLevel::Top); }, id);
        else
            visit([&](auto id) { _imp->model->add_constraint(WeightedPseudoBooleanSum{} + (1_i * (id >= v)) + (1_i * ! (id >= higher_gevar->first)) >= 1_i); }, id);
    }

    // implies the next lowest gevar, if there is one?
    if (this_gevar != other_gevars.begin()) {
        if (_imp->logger)
            visit([&](auto id) { _imp->logger->emit_rup_proof_line(WeightedPseudoBooleanSum{} + (1_i * (id >= prev(this_gevar)->first)) + (1_i * ! (id >= v)) >= 1_i, ProofLevel::Top); }, id);
        else
            visit([&](auto id) { _imp->model->add_constraint(WeightedPseudoBooleanSum{} + (1_i * (id >= prev(this_gevar)->first)) + (1_i * ! (id >= v)) >= 1_i); }, id);
    }
}

auto VariableConstraintsTracker::track_bounds(const SimpleOrProofOnlyIntegerVariableID & id, Integer lower, Integer upper) -> void
{
    _imp->bounds_for_gevars.emplace(id, pair{lower, upper});
}
