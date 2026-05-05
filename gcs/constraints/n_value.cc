#include <gcs/constraints/n_value.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <list>
#include <map>
#include <set>
#include <sstream>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::list;
using std::map;
using std::max;
using std::set;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

NValue::NValue(const IntegerVariableID & n, std::vector<IntegerVariableID> vars) :
    _n_values(n),
    _vars(move(vars))
{
}

auto NValue::clone() const -> unique_ptr<Constraint>
{
    return make_unique<NValue>(_n_values, _vars);
}

auto NValue::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto NValue::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    for (const auto & var : _vars) {
        for (auto v : initial_state.each_value_immutable(var))
            _possible_values.emplace(v, list<IntegerVariableID>{}).first->second.push_back(var);
    }
    return true;
}

auto NValue::define_proof_model(ProofModel & model) -> void
{
    list<ProofFlag> flags;
    for (auto [v, vars] : _possible_values) {
        auto flag = model.create_proof_flag("nvalue");
        WPBSum forward;
        for (auto & var : vars)
            forward += 1_i * (var == v);
        forward += 1_i * ! flag;
        model.add_constraint("NValue", "forward sum", forward >= 1_i);

        WPBSum reverse;
        for (auto & var : vars)
            reverse += 1_i * (var != v);
        reverse += Integer(vars.size()) * flag;
        model.add_constraint("NValue", "reverse sum", reverse >= Integer(vars.size()));

        flags.push_back(flag);
    }

    WPBSum forward, reverse;
    for (auto & flag : flags) {
        forward += 1_i * flag;
        reverse += -1_i * flag;
    }
    forward += -1_i * _n_values;
    reverse += 1_i * _n_values;
    model.add_constraint("NValue", "forward total", forward >= 0_i);
    model.add_constraint("NValue", "reverse total", reverse >= 0_i);
}

auto NValue::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_bounds.emplace_back(_n_values);
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());

    vector<IntegerVariableID> all_vars = _vars;
    all_vars.push_back(_n_values);

    propagators.install([all_vars = move(all_vars), n_values = _n_values, vars = _vars](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        set<Integer> all_possible_values;
        for (const auto & var : vars) {
            for (auto v : state.each_value_immutable(var))
                all_possible_values.insert(v);
        }

        inference.infer(logger, n_values < Integer(all_possible_values.size()) + 1_i, JustifyUsingRUP{},
            generic_reason(state, all_vars));

        set<Integer> all_definite_values;
        for (const auto & var : vars) {
            auto val = state.optional_single_value(var);
            if (val)
                all_definite_values.insert(*val);
        }

        inference.infer(logger, n_values >= max(1_i, Integer(all_definite_values.size())), JustifyUsingRUP{}, generic_reason(state, all_vars));

        return PropagatorState::Enable;
    },
        triggers, "nvalue");
}

auto NValue::s_exprify(const string & name, const innards::ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} nvalue (", name);
    for (const auto & var : _vars) {
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    }
    print(s, ") {}", model->names_and_ids_tracker().s_expr_name_of(_n_values));

    return s.str();
}
