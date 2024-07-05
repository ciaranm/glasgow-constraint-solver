#include <gcs/constraints/in.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::erase_if;
using std::move;
using std::optional;
using std::sort;
using std::string;
using std::unique;
using std::unique_ptr;
using std::vector;

In::In(IntegerVariableID var, vector<IntegerVariableID> vars, vector<Integer> vals) :
    _var(var),
    _var_vals(move(vars)),
    _val_vals(move(vals))
{
}

In::In(IntegerVariableID var, vector<IntegerVariableID> vals) :
    _var(var),
    _var_vals(move(vals))
{
}

In::In(IntegerVariableID var, vector<Integer> vals) :
    _var(var),
    _val_vals(move(vals))
{
}

auto In::clone() const -> unique_ptr<Constraint>
{
    return make_unique<In>(_var, _var_vals, _val_vals);
}

auto In::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    erase_if(_var_vals, [&](const IntegerVariableID & v) -> bool {
        auto const_val = initial_state.optional_single_value(v);
        if (const_val)
            _val_vals.push_back(*const_val);
        return const_val.has_value();
    });

    sort(_val_vals.begin(), _val_vals.end());
    _val_vals.erase(unique(_val_vals.begin(), _val_vals.end()), _val_vals.end());

    if (_var_vals.empty() && _val_vals.empty())
        propagators.model_contradiction(initial_state, optional_model, "No values or variables present for an 'In' constraint");
    else if (_var_vals.empty()) {
        vector<IntegerVariableID> vars;
        vars.emplace_back(_var);

        vector<vector<Integer>> tuples;
        for (auto & v : _val_vals)
            tuples.emplace_back(vector{{v}});

        propagators.define_and_install_table(initial_state, optional_model, move(vars), move(tuples), "in");
    }
    else {
        throw UnimplementedException{};
    }
}

auto In::describe_for_proof() -> string
{
    return "in";
}
