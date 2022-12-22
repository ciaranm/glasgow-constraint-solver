/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/exception.hh>
#include <gcs/innards/extensional_utils.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/presolvers/auto_table.hh>
#include <gcs/search_heuristics.hh>

#include <util/enumerate.hh>

#include <optional>
#include <sstream>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::optional;
using std::pair;
using std::stringstream;
using std::to_string;
using std::unique_ptr;
using std::vector;

AutoTable::AutoTable(const vector<IntegerVariableID> & v) :
    _vars(v)
{
}

namespace
{
    auto solve_subproblem(unsigned depth, SimpleTuples & tuples, const vector<IntegerVariableID> & vars,
        Propagators & propagators, State & state, SimpleIntegerVariableID selector_var_id) -> void
    {
        if (state.maybe_proof())
            state.maybe_proof()->enter_proof_level(depth + 1);

        if (propagators.propagate(state, nullptr)) {
            auto branch_var = branch_on_dom_then_deg(vars)(state.current(), propagators);
            if (! branch_var) {
                vector<Integer> tuple;
                for (auto & var : vars)
                    tuple.push_back(state(var));

                if (auto proof = state.maybe_proof()) {
                    proof->emit_proof_comment("new table entry found");
                    proof->enter_proof_level(0);

                    Integer sel_value(tuples.size());
                    proof->create_literals_for_introduced_variable_value(selector_var_id, sel_value, "autotable");

                    stringstream forward_implication, reverse_implication;
                    forward_implication << "red " << vars.size() << " " << proof->proof_variable(selector_var_id != sel_value);
                    reverse_implication << "red 1 " << proof->proof_variable(selector_var_id == sel_value);

                    for (const auto & [idx, v] : enumerate(vars)) {
                        forward_implication << " 1 " << proof->proof_variable(v == state(v));
                        reverse_implication << " 1 ~" << proof->proof_variable(v == state(v));
                    }
                    forward_implication << " >= " << vars.size() << " ; "
                                        << proof->proof_variable(selector_var_id == sel_value) << " 0";
                    reverse_implication << " >= 1 ; "
                                        << proof->proof_variable(selector_var_id == sel_value) << " 1";

                    proof->emit_proof_line(forward_implication.str());
                    proof->emit_proof_line(reverse_implication.str());
                    state.add_extra_proof_condition(selector_var_id != sel_value);

                    proof->enter_proof_level(depth + 1);
                }

                tuples.emplace_back(move(tuple));
            }
            else {
                state.for_each_value(*branch_var, [&](Integer val) {
                    auto timestamp = state.new_epoch();
                    state.guess(*branch_var == val);
                    solve_subproblem(depth + 1, tuples, vars, propagators, state, selector_var_id);
                    state.backtrack(timestamp);
                });
            }
        }

        if (auto proof = state.maybe_proof()) {
            proof->enter_proof_level(depth);
            proof->backtrack(state);
            proof->forget_proof_level(depth + 1);
        }
    }
}

auto AutoTable::run(Problem &, Propagators & propagators, State & initial_state) -> bool
{
    SimpleTuples tuples;

    auto timestamp = initial_state.new_epoch(true);
    initial_state.guess(TrueLiteral{});

    auto selector_var_id = initial_state.what_variable_id_will_be_created_next();
    if (initial_state.maybe_proof())
        initial_state.maybe_proof()->emit_proof_comment("starting autotabulation");
    solve_subproblem(0, tuples, _vars, propagators, initial_state, selector_var_id);

    if (initial_state.maybe_proof())
        initial_state.maybe_proof()->emit_proof_comment("creating autotable with " + to_string(tuples.size()) + " entries");

    initial_state.backtrack(timestamp);

    auto selector = initial_state.allocate_integer_variable_with_state(0_i, Integer(tuples.size() - 1));
    if (selector != selector_var_id)
        throw UnexpectedException{"something went horribly wrong with variable IDs when autotabulating"};

    ExtensionalData data{selector, _vars, move(tuples)};
    if (initial_state.maybe_proof())
        initial_state.maybe_proof()->emit_proof_comment("finished autotabulation");

    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};
    propagators.install([data = move(data)](State & state) mutable -> pair<Inference, PropagatorState> {
        return propagate_extensional(data, state);
    },
        triggers, "autotable");

    return true;
}

auto AutoTable::clone() const -> unique_ptr<Presolver>
{
    return make_unique<AutoTable>(_vars);
}
