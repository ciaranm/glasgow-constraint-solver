#include <gcs/exception.hh>
#include <gcs/innards/extensional_utils.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/presolvers/auto_table.hh>
#include <gcs/search_heuristics.hh>

#include <util/enumerate.hh>

#include <optional>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
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
        Propagators & propagators, State & state, const optional<Literal> & this_branch_guess,
        ProofLogger * const logger, SimpleIntegerVariableID selector_var_id) -> void
    {
        if (logger)
            logger->enter_proof_level(depth + 1);

        if (propagators.propagate(this_branch_guess, state, logger)) {
            auto brancher = branch_with(variable_order::dom_then_deg(vars), value_order::smallest_first())(state.current(), propagators);
            auto branch_iter = brancher.begin();
            if (branch_iter == brancher.end()) {
                vector<Integer> tuple;
                for (auto & var : vars)
                    tuple.push_back(state(var));

                if (logger) {
                    logger->emit_proof_comment("new table entry found");

                    Integer sel_value(tuples.size());
                    logger->names_and_ids_tracker().create_literals_for_introduced_variable_value(selector_var_id, sel_value, "autotable");

                    WeightedPseudoBooleanSum forward_implication, reverse_implication;
                    forward_implication += Integer(vars.size()) * (selector_var_id != sel_value);
                    reverse_implication += 1_i * (selector_var_id == sel_value);

                    for (const auto & [idx, v] : enumerate(vars)) {
                        forward_implication += 1_i * (v == state(v));
                        reverse_implication += 1_i * (v != state(v));
                    }

                    logger->emit_red_proof_line(forward_implication >= Integer(vars.size()),
                        {{selector_var_id == sel_value, FalseLiteral{}}}, ProofLevel::Top);
                    logger->emit_red_proof_line(reverse_implication >= 1_i,
                        {{selector_var_id == sel_value, TrueLiteral{}}}, ProofLevel::Top);
                    state.add_extra_proof_condition(selector_var_id != sel_value);
                }

                tuples.emplace_back(move(tuple));
            }
            else {
                for (; branch_iter != brancher.end(); ++branch_iter) {
                    auto timestamp = state.new_epoch();
                    auto branch = *branch_iter;
                    state.guess(branch);
                    solve_subproblem(depth + 1, tuples, vars, propagators, state, branch, logger, selector_var_id);
                    state.backtrack(timestamp);
                }
            }
        }

        if (logger) {
            logger->enter_proof_level(depth);
            vector<Literal> guesses;
            for (const auto & lit : state.guesses())
                guesses.push_back(lit);
            logger->backtrack(guesses);
            logger->forget_proof_level(depth + 1);
        }
    }
}

auto AutoTable::run(Problem &, Propagators & propagators, State & initial_state, ProofLogger * const logger) -> bool
{
    SimpleTuples tuples;

    auto timestamp = initial_state.new_epoch(true);
    initial_state.guess(TrueLiteral{});

    auto selector_var_id = initial_state.what_variable_id_will_be_created_next();
    if (logger)
        logger->emit_proof_comment("starting autotabulation");
    solve_subproblem(0, tuples, _vars, propagators, initial_state, nullopt, logger, selector_var_id);

    if (logger)
        logger->emit_proof_comment("creating autotable with " + to_string(tuples.size()) + " entries");

    initial_state.backtrack(timestamp);

    auto selector = initial_state.allocate_integer_variable_with_state(0_i, Integer(tuples.size() - 1));
    if (selector != selector_var_id)
        throw UnexpectedException{"something went horribly wrong with variable IDs when autotabulating"};

    ExtensionalData data{selector, _vars, move(tuples)};
    if (logger)
        logger->emit_proof_comment("finished autotabulation");

    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};
    propagators.install([data = move(data)](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        return propagate_extensional(data, state, inference, logger);
    },
        {_vars}, triggers, "autotable");

    return true;
}

auto AutoTable::clone() const -> unique_ptr<Presolver>
{
    return make_unique<AutoTable>(_vars);
}
