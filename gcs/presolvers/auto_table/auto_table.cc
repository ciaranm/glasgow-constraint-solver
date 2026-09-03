#include <gcs/constraints/extensional_utils.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/presolvers/auto_table/auto_table.hh>
#include <gcs/search_heuristics.hh>

#include <util/enumerate.hh>

#include <optional>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::make_unique;
using std::move;
using std::nullopt;
using std::optional;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

AutoTable::AutoTable(const vector<IntegerVariableID> & v, shared_ptr<AutoTableStats> stats) :
    _vars(v),
    // Always a block: these numbers had no home outside a proof file, and the
    // one that matters most is not in the proof file either when proofs are
    // written with assertions on.
    _stats(stats ? move(stats) : make_shared<AutoTableStats>())
{
}

namespace
{
    auto solve_subproblem(unsigned depth, SimpleTuples & tuples, const vector<IntegerVariableID> & vars, Propagators & propagators, State & state,
        const optional<Literal> & this_branch_guess, const BranchCallback & branch_callback, ProofLogger * const logger,
        SimpleIntegerVariableID selector_var_id, size_t & search_nodes) -> void
    {
        ++search_nodes;

        if (logger && logger->get_assertion_level() == AssertionLevel::Off)
            logger->enter_proof_level(depth + 1);

        Literals guesses;
        if (this_branch_guess)
            guesses.push_back(*this_branch_guess);
        if (propagators.propagate(guesses, state, logger)) {
            // As in solve_with_state: the brancher is a coroutine, so it only stores
            // this reference now and reads it when begin() resumes it. State::current()
            // returns by value, so the CurrentState has to be a named local that
            // outlives the generator rather than a temporary that dies on this line.
            auto current_state = state.current();
            auto brancher = branch_callback(current_state, propagators);
            auto branch_iter = brancher.begin();
            if (branch_iter == brancher.end()) {
                vector<Integer> tuple;
                for (auto & var : vars)
                    tuple.push_back(state(var));

                if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
                    logger->emit_proof_comment("new table entry found");

                    Integer sel_value(tuples.size());
                    logger->names_and_ids_tracker().create_literals_for_introduced_variable_value(selector_var_id, sel_value, "autotable");

                    WPBSum forward_implication, reverse_implication;
                    forward_implication += Integer(vars.size()) * (selector_var_id != sel_value);
                    reverse_implication += 1_i * (selector_var_id == sel_value);

                    for (const auto & [idx, v] : enumerate(vars)) {
                        forward_implication += 1_i * (v == state(v));
                        reverse_implication += 1_i * (v != state(v));
                    }

                    logger->emit_red_proof_line(
                        forward_implication >= Integer(vars.size()), {{selector_var_id == sel_value, FalseLiteral{}}}, ProofLevel::Top);
                    logger->emit_red_proof_line(reverse_implication >= 1_i, {{selector_var_id == sel_value, TrueLiteral{}}}, ProofLevel::Top);
                    state.add_extra_proof_condition(selector_var_id != sel_value);
                }

                tuples.emplace_back(move(tuple));
            }
            else {
                for (; branch_iter != brancher.end(); ++branch_iter) {
                    auto timestamp = state.new_epoch();
                    auto branch = *branch_iter;
                    state.guess(branch);
                    solve_subproblem(depth + 1, tuples, vars, propagators, state, branch, branch_callback, logger, selector_var_id, search_nodes);
                    state.backtrack(timestamp);
                }
            }
        }

        if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
            logger->enter_proof_level(depth);
            vector<Literal> guesses;
            for (const auto & g : state.guesses())
                guesses.push_back(g);
            logger->backtrack(guesses);
            logger->forget_proof_level(depth + 1);
        }
    }
}

auto AutoTable::run(Problem & problem, Propagators & propagators, State & initial_state, ProofLogger * const logger) -> bool
{
    // Before anything else, and unconditionally: a presolver that ran and found
    // nothing is what this block exists to make visible.
    propagators.add_component_stats(_stats);
    _stats->ran = true;
    _stats->variables = _vars.size();

    SimpleTuples tuples;

    // dom_then_deg is stateless, so its setup is a no-op; build the per-node
    // callback once and reuse it down the subproblem recursion.
    auto branch_callback = branch_with(variable_order::dom_then_deg(_vars), value_order::smallest_first())(problem, initial_state, propagators);

    auto timestamp = initial_state.new_epoch(true);
    initial_state.guess(TrueLiteral{});

    // A local rather than the block's field, so that a block shared across two
    // solves reports this run's cost beside this run's tuples rather than one
    // accumulated and the other overwritten.
    size_t search_nodes = 0;
    auto selector_var_id = initial_state.what_variable_id_will_be_created_next();
    solve_subproblem(0, tuples, _vars, propagators, initial_state, nullopt, branch_callback, logger, selector_var_id, search_nodes);

    _stats->tuples = tuples.size();
    _stats->search_nodes = search_nodes;

    initial_state.backtrack(timestamp);

    if (tuples.empty())
        return false;

    auto selector = initial_state.allocate_integer_variable_with_state(0_i, Integer(tuples.size() - 1));
    if (selector != selector_var_id)
        throw UnexpectedException{"something went horribly wrong with variable IDs when autotabulating"};

    // `selector` stays a State variable here only because this presolver's proof
    // derivation introduces its literals lazily; the propagator itself no longer
    // sees a selector at all.
    auto n_tuples = tuples.size();
    ExtensionalData data{_vars, move(tuples), ExtensionalLiveTuples::create(initial_state, n_tuples)};

    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};
    // A presolver-derived propagator has no posted-constraint identity of its own.
    propagators.install(
        CurrentlyUnnamedConstraint{},
        [data = move(data)](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            return propagate_extensional(data, state, inference, logger);
        },
        triggers);

    return true;
}

auto AutoTable::clone() const -> unique_ptr<Presolver>
{
    return make_unique<AutoTable>(_vars, _stats);
}

auto AutoTableStats::component_name() const -> string
{
    return "auto_table";
}

auto AutoTableStats::summary() const -> string
{
    if (! ran)
        return "did not run";

    if (0 == tuples)
        return "found no satisfying assignment of " + to_string(variables) + " variables, in " + to_string(search_nodes) + " nodes";

    return to_string(tuples) + " tuples over " + to_string(variables) + " variables, found in " + to_string(search_nodes) + " nodes";
}

auto AutoTableStats::entries() const -> vector<StatsEntry>
{
    return {StatsEntry{"ran", ran ? 1 : 0}, StatsEntry{"variables", static_cast<long long>(variables)},
        StatsEntry{"tuples", static_cast<long long>(tuples)}, StatsEntry{"search_nodes", static_cast<long long>(search_nodes)}};
}
