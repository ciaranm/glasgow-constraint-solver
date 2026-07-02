#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/exception.hh>
#include <gcs/expression.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

using namespace gcs;
using namespace gcs::innards;

using std::function;
using std::move;
using std::nullopt;
using std::optional;
using std::string;
using std::vector;

auto gcs::innards::build_table_in_proof(const vector<IntegerVariableID> & vars, const function<auto(const vector<Integer> &)->bool> & accept,
    const string & selector_name, const string & comment, State & state, ProofLogger * const logger) -> optional<ExtensionalData>
{
    vector<vector<IntegerOrWildcard>> permitted;
    vector<Integer> current;

    auto future_var_id = state.what_variable_id_will_be_created_next();

    WPBSum trail;
    function<void(ProofLogger * const)> search = [&](ProofLogger * const logger) {
        if (current.size() == vars.size()) {
            if (accept(current)) {
                permitted.emplace_back(current.begin(), current.end());
                if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
                    Integer sel_value(permitted.size() - 1);
                    logger->names_and_ids_tracker().create_literals_for_introduced_variable_value(future_var_id, sel_value, selector_name);
                    trail += 1_i * (future_var_id == sel_value);

                    WPBSum forward_implication, reverse_implication;
                    forward_implication += Integer(vars.size()) * (future_var_id != sel_value);
                    reverse_implication += 1_i * (future_var_id == sel_value);

                    for (const auto & [idx, var] : enumerate(vars)) {
                        forward_implication += 1_i * (var == current[idx]);
                        reverse_implication += 1_i * (var != current[idx]);
                    }

                    logger->emit_red_proof_line(
                        forward_implication >= Integer(vars.size()), {{future_var_id == sel_value, FalseLiteral{}}}, ProofLevel::Current);
                    logger->emit_red_proof_line(reverse_implication >= 1_i, {{future_var_id == sel_value, TrueLiteral{}}}, ProofLevel::Current);
                }
            }
        }
        else {
            const auto & var = vars[current.size()];
            for (auto val : state.each_value_mutable(var)) {
                current.push_back(val);
                search(logger);
                current.pop_back();
            }
        }

        if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
            WPBSum backtrack = trail;
            for (const auto & [idx, val] : enumerate(current))
                backtrack += 1_i * (vars[idx] != val);

            logger->emit_rup_proof_line(backtrack >= 1_i, ProofLevel::Current);
        }
    };

    if (logger && logger->get_assertion_level() == AssertionLevel::Off)
        logger->emit_proof_comment(comment);
    search(logger);

    if (permitted.empty())
        return nullopt;

    auto sel = state.allocate_integer_variable_with_state(0_i, Integer(permitted.size() - 1));
    if (sel != future_var_id)
        throw UnexpectedException{"something went horribly wrong with variable IDs"};

    return ExtensionalData{sel, vector<IntegerVariableID>{vars}, move(permitted)};
}
