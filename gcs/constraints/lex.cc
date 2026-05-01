#include <algorithm>
#include <gcs/constraints/lex.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <sstream>
#include <utility>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#else
#include <fmt/ostream.h>
#endif

using std::min;
using std::move;
using std::size_t;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

using namespace gcs;
using namespace gcs::innards;

LexSmartTable::LexSmartTable(vector<IntegerVariableID> vars_1, vector<IntegerVariableID> vars_2) :
    _vars_1(move(vars_1)),
    _vars_2(move(vars_2))
{
}

auto LexSmartTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<LexSmartTable>(_vars_1, _vars_2);
}

auto LexSmartTable::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    // Build the constraint as smart table
    // Question: Do we trust this encoding as a smart table?
    // Should we morally have a simpler PB encoding and reformulate?
    // Like an auto-smart-table proof?
    SmartTuples tuples;

    for (unsigned int i = 0; i < min(_vars_1.size(), _vars_2.size()); ++i) {
        vector<SmartEntry> tuple;
        for (unsigned int j = 0; j < i + 1; ++j) {
            if (j < i)
                tuple.emplace_back(SmartTable::equals(_vars_1[j], _vars_2[j]));
            else if (j == i)
                tuple.emplace_back(SmartTable::greater_than(_vars_1[j], _vars_2[j]));
        }
        tuples.emplace_back(tuple);
    }

    auto all_vars = _vars_1;
    all_vars.insert(all_vars.end(), _vars_2.begin(), _vars_2.end());

    auto smt_table = SmartTable{all_vars, tuples};
    move(smt_table).install(propagators, initial_state, optional_model);
}

auto LexSmartTable::s_exprify(const std::string & name, const innards::ProofModel * const model) const -> std::string
{
    stringstream s;

    print(s, "{} lex (", name);
    for (const auto & var : _vars_1)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") (");
    for (const auto & var : _vars_2)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ")");

    return s.str();
}

Lex::Lex(vector<IntegerVariableID> vars_1, vector<IntegerVariableID> vars_2) :
    _vars_1(move(vars_1)),
    _vars_2(move(vars_2))
{
}

auto Lex::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Lex>(_vars_1, _vars_2);
}

auto Lex::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (optional_model) {
        // Phase 2: keep delegating to LexSmartTable when a proof model is being
        // built. Phase 3 will replace this with our own proof encoding.
        auto smt_table = LexSmartTable{move(_vars_1), move(_vars_2)};
        move(smt_table).install(propagators, initial_state, optional_model);
        return;
    }

    Triggers triggers;
    for (auto & v : _vars_1)
        triggers.on_bounds.push_back(v);
    for (auto & v : _vars_2)
        triggers.on_bounds.push_back(v);

    // TODO: return PropagatorState::DisableUntilBacktrack once the constraint
    // is fully discharged (e.g. strict already forced at some position) instead
    // of always re-firing.
    propagators.install([vars_1 = move(_vars_1), vars_2 = move(_vars_2)](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        auto n = min(vars_1.size(), vars_2.size());

        // One reason for every inference this call: bounds of every variable.
        auto all_vars = vars_1;
        all_vars.insert(all_vars.end(), vars_2.begin(), vars_2.end());
        auto reason = bounds_reason(state, all_vars);

        // Left-to-right pass: while still in the forced-equal prefix, enforce
        // vars_1[i] >= vars_2[i] and decide whether to stop.
        size_t alpha = n;
        bool strict_forced = false;

        for (size_t i = 0; i < n; ++i) {
            auto b1 = state.bounds(vars_1[i]);
            auto b2 = state.bounds(vars_2[i]);

            // Either of these may raise a contradiction internally if the
            // tightened bound becomes infeasible.
            inference.infer_greater_than_or_equal(logger, vars_1[i], b2.first, JustifyUsingRUP{}, reason);
            inference.infer_less_than(logger, vars_2[i], b1.second + 1_i, JustifyUsingRUP{}, reason);

            auto nb1 = state.bounds(vars_1[i]);
            auto nb2 = state.bounds(vars_2[i]);

            if (nb1.first > nb2.second) {
                // Strict already forced at i: constraint discharged here.
                strict_forced = true;
                break;
            }
            if (nb1.first == nb1.second && nb2.first == nb2.second && nb1.first == nb2.first) {
                // Both fixed to the same value: keep walking.
                continue;
            }

            alpha = i;
            break;
        }

        if ((! strict_forced) && alpha == n) {
            // Walked off the end with everything forced equal: strict is
            // required somewhere, so infeasible.
            inference.contradiction(logger, JustifyUsingRUP{}, reason);
        }

        if (! strict_forced) {
            // Right-to-left pass: any beta > alpha where strict greater is
            // feasible? If not, strict has to happen at alpha.
            bool strict_possible_after_alpha = false;
            for (size_t i = n; i-- > alpha + 1;) {
                auto b1 = state.bounds(vars_1[i]);
                auto b2 = state.bounds(vars_2[i]);
                if (b1.second > b2.first) {
                    strict_possible_after_alpha = true;
                    break;
                }
            }

            if (! strict_possible_after_alpha) {
                auto b1 = state.bounds(vars_1[alpha]);
                auto b2 = state.bounds(vars_2[alpha]);
                inference.infer_greater_than_or_equal(logger, vars_1[alpha], b2.first + 1_i, JustifyUsingRUP{}, reason);
                inference.infer_less_than(logger, vars_2[alpha], b1.second, JustifyUsingRUP{}, reason);
            }
        }

        return PropagatorState::Enable;
    },
        triggers, "lex");
}

auto Lex::s_exprify(const std::string & name, const innards::ProofModel * const model) const -> std::string
{
    stringstream s;

    print(s, "{} lex (", name);
    for (const auto & var : _vars_1)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") (");
    for (const auto & var : _vars_2)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ")");

    return s.str();
}
