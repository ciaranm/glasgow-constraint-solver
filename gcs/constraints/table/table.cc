#include <gcs/constraints/table/table.hh>
#include <gcs/exception.hh>
#include <gcs/innards/extensional_utils.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <optional>
#include <sstream>
#include <utility>
#include <variant>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::string;
using std::stringstream;
using std::to_string;
using std::unique_ptr;
using std::variant;
using std::vector;
using std::visit;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

Table::Table(vector<IntegerVariableID> v, ExtensionalTuples t) :
    _vars(move(v)),
    _tuples(move(t))
{
}

auto Table::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Table>(_vars, ExtensionalTuples{_tuples});
}

namespace
{
    auto is_immediately_infeasible(const IntegerVariableID & var, const Integer & val) -> bool
    {
        return is_literally_false(var == val);
    }

    auto is_immediately_infeasible(const IntegerVariableID &, const Wildcard &) -> bool
    {
        return false;
    }

    auto is_immediately_infeasible(const IntegerVariableID & var, const IntegerOrWildcard & val) -> bool
    {
        return visit([&](const auto & val) { return is_immediately_infeasible(var, val); }, val);
    }

    auto add_lit_unless_immediately_true(WPBSum & lits, const IntegerVariableID & var, const Integer & val) -> void
    {
        if (! is_literally_true(var == val))
            lits += 1_i * (var == val);
    }

    auto add_lit_unless_immediately_true(WPBSum &, const IntegerVariableID &, const Wildcard &) -> void
    {
    }

    auto add_lit_unless_immediately_true(WPBSum & lits, const IntegerVariableID & var, const IntegerOrWildcard & val) -> void
    {
        return visit([&](const auto & val) { add_lit_unless_immediately_true(lits, var, val); }, val);
    }

    template <typename T_>
    auto depointinate(const std::shared_ptr<const T_> & t) -> const T_ &
    {
        return *t;
    }

    template <typename T_>
    auto depointinate(const T_ & t) -> const T_ &
    {
        return t;
    }

    auto tuple_entry_as_string(Integer i) -> string
    {
        return i.to_string();
    }

    auto tuple_entry_as_string(Wildcard) -> string
    {
        return "*";
    }

    auto tuple_entry_as_string(const variant<Integer, Wildcard> & v) -> string
    {
        return visit([](auto v) { return tuple_entry_as_string(v); }, v);
    }
}

auto Table::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Table::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    visit([&](auto & tuples) {
        if (depointinate(tuples).empty()) {
            // No allowed tuples means the constraint is UNSAT. We let
            // define_proof_model emit a trivially-false `0 >= 1` constraint
            // (which is morally what an empty selector domain encodes), and
            // install_propagators installs a contradiction initialiser. Skip
            // the selector allocation: an empty range [0, -1] would be
            // invalid, and the propagator won't run anyway.
            _has_no_tuples = true;
            return;
        }
        for (auto & tuple : depointinate(tuples))
            if (tuple.size() != _vars.size())
                throw UnexpectedException{"table size mismatch"};
        _selector = initial_state.allocate_integer_variable_with_state(0_i, Integer(depointinate(tuples).size() - 1));
    },
        _tuples);

    return true;
}

auto Table::define_proof_model(ProofModel & model) -> void
{
    if (_has_no_tuples) {
        // Morally equivalent to a selector with empty domain (`0 ≥ 1`).
        model.add_constraint("Table", "no allowed tuples", WPBSum{} >= 1_i);
        return;
    }

    visit([&](auto && tuples) {
        model.set_up_integer_variable(_selector, 0_i, Integer(depointinate(tuples).size() - 1),
            "aux_table" + to_string(_selector.index),
            IntegerVariableProofRepresentation::DirectOnly);

        // pb encoding, if necessary
        for (const auto & [tuple_idx, tuple] : enumerate(depointinate(tuples))) {
            // selector == tuple_idx -> /\_i vars[i] == tuple[i]
            bool infeasible = false;
            WPBSum lits;
            lits += Integer(tuple.size()) * (_selector != Integer(tuple_idx));
            for (const auto & [var_idx, var] : enumerate(_vars)) {
                if (is_immediately_infeasible(var, tuple[var_idx]))
                    infeasible = true;
                else
                    add_lit_unless_immediately_true(lits, var, tuple[var_idx]);
            }
            if (infeasible)
                model.add_constraint({_selector != Integer(tuple_idx)});
            else
                model.add_constraint(lits >= Integer(lits.terms.size() - 1));
        }
    },
        move(_tuples));
}

auto Table::install_propagators(Propagators & propagators) -> void
{
    if (_has_no_tuples) {
        propagators.install_initial_contradiction("Empty table constraint from table",
            JustifyUsingRUP{});
        return;
    }

    visit([&](auto && tuples) {
        Triggers triggers;
        for (auto & v : _vars)
            triggers.on_change.push_back(v);
        triggers.on_change.push_back(_selector);

        propagators.install([table = ExtensionalData{_selector, move(_vars), move(tuples)}](
                                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            return propagate_extensional(table, state, inference, logger);
        },
            triggers);
    },
        move(_tuples));
}

auto Table::s_exprify(const innards::ProofModel * const model) const -> std::string
{
    stringstream s;

    print(s, "{} table", _name);
    println(s, "(");

    println(s, "    (");
    visit([&](const auto & tuples) {
        for (const auto & t : depointinate(tuples)) {
            println(s, "        (");
            for (const auto & v : t) {
                println(s, "            {}", tuple_entry_as_string(v));
            }
            println(s, "        )");
        }
    },
        _tuples);
    println(s, "    )");

    println(s, "    (");
    for (const auto & var : _vars)
        println(s, "        {}", model->names_and_ids_tracker().s_expr_name_of(var));
    println(s, "    )");

    println(s, ")");

    return s.str();
}
