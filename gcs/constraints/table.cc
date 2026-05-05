#include <gcs/constraints/table.hh>
#include <gcs/exception.hh>
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
        return to_string(i.raw_value);
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
    visit([&](auto & tuples) {
        for (auto & tuple : depointinate(tuples))
            if (tuple.size() != _vars.size())
                throw UnexpectedException{"table size mismatch"};
    },
        _tuples);

    propagators.define_and_install_table(initial_state, optional_model, vector<IntegerVariableID>{_vars}, move(_tuples), "table");
}

auto Table::s_exprify(const string & name, const innards::ProofModel * const model) const -> std::string
{
    stringstream s;

    print(s, "{} table", name);
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

NegativeTable::NegativeTable(vector<IntegerVariableID> v, ExtensionalTuples t) :
    _vars(move(v)),
    _tuples(move(t))
{
}

auto NegativeTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<NegativeTable>(_vars, ExtensionalTuples{_tuples});
}

namespace
{
    auto add_literal(Literals & lits, const IntegerVariableID & var, const Integer & val)
    {
        lits.emplace_back(var != val);
    }

    auto add_literal(Literals &, const IntegerVariableID &, const Wildcard &)
    {
    }

    auto add_literal(Literals & lits, const IntegerVariableID & var, const IntegerOrWildcard & val)
    {
        visit([&](const auto & val) { add_literal(lits, var, val); }, val);
    }
}

namespace
{
    auto operator==(const IntegerVariableID &, const Wildcard &) -> Literal
    {
        return TrueLiteral{};
    }

    auto operator==(const IntegerVariableID & v, const IntegerOrWildcard & val) -> Literal
    {
        return visit([&](const auto & val) -> Literal { return v == val; }, val);
    }

    auto operator!=(const IntegerVariableID &, const Wildcard &) -> Literal
    {
        return FalseLiteral{};
    }

    auto operator!=(const IntegerVariableID & v, const IntegerOrWildcard & val) -> Literal
    {
        return visit([&](const auto & val) -> Literal { return v != val; }, val);
    }
}

namespace gcs
{
    using ::operator==;
    using ::operator!=;
}

auto NegativeTable::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto NegativeTable::prepare(Propagators &, State &, ProofModel * const) -> bool
{
    visit([&](auto & tuples) {
        for (auto & tuple : depointinate(tuples))
            if (tuple.size() != _vars.size())
                throw UnexpectedException{"table size mismatch"};
    },
        _tuples);
    return true;
}

auto NegativeTable::define_proof_model(ProofModel & model) -> void
{
    visit([&](auto & tuples) {
        for (auto & t : depointinate(tuples)) {
            Literals lits;
            for (const auto & [idx, v] : enumerate(_vars))
                add_literal(lits, v, t[idx]);
            model.add_constraint("NegativeTable", "forbidden", move(lits));
        }
    },
        _tuples);
}

auto NegativeTable::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (auto & v : _vars)
        triggers.on_change.emplace_back(v);

    visit([&](const auto & tuples) {
        propagators.install([vars = move(_vars), tuples = move(tuples)](
                                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            for (auto & t : depointinate(tuples)) {
                bool falsified = false;
                optional<Literal> l1, l2;
                for (const auto & [idx, v] : enumerate(vars)) {
                    switch (state.test_literal(v == t[idx])) {
                        using enum LiteralIs;
                    case DefinitelyFalse:
                        falsified = true;
                        break;
                    case DefinitelyTrue:
                        break;
                    case Undecided:
                        if (! l1)
                            l1 = (v != t[idx]);
                        else if (! l2)
                            l2 = (v != t[idx]);
                    }
                }

                if (! falsified) {
                    if (! l1)
                        inference.contradiction(logger, JustifyUsingRUP{}, generic_reason(state, vars));
                    else if (! l2)
                        inference.infer(logger, *l1, JustifyUsingRUP{}, generic_reason(state, vars));
                }
            }
            return PropagatorState::Enable;
        },
            triggers, "negative table");
    },
        _tuples);
}

auto NegativeTable::s_exprify(const string & name, const innards::ProofModel * const model) const -> std::string
{
    stringstream s;

    print(s, "{} negative_table", name);
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
