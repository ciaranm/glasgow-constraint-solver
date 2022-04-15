/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/table.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <algorithm>
#include <functional>
#include <list>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <type_traits>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::pair;
using std::string;
using std::vector;
using std::visit;

Table::Table(const vector<IntegerVariableID> & v, ExtensionalTuples && t) :
    _vars(v),
    _tuples(move(t))
{
}

auto Table::install(Propagators & propagators, const State & initial_state) && -> void
{
    visit([&](auto & tuples) {
        for (auto & tuple : tuples)
            if (tuple.size() != _vars.size())
                throw UnexpectedException{"table size mismatch"};
    },
        _tuples);

    propagators.define_and_install_table(initial_state, vector<IntegerVariableID>{_vars}, move(_tuples), "table");
}

auto Table::describe_for_proof() -> string
{
    return "table";
}

NegativeTable::NegativeTable(const vector<IntegerVariableID> & v, ExtensionalTuples && t) :
    _vars(v),
    _tuples(move(t))
{
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

auto NegativeTable::install(Propagators & propagators, const State & initial_state) && -> void
{
    visit([&](auto & tuples) {
        for (auto & tuple : tuples)
            if (tuple.size() != _vars.size())
                throw UnexpectedException{"table size mismatch"};

        if (propagators.want_definitions()) {
            for (auto & t : tuples) {
                Literals lits;
                for (const auto & [idx, v] : enumerate(_vars))
                    add_literal(lits, v, t[idx]);
                propagators.define_cnf(initial_state, move(lits));
            }
        }
    },
        _tuples);

    Triggers triggers;
    for (auto & v : _vars)
        triggers.on_change.emplace_back(v);

    visit([&](const auto & tuples) {
        propagators.install(
            initial_state, [vars = move(_vars), tuples = move(tuples)](State & state) -> pair<Inference, PropagatorState> {
                auto inf = Inference::NoChange;
                for (auto & t : tuples) {
                    bool falsified = false;
                    optional<Literal> l1, l2;
                    for (const auto & [idx, v] : enumerate(vars)) {
                        switch (state.test_literal(v == t[idx])) {
                        case LiteralIs::DefinitelyFalse:
                            falsified = true;
                            break;
                        case LiteralIs::DefinitelyTrue:
                            break;
                        case LiteralIs::Undecided:
                            if (! l1)
                                l1 = (v != t[idx]);
                            else if (! l2)
                                l2 = (v != t[idx]);
                        }
                    }

                    if (! falsified) {
                        if (! l1)
                            return pair{Inference::Contradiction, PropagatorState::Enable};
                        else if (! l2)
                            increase_inference_to(inf, state.infer(*l1, JustifyUsingRUP{}));
                    }
                }
                return pair{inf, PropagatorState::Enable};
            },
            triggers, "negative table");
    },
        _tuples);
}

auto NegativeTable::describe_for_proof() -> string
{
    return "negative table";
}
