#include <gcs/constraints/table.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
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
using std::unique_ptr;
using std::vector;
using std::visit;

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

auto NegativeTable::install(Propagators & propagators, State &, ProofModel * const optional_model) && -> void
{
    visit([&](auto & tuples) {
        for (auto & tuple : depointinate(tuples))
            if (tuple.size() != _vars.size())
                throw UnexpectedException{"table size mismatch"};

        if (optional_model) {
            for (auto & t : depointinate(tuples)) {
                Literals lits;
                for (const auto & [idx, v] : enumerate(_vars))
                    add_literal(lits, v, t[idx]);
                optional_model->add_constraint("NegativeTable", "forbidden", move(lits));
            }
        }
    },
        _tuples);

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
