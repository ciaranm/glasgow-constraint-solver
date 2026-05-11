#include <gcs/constraints/table/negative_table.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <cstddef>
#include <limits>
#include <memory>
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

using std::make_shared;
using std::nullopt;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::stringstream;
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

NegativeTable::NegativeTable(vector<IntegerVariableID> v, ExtensionalTuples t) :
    _vars(move(v)),
    _tuples(move(t))
{
}

auto NegativeTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<NegativeTable>(_vars, ExtensionalTuples{_tuples});
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

namespace
{
    constexpr size_t no_watch = std::numeric_limits<size_t>::max();
}

auto NegativeTable::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (auto & v : _vars)
        triggers.on_change.emplace_back(v);

    // Watches are non-backtrackable: when a watch moves during search, leaving it moved
    // after backtrack is sound (the new position is still a valid watch — its literal
    // can only become "more not-false" as the state relaxes) and avoids restoration
    // overhead. Using shared_ptr so the initialiser and main propagator share storage.
    auto watches = make_shared<vector<pair<size_t, size_t>>>();

    visit([&, this](auto && tuples) {
        // Init: walk every tuple, find two watch positions, propagate units, raise
        // contradictions. A position is unusable as a watch iff `var == t[pos]` is
        // currently DefinitelyTrue — this captures both the "var is forced to t[pos]"
        // case and the "t[pos] is a wildcard" case (since `var == Wildcard` overloads
        // to TrueLiteral, which tests as DefinitelyTrue).
        propagators.install_initialiser(
            [vars = _vars, tuples = tuples, watches = watches](
                const State & state, auto & inference, ProofLogger * const logger) -> void {
                const auto & tuple_data = depointinate(tuples);
                watches->reserve(tuple_data.size());

                for (size_t ti = 0; ti < tuple_data.size(); ++ti) {
                    const auto & t = tuple_data[ti];

                    auto find_unbroken = [&](size_t skip) -> optional<size_t> {
                        for (size_t p = 0; p < vars.size(); ++p) {
                            if (p == skip)
                                continue;
                            if (state.test_literal(vars[p] == t[p]) != LiteralIs::DefinitelyTrue)
                                return p;
                        }
                        return nullopt;
                    };

                    auto w1 = find_unbroken(no_watch);
                    if (! w1) {
                        inference.contradiction(logger, JustifyUsingRUP{},
                            generic_reason(state, vars));
                    }

                    auto w2 = find_unbroken(*w1);
                    if (! w2) {
                        // Unit clause: vars[*w1] != t[*w1] is the only possibly-true
                        // disjunct, so it must hold.
                        inference.infer(logger, vars[*w1] != t[*w1], JustifyUsingRUP{},
                            generic_reason(state, vars));
                        // Mark the tuple as already handled — both watches at the same
                        // position will read as broken on every subsequent fire, and
                        // any rescue search will discover the inference is now redundant.
                        watches->emplace_back(*w1, *w1);
                    }
                    else {
                        watches->emplace_back(*w1, *w2);
                    }
                }
            });

        propagators.install(
            [vars = move(_vars), tuples = move(tuples), watches = watches](
                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                const auto & tuple_data = depointinate(tuples);

                auto is_broken = [&](const auto & t, size_t p) -> bool {
                    return state.test_literal(vars[p] == t[p]) == LiteralIs::DefinitelyTrue;
                };

                auto find_unbroken = [&](const auto & t, size_t skip1, size_t skip2) -> optional<size_t> {
                    for (size_t p = 0; p < vars.size(); ++p) {
                        if (p == skip1 || p == skip2)
                            continue;
                        if (state.test_literal(vars[p] == t[p]) != LiteralIs::DefinitelyTrue)
                            return p;
                    }
                    return nullopt;
                };

                for (size_t ti = 0; ti < tuple_data.size(); ++ti) {
                    auto & w = (*watches)[ti];
                    const auto & t = tuple_data[ti];

                    bool b1 = is_broken(t, w.first);
                    bool b2 = is_broken(t, w.second);

                    if (! b1 && ! b2)
                        continue;

                    if (b1 && b2) {
                        auto new1 = find_unbroken(t, no_watch, no_watch);
                        if (! new1) {
                            inference.contradiction(logger, JustifyUsingRUP{},
                                generic_reason(state, vars));
                        }
                        auto new2 = find_unbroken(t, *new1, no_watch);
                        if (! new2) {
                            inference.infer(logger, vars[*new1] != t[*new1], JustifyUsingRUP{},
                                generic_reason(state, vars));
                        }
                        else {
                            w.first = *new1;
                            w.second = *new2;
                        }
                    }
                    else if (b1) {
                        auto new1 = find_unbroken(t, w.second, no_watch);
                        if (! new1) {
                            inference.infer(logger, vars[w.second] != t[w.second], JustifyUsingRUP{},
                                generic_reason(state, vars));
                        }
                        else {
                            w.first = *new1;
                        }
                    }
                    else {
                        auto new2 = find_unbroken(t, w.first, no_watch);
                        if (! new2) {
                            inference.infer(logger, vars[w.first] != t[w.first], JustifyUsingRUP{},
                                generic_reason(state, vars));
                        }
                        else {
                            w.second = *new2;
                        }
                    }
                }
                return PropagatorState::Enable;
            },
            triggers);
    },
        _tuples);
}

auto NegativeTable::s_exprify(const innards::ProofModel * const model) const -> std::string
{
    stringstream s;

    print(s, "{} negative_table", _name);
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
