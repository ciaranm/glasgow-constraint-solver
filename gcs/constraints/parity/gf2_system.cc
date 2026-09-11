#include <gcs/constraints/parity/gf2_system.hh>
#include <gcs/exception.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <bit>
#include <map>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::countr_zero;
using std::get;
using std::holds_alternative;
using std::map;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::popcount;
using std::size_t;
using std::swap;
using std::vector;
using std::ranges::all_of;

auto GF2Bits::none() const -> bool
{
    return all_of(_words, [](const auto & w) { return 0 == w; });
}

auto GF2Bits::count() const -> size_t
{
    size_t result = 0;
    for (const auto & w : _words)
        result += static_cast<size_t>(popcount(w));
    return result;
}

auto GF2Bits::first_set() const -> optional<size_t>
{
    for (size_t w = 0; w != _words.size(); ++w)
        if (0 != _words[w])
            return w * 64 + static_cast<size_t>(countr_zero(_words[w]));
    return nullopt;
}

auto GF2Bits::set_indices() const -> vector<size_t>
{
    vector<size_t> result;
    for (size_t w = 0; w != _words.size(); ++w) {
        auto bits = _words[w];
        while (0 != bits) {
            result.push_back(w * 64 + static_cast<size_t>(countr_zero(bits)));
            bits &= bits - 1;
        }
    }
    return result;
}

auto gcs::innards::canonical_atom(const IntegerVariableCondition & lit) -> pair<IntegerVariableCondition, bool>
{
    switch (lit.op) {
        using enum VariableConditionOperator;
    case Equal:
    case GreaterEqual:
    case InRange: return {lit, false};
    case NotEqual: return {IntegerVariableCondition{lit.var, Equal, lit.value, lit.upper_value}, true};
    case Less: return {IntegerVariableCondition{lit.var, GreaterEqual, lit.value, lit.upper_value}, true};
    case NotInRange: return {IntegerVariableCondition{lit.var, InRange, lit.value, lit.upper_value}, true};
    }
    throw NonExhaustiveSwitch{};
}

auto gcs::innards::build_gf2_system(const vector<Literals> & posted_rows) -> GF2System
{
    // Two passes: the first finds the columns, because a row cannot be built
    // until the width is known.
    map<IntegerVariableCondition, size_t> column_of;
    GF2System result;
    for (const auto & row : posted_rows)
        for (const auto & lit : row)
            if (holds_alternative<IntegerVariableCondition>(lit)) {
                auto atom = canonical_atom(get<IntegerVariableCondition>(lit)).first;
                if (column_of.emplace(atom, result.atoms.size()).second)
                    result.atoms.push_back(atom);
            }

    for (const auto & [r, posted] : enumerate(posted_rows)) {
        GF2Row row{GF2Bits{result.atoms.size()}, GF2Bits{posted_rows.size()}, true};
        row.origin.set(r);
        for (const auto & lit : posted)
            overloaded{//
                [&](const IntegerVariableCondition & cond) {
                    auto [atom, negated] = canonical_atom(cond);
                    // XOR rather than set: a repeated atom cancels, which is
                    // exactly what `x XOR x = 0` says, and a negated literal is
                    // its atom plus a flip of the right-hand side.
                    row.atoms.flip(column_of.at(atom));
                    if (negated)
                        row.rhs = ! row.rhs;
                },
                [&](const TrueLiteral &) { row.rhs = ! row.rhs; }, [&](const FalseLiteral &) {}}
                .visit(lit);
        result.rows.push_back(move(row));
    }

    return result;
}

auto gcs::innards::gauss_jordan(vector<GF2Row> & rows, size_t n_atoms) -> size_t
{
    size_t rank = 0;
    for (size_t col = 0; col != n_atoms && rank != rows.size(); ++col) {
        auto pivot = rows.size();
        for (size_t r = rank; r != rows.size(); ++r)
            if (rows[r].atoms.test(col)) {
                pivot = r;
                break;
            }
        if (pivot == rows.size())
            continue;

        swap(rows[rank], rows[pivot]);
        for (size_t r = 0; r != rows.size(); ++r)
            if (r != rank && rows[r].atoms.test(col)) {
                rows[r].atoms ^= rows[rank].atoms;
                rows[r].origin ^= rows[rank].origin;
                rows[r].rhs = rows[r].rhs != rows[rank].rhs;
            }
        ++rank;
    }
    return rank;
}
