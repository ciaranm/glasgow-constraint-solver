#include <gcs/constraints/innards/require_bounded.hh>

#include <util/overloaded.hh>

#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::vector;

auto gcs::innards::require_bounded(const vector<Integer> & values, const char * what) -> void
{
    for (const auto & v : values)
        require_bounded(v, what);
}

auto gcs::innards::require_bounded(const vector<vector<Integer>> & values, const char * what) -> void
{
    for (const auto & row : values)
        require_bounded(row, what);
}

auto gcs::innards::require_bounded(const WeightedSum & sum, const char * what) -> void
{
    for (const auto & term : sum.terms)
        require_bounded(term.coefficient, what);
}

auto gcs::innards::require_bounded(const ExtensionalTuples & tuples, const char * what) -> void
{
    overloaded{
        [&](const ArrayParam<SimpleTuples> & simple) { require_bounded(*simple, what); }, //
        [&](const ArrayParam<WildcardTuples> & wild) {
            for (const auto & row : *wild)
                for (const auto & entry : row)
                    if (const auto * v = std::get_if<Integer>(&entry))
                        require_bounded(*v, what);
        } //
    }
        .visit(tuples);
}

auto gcs::innards::require_bounded(const IntegerVariableCondition & cond, const char * what) -> void
{
    // Up to one past the top of the range: `x <= v` is stored as `x < v + 1`.
    auto check = [&](Integer v) {
        if (v < Integer::min_bounded_value() || v > Integer::max_bounded_value() + 1_i)
            throw_outside_bounded_range(what, v.raw_value);
    };
    check(cond.value);
    if (cond.op == VariableConditionOperator::InRange || cond.op == VariableConditionOperator::NotInRange)
        check(cond.upper_value);
}

auto gcs::innards::require_bounded(const Literal & lit, const char * what) -> void
{
    if (const auto * cond = std::get_if<IntegerVariableCondition>(&lit))
        require_bounded(*cond, what);
}

auto gcs::innards::require_bounded(const Literals & lits, const char * what) -> void
{
    for (const auto & lit : lits)
        require_bounded(lit, what);
}

auto gcs::innards::require_bounded(const ReificationCondition & cond, const char * what) -> void
{
    overloaded{
        [&](const reif::MustHold &) {},                                //
        [&](const reif::MustNotHold &) {},                             //
        [&](const reif::If & c) { require_bounded(c.cond, what); },    //
        [&](const reif::NotIf & c) { require_bounded(c.cond, what); }, //
        [&](const reif::Iff & c) { require_bounded(c.cond, what); }    //
    }
        .visit(cond);
}
