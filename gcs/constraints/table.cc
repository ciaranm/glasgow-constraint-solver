/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/table.hh>
#include <gcs/low_level_constraint_store.hh>
#include <gcs/state.hh>
#include <gcs/exception.hh>

#include <util/for_each.hh>

#include <algorithm>
#include <functional>
#include <list>
#include <map>
#include <set>
#include <sstream>
#include <type_traits>
#include <utility>
#include <variant>

using namespace gcs;

using std::string;
using std::vector;

Table::Table(const vector<IntegerVariableID> & v, vector<vector<Integer> > && t) :
    _vars(v),
    _tuples(move(t))
{
}

auto Table::convert_to_low_level(LowLevelConstraintStore & constraints, const State & initial_state) && -> void
{
    for (auto & tuple : _tuples)
        if (tuple.size() != _vars.size())
            throw UnexpectedException{ "table size mismatch" };

    constraints.table(initial_state, vector<IntegerVariableID>{ _vars }, move(_tuples));
}

auto Table::describe_for_proof() -> string
{
    return "table";
}

