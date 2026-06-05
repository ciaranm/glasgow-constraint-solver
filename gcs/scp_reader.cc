#include <gcs/constraints/abs.hh>
#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/in.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/problem.hh>
#include <gcs/reification.hh>
#include <gcs/scp_reader.hh>
#include <gcs/variable_condition.hh>

#include <charconv>
#include <optional>
#include <utility>

using std::map;
using std::move;
using std::string;
using std::string_view;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

ScpReadError::ScpReadError(const string & w) :
    _wat("Error reading .scp: " + w)
{
}

auto ScpReadError::what() const noexcept -> const char *
{
    return _wat.c_str();
}

namespace
{
    auto as_integer(const SExpr & e) -> Integer
    {
        const auto & a = e.as_atom();
        long long value;
        auto [ptr, ec] = std::from_chars(a.data(), a.data() + a.size(), value);
        if (ec != std::errc{} || ptr != a.data() + a.size())
            throw ScpReadError{"expected an integer, got '" + a + "'"};
        return Integer{value};
    }

    // The children of a list term, or a clear error if `e` is an atom. `what`
    // is taken by value (not const string &) so the -Wdangling-reference
    // heuristic doesn't flag the returned reference, which is into `e`.
    auto children_of(const SExpr & e, const char * what) -> const vector<SExpr> &
    {
        if (! e.is_list())
            throw ScpReadError{string{"expected a list for "} + what};
        return e.as_list();
    }

    // Resolve an argument to a variable: a declared name, or an integer constant
    // mapped to a ConstantIntegerVariableID. Anywhere a variable name may appear
    // in a .scp, a constant integer may appear in its place.
    auto resolve_variable(const map<string, IntegerVariableID> & variables, const SExpr & e) -> IntegerVariableID
    {
        const auto & a = e.as_atom();
        if (auto it = variables.find(a); it != variables.end())
            return it->second;
        return constant_variable(as_integer(e));
    }

    // Resolve a list term to a vector of variables (the common case).
    auto resolve_variable_list(const map<string, IntegerVariableID> & variables, const SExpr & list, const char * what) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> result;
        for (const auto & e : children_of(list, what))
            result.push_back(resolve_variable(variables, e));
        return result;
    }

    // If `s` is the form Problem auto-generates for unnamed constraints,
    // `_<digits>`, return that number; otherwise nullopt.
    auto auto_number_of(const string & s) -> std::optional<unsigned long long>
    {
        if (s.size() < 2 || s[0] != '_')
            return std::nullopt;
        for (auto i = s.begin() + 1; i != s.end(); ++i)
            if (*i < '0' || *i > '9')
                return std::nullopt;
        unsigned long long number;
        auto [ptr, ec] = std::from_chars(s.data() + 1, s.data() + s.size(), number);
        if (ec != std::errc{})
            throw ScpReadError{"constraint label '" + s + "' is out of range"};
        return number;
    }

    auto post_constraint(Problem & problem, const Constraint & constraint, const string & label) -> void
    {
        // `_N` is reserved (post_named rejects it); reproduce it via
        // post_autonumbered, which validates the number lines up. Anything else
        // is a genuine name.
        if (auto number = auto_number_of(label))
            problem.post_autonumbered(constraint, *number);
        else
            problem.post_named(constraint, label);
    }

    // A reification condition is the triple (variable op value), where op is the
    // s_expr_name_of(VariableConditionOperator) spelling.
    auto resolve_condition(const map<string, IntegerVariableID> & variables, const SExpr & triple) -> IntegerVariableCondition
    {
        const auto & parts = children_of(triple, "a reification condition");
        if (parts.size() != 3)
            throw ScpReadError{"a reification condition must be (variable op value)"};
        auto var = resolve_variable(variables, parts[0]);
        const auto & op = parts[1].as_atom();
        auto value = as_integer(parts[2]);
        using enum VariableConditionOperator;
        if (op == "eq")
            return {var, Equal, value};
        if (op == "neq")
            return {var, NotEqual, value};
        if (op == "geq")
            return {var, GreaterEqual, value};
        if (op == "lt")
            return {var, Less, value};
        throw ScpReadError{"unknown reification-condition operator '" + op + "'"};
    }

    // The comparison family: (label <less|greater>_than[_equal][_if|_iff]
    // [(cond)] v1 v2). The keyword carries the swapped / or-equal / reification
    // flags that the general ReifiedCompareLessThanOrMaybeEqual constructor takes
    // directly, so this reconstructs exactly the object the writer serialised.
    auto read_comparison(Problem & problem, const map<string, IntegerVariableID> & variables,
        const string & op, const vector<SExpr> & terms, const string & label) -> void
    {
        bool vars_swapped = op.starts_with("greater_than");
        string rest = op.substr(vars_swapped ? sizeof("greater_than") - 1 : sizeof("less_than") - 1);
        bool or_equal = rest.starts_with("_equal");
        if (or_equal)
            rest = rest.substr(sizeof("_equal") - 1);
        // `rest` is now "" (unconditional), "_if" (half-reified) or "_iff".

        ReificationCondition cond = reif::MustHold{};
        std::size_t v1_index = 2;
        if (rest.empty()) {
            if (terms.size() != 4)
                throw ScpReadError{"comparison '" + op + "' is (label op v1 v2)"};
        }
        else {
            if (terms.size() != 5)
                throw ScpReadError{"reified comparison '" + op + "' is (label op (cond) v1 v2)"};
            auto condition = resolve_condition(variables, terms[2]);
            if (rest == "_if")
                cond = reif::If{condition};
            else if (rest == "_iff")
                cond = reif::Iff{condition};
            else
                throw ScpReadError{"unknown comparison '" + op + "'"};
            v1_index = 3;
        }

        post_constraint(problem,
            ReifiedCompareLessThanOrMaybeEqual{
                resolve_variable(variables, terms[v1_index]),
                resolve_variable(variables, terms[v1_index + 1]),
                cond, or_equal, vars_swapped},
            label);
    }
}

auto gcs::read_scp(Problem & problem, string_view text) -> map<string, IntegerVariableID>
{
    auto top = parse_s_expr(text);
    const auto & sections = children_of(top, "the top-level (variables constraints) form");
    if (sections.size() != 2)
        throw ScpReadError{"top level must be exactly (variables constraints)"};

    map<string, IntegerVariableID> variables;

    // Variables: each declaration is (name lower upper).
    for (const auto & decl : children_of(sections[0], "the variables section")) {
        const auto & parts = children_of(decl, "a variable declaration");
        if (parts.size() != 3)
            throw ScpReadError{"a variable declaration must be (name lower upper)"};
        auto name = parts[0].as_atom();
        auto var = problem.create_integer_variable(as_integer(parts[1]), as_integer(parts[2]), name);
        if (! variables.emplace(name, var).second)
            throw ScpReadError{"duplicate variable name '" + name + "'"};
    }

    // Constraints: each is (label operator args...).
    for (const auto & constraint : children_of(sections[1], "the constraints section")) {
        const auto & terms = children_of(constraint, "a constraint");
        if (terms.size() < 2)
            throw ScpReadError{"a constraint must be (label operator ...)"};
        const auto & label = terms[0].as_atom();
        const auto & op = terms[1].as_atom();

        if (op == "abs") {
            if (terms.size() != 4)
                throw ScpReadError{"abs takes two operands: (label abs v1 v2)"};
            post_constraint(problem, Abs{resolve_variable(variables, terms[2]), resolve_variable(variables, terms[3])}, label);
        }
        else if (op == "all_different") {
            if (terms.size() != 3)
                throw ScpReadError{"all_different takes one list: (label all_different (vars...))"};
            post_constraint(problem, AllDifferent{resolve_variable_list(variables, terms[2], "the all_different variable list")}, label);
        }
        else if (op == "in") {
            if (terms.size() != 4)
                throw ScpReadError{"in takes a variable and a list: (label in var (values...))"};
            // The value list is just a list of variables; an integer value is a
            // ConstantIntegerVariableID, which In folds back into a constant.
            post_constraint(problem,
                In{resolve_variable(variables, terms[2]), resolve_variable_list(variables, terms[3], "the in value list")}, label);
        }
        else if (op.starts_with("less_than") || op.starts_with("greater_than")) {
            read_comparison(problem, variables, op, terms, label);
        }
        else
            throw ScpReadError{"unsupported constraint operator '" + op + "'"};
    }

    return variables;
}
