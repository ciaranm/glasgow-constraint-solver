#include <gcs/constraints/abs.hh>
#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/in.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/problem.hh>
#include <gcs/scp_reader.hh>

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

    // Resolve an argument atom to a variable: a declared name, otherwise an
    // integer constant.
    auto resolve = [&](const SExpr & e) -> IntegerVariableID {
        const auto & a = e.as_atom();
        if (auto it = variables.find(a); it != variables.end())
            return it->second;
        return constant_variable(as_integer(e));
    };

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
            post_constraint(problem, Abs{resolve(terms[2]), resolve(terms[3])}, label);
        }
        else if (op == "all_different") {
            if (terms.size() != 3)
                throw ScpReadError{"all_different takes one list: (label all_different (vars...))"};
            vector<IntegerVariableID> vars;
            for (const auto & v : children_of(terms[2], "the all_different variable list"))
                vars.push_back(resolve(v));
            post_constraint(problem, AllDifferent{move(vars)}, label);
        }
        else if (op == "in") {
            if (terms.size() != 4)
                throw ScpReadError{"in takes a variable and a list: (label in var (values...))"};
            auto var = resolve(terms[2]);
            vector<IntegerVariableID> var_values;
            vector<Integer> int_values;
            for (const auto & v : children_of(terms[3], "the in value list")) {
                const auto & a = v.as_atom();
                if (auto it = variables.find(a); it != variables.end())
                    var_values.push_back(it->second);
                else
                    int_values.push_back(as_integer(v));
            }
            post_constraint(problem, In{var, move(var_values), move(int_values)}, label);
        }
        else
            throw ScpReadError{"unsupported constraint operator '" + op + "'"};
    }

    return variables;
}
