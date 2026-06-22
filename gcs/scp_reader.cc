#include <gcs/constraints/abs.hh>
#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/all_equal.hh>
#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/count.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/in.hh>
#include <gcs/constraints/increasing.hh>
#include <gcs/constraints/inverse.hh>
#include <gcs/constraints/linear/linear_equality.hh>
#include <gcs/constraints/linear/linear_inequality.hh>
#include <gcs/constraints/logical.hh>
#include <gcs/constraints/min_max.hh>
#include <gcs/constraints/minus.hh>
#include <gcs/constraints/n_value.hh>
#include <gcs/constraints/parity.hh>
#include <gcs/constraints/plus.hh>
#include <gcs/expression.hh>
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
    MessageException("Error reading .scp: " + w)
{
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
        // cake_pb_cp's condition operators are symbols.
        if (op == "=")
            return {var, Equal, value};
        if (op == "!=")
            return {var, NotEqual, value};
        if (op == ">=")
            return {var, GreaterEqual, value};
        if (op == "<")
            return {var, Less, value};
        throw ScpReadError{"unknown reification-condition operator '" + op + "'"};
    }

    // For the equals-style families (equals / not_equals and their lin_
    // counterparts): map a keyword's reification suffix to a (condition, flipped)
    // pair. `flipped` is the cosmetic not-equals-iff flag (ReifiedEquals::_neq /
    // ReifiedLinearEquality::_flipped_cond). `cond_term` is only read when the
    // form is reified (the (variable op value) triple).
    auto equality_reification(bool not_equals, bool iff, bool half,
        const map<string, IntegerVariableID> & variables, const SExpr & cond_term) -> std::pair<ReificationCondition, bool>
    {
        if (iff)
            return {ReificationCondition{reif::Iff{resolve_condition(variables, cond_term)}}, not_equals};
        if (half)
            return {not_equals ? ReificationCondition{reif::NotIf{resolve_condition(variables, cond_term)}}
                               : ReificationCondition{reif::If{resolve_condition(variables, cond_term)}},
                false};
        return {not_equals ? ReificationCondition{reif::MustNotHold{}} : ReificationCondition{reif::MustHold{}}, false};
    }

    // The comparison family: (label <less|greater>_<than|equal>[_if|_iff]
    // [(cond)] v1 v2), in cake_pb_cp's names. The keyword carries the swapped /
    // or-equal / reification flags that the general
    // ReifiedCompareLessThanOrMaybeEqual constructor takes directly, so this
    // reconstructs exactly the object the writer serialised.
    auto read_comparison(Problem & problem, const map<string, IntegerVariableID> & variables,
        const string & op, const vector<SExpr> & terms, const string & label) -> void
    {
        bool vars_swapped = op.starts_with("greater_");
        string rest = op.substr(vars_swapped ? sizeof("greater_") - 1 : sizeof("less_") - 1);
        bool or_equal = rest.starts_with("equal");
        rest = rest.substr(or_equal ? sizeof("equal") - 1 : sizeof("than") - 1);
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

        // "less A B" means A <op> B; "greater A B" means A >op B, i.e. B <op A.
        // The base constructor enforces (first) <op> (second), so reverse the
        // operands for the greater form to recover that.
        auto first = resolve_variable(variables, terms[v1_index]);
        auto second = resolve_variable(variables, terms[v1_index + 1]);
        post_constraint(problem,
            ReifiedCompareLessThanOrMaybeEqual{
                vars_swapped ? second : first,
                vars_swapped ? first : second,
                cond, or_equal, vars_swapped},
            label);
    }

    // The linear family: (label lin_<equals|not_equals|lin_less_equal>[_if|_iff]
    // [(cond)] (c1 v1 c2 v2 ...) value). The keyword selects the constraint and
    // its reification, matching the general ReifiedLinear* constructors. (The
    // .scp does not record the GAC flag, so it defaults off; that affects
    // propagation strength, not the solution set or the written .scp.)
    auto read_linear(Problem & problem, const map<string, IntegerVariableID> & variables,
        const string & op, const vector<SExpr> & terms, const string & label) -> void
    {
        bool iff = op.ends_with("_iff");
        bool half = ! iff && op.ends_with("_if");
        bool reified = iff || half;

        if (terms.size() != (reified ? 5u : 4u))
            throw ScpReadError{"linear constraint '" + op + "' has the wrong number of parts"};

        const auto & pairs = children_of(terms[reified ? 3 : 2], "the linear coefficient/variable list");
        if (pairs.size() % 2 != 0)
            throw ScpReadError{"the linear coefficient/variable list must alternate coefficient and variable"};
        WeightedSum coeff_vars;
        for (std::size_t i = 0; i + 1 < pairs.size(); i += 2)
            coeff_vars += as_integer(pairs[i]) * resolve_variable(variables, pairs[i + 1]);
        auto value = as_integer(terms[reified ? 4 : 3]);

        auto condition = [&] { return resolve_condition(variables, terms[2]); };

        if (op.starts_with("lin_less_equal")) {
            ReificationCondition cond = reif::MustHold{};
            if (iff)
                cond = reif::Iff{condition()};
            else if (half)
                cond = reif::If{condition()};
            post_constraint(problem, ReifiedLinearInequality{std::move(coeff_vars), value, cond}, label);
            return;
        }

        // Equality family: lin_equals* and lin_not_equals*.
        auto [cond, flipped_cond] = equality_reification(op.starts_with("lin_not_equals"), iff, half, variables, terms[2]);
        post_constraint(problem, ReifiedLinearEquality{std::move(coeff_vars), value, cond, false, flipped_cond}, label);
    }

    // The equals family: (label <equals|not_equals>[_if|_iff] [(cond)] v1 v2),
    // reconstructed via the general ReifiedEquals constructor.
    auto read_equals(Problem & problem, const map<string, IntegerVariableID> & variables,
        const string & op, const vector<SExpr> & terms, const string & label) -> void
    {
        bool iff = op.ends_with("_iff");
        bool half = ! iff && op.ends_with("_if");
        bool reified = iff || half;

        if (terms.size() != (reified ? 5u : 4u))
            throw ScpReadError{"equals constraint '" + op + "' is (label op [(cond)] v1 v2)"};
        std::size_t v1_index = reified ? 3 : 2;

        auto [cond, neq] = equality_reification(op.starts_with("not_equals"), iff, half, variables, terms[2]);
        post_constraint(problem,
            ReifiedEquals{resolve_variable(variables, terms[v1_index]), resolve_variable(variables, terms[v1_index + 1]), cond, neq},
            label);
    }
}

auto gcs::read_scp(Problem & problem, string_view text) -> map<string, IntegerVariableID>
{
    auto top = parse_s_expr(text);
    const auto & sections = children_of(top, "the top-level (variables constraints [objective]) form");
    // The optional third element is the objective / (enumerate) directive; this
    // reader solves and enumerates, so it is accepted but not acted on (an
    // objective would need the client to optimise rather than enumerate).
    if (sections.size() != 2 && sections.size() != 3)
        throw ScpReadError{"top level must be (variables constraints) or (variables constraints objective)"};

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
        else if (op == "all_equal") {
            if (terms.size() != 3)
                throw ScpReadError{"all_equal takes one list: (label all_equal (vars...))"};
            post_constraint(problem, AllEqual{resolve_variable_list(variables, terms[2], "the all_equal variable list")}, label);
        }
        else if (op == "circuit") {
            if (terms.size() != 3)
                throw ScpReadError{"circuit takes one list: (label circuit (succ...))"};
            post_constraint(problem, Circuit{resolve_variable_list(variables, terms[2], "the circuit successor list")}, label);
        }
        else if (op == "array_min" || op == "array_max") {
            // (label array_min (vars...) result): result = min/max of the array.
            if (terms.size() != 4)
                throw ScpReadError{"the array aggregate takes a list and a result: (label " + op + " (vars...) result)"};
            auto vars = resolve_variable_list(variables, terms[2], "the array aggregate variable list");
            auto result = resolve_variable(variables, terms[3]);
            if (op == "array_min")
                post_constraint(problem, ArrayMin{move(vars), result}, label);
            else
                post_constraint(problem, ArrayMax{move(vars), result}, label);
        }
        else if (op == "increasing" || op == "strictly_increasing" || op == "decreasing" || op == "strictly_decreasing") {
            // The keyword carries the strict / descending flags that IncreasingChain
            // takes directly (the inverse of how the writer derives the keyword).
            if (terms.size() != 3)
                throw ScpReadError{"the increasing family takes one list: (label " + op + " (vars...))"};
            post_constraint(problem,
                IncreasingChain{resolve_variable_list(variables, terms[2], "the increasing variable list"),
                    op.starts_with("strictly_"), op.ends_with("decreasing")},
                label);
        }
        else if (op == "in") {
            if (terms.size() != 4)
                throw ScpReadError{"in takes a list and a variable: (label in (values...) var)"};
            // The value list is just a list of variables; an integer value is a
            // ConstantIntegerVariableID, which In folds back into a constant. The
            // list comes first, then the variable, matching cake_pb_cp's parser.
            post_constraint(problem,
                In{resolve_variable(variables, terms[3]), resolve_variable_list(variables, terms[2], "the in value list")}, label);
        }
        else if (op == "element") {
            // (label element (X0 ... Xn-1) (index off) result): result = Xs[index - off].
            if (terms.size() != 5)
                throw ScpReadError{"element takes (label element (array...) (index off) result)"};
            const auto & index_pair = children_of(terms[3], "the element index");
            if (index_pair.size() != 2)
                throw ScpReadError{"the element index must be (index off)"};
            // Element takes an ArrayParam, so hand it the array by value: the
            // constraint owns it (no external storage to keep alive).
            post_constraint(problem,
                Element{resolve_variable(variables, terms[4]),
                    std::pair{resolve_variable(variables, index_pair[0]), as_integer(index_pair[1])},
                    resolve_variable_list(variables, terms[2], "the element array")},
                label);
        }
        else if (op == "count") {
            // (label count (X1 ... Xn) value how_many): how_many = #{ i : Xi = value }.
            if (terms.size() != 5)
                throw ScpReadError{"count takes (label count (vars...) value how_many)"};
            post_constraint(problem,
                Count{resolve_variable_list(variables, terms[2], "the count variable list"),
                    resolve_variable(variables, terms[3]), resolve_variable(variables, terms[4])},
                label);
        }
        else if (op == "nvalue") {
            // (label nvalue (X1 ... Xn) Y): Y = #{ distinct values among the Xi }.
            if (terms.size() != 4)
                throw ScpReadError{"nvalue takes (label nvalue (vars...) n_values)"};
            post_constraint(problem,
                NValue{resolve_variable(variables, terms[3]),
                    resolve_variable_list(variables, terms[2], "the nvalue variable list")},
                label);
        }
        else if (op == "inverse") {
            // (label inverse ((X...) offx) ((Y...) offy)): X[i]=j+offy <-> Y[j]=i+offx.
            if (terms.size() != 4)
                throw ScpReadError{"inverse takes (label inverse ((X...) offx) ((Y...) offy))"};
            const auto & a = children_of(terms[2], "the inverse X group");
            const auto & b = children_of(terms[3], "the inverse Y group");
            if (a.size() != 2 || b.size() != 2)
                throw ScpReadError{"each inverse group is ((vars...) offset)"};
            post_constraint(problem,
                Inverse{resolve_variable_list(variables, a[0], "the inverse X list"),
                    resolve_variable_list(variables, b[0], "the inverse Y list"),
                    as_integer(a[1]), as_integer(b[1])},
                label);
        }
        else if (op == "and") {
            // (label and (X1 ... Xn) Y): Y <-> all Xi nonzero.
            if (terms.size() != 4)
                throw ScpReadError{"and takes (label and (vars...) reif)"};
            post_constraint(problem,
                And{resolve_variable_list(variables, terms[2], "the and variable list"),
                    resolve_variable(variables, terms[3])},
                label);
        }
        else if (op == "or") {
            // (label or (X1 ... Xn) Y): Y <-> some Xi nonzero.
            if (terms.size() != 4)
                throw ScpReadError{"or takes (label or (vars...) reif)"};
            post_constraint(problem,
                Or{resolve_variable_list(variables, terms[2], "the or variable list"),
                    resolve_variable(variables, terms[3])},
                label);
        }
        else if (op == "parity") {
            // (label parity (X1 ... Xn) Y): cake encodes Y = XOR(Xi). The solver
            // only has the bare odd-parity constraint (ParityOdd, XOR(Xi) = 1),
            // which it writes with the constant Y = 1, so require that here.
            if (terms.size() != 4)
                throw ScpReadError{"parity takes (label parity (vars...) 1)"};
            if (as_integer(terms[3]) != Integer{1})
                throw ScpReadError{"parity Y must be the constant 1 (only bare odd parity is supported)"};
            post_constraint(problem,
                ParityOdd{resolve_variable_list(variables, terms[2], "the parity variable list")},
                label);
        }
        else if (op == "plus") {
            // (label plus a b result): a + b = result.
            if (terms.size() != 5)
                throw ScpReadError{"plus takes (label plus a b result)"};
            post_constraint(problem,
                Plus{resolve_variable(variables, terms[2]), resolve_variable(variables, terms[3]),
                    resolve_variable(variables, terms[4])},
                label);
        }
        else if (op == "minus") {
            // (label minus a b result): a - b = result.
            if (terms.size() != 5)
                throw ScpReadError{"minus takes (label minus a b result)"};
            post_constraint(problem,
                Minus{resolve_variable(variables, terms[2]), resolve_variable(variables, terms[3]),
                    resolve_variable(variables, terms[4])},
                label);
        }
        else if (op.starts_with("less_") || op.starts_with("greater_")) {
            read_comparison(problem, variables, op, terms, label);
        }
        else if (op.starts_with("lin_")) {
            read_linear(problem, variables, op, terms, label);
        }
        else if (op.starts_with("equals") || op.starts_with("not_equals")) {
            read_equals(problem, variables, op, terms, label);
        }
        else
            throw ScpReadError{"unsupported constraint operator '" + op + "'"};
    }

    return variables;
}
