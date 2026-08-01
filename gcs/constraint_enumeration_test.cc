#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/innards/variable_id_utils.hh>
#include <gcs/presolver.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <catch2/catch_test_macros.hpp>
#include <catch2/catch_tostring.hpp>

#include <cstddef>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace std::string_literals;

using gcs::innards::debug_string;

using std::make_shared;
using std::make_unique;
using std::nullopt;
using std::optional;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    // How many things a generator yields. Spelled out rather than via
    // ranges::distance so that it says the same thing whether std::generator
    // comes from the standard library or from the polyfill.
    template <typename Range_>
    [[nodiscard]] auto count_of(Range_ && r) -> size_t
    {
        size_t result = 0;
        for ([[maybe_unused]] const auto & item : r)
            ++result;
        return result;
    }

    // A ReificationCondition is variant<MustHold, MustNotHold, If, NotIf, Iff>,
    // and its index is all these tests need to tell the forms apart.
    constexpr size_t must_hold = 0, if_cond = 2, iff_cond = 4;

    // The bits of a linear inequality a difference-logic presolver reads back,
    // flattened so that a test can compare two of them.
    struct SeenLinear final
    {
        string id;
        vector<Weighted<IntegerVariableID>> terms;
        Integer value;
        size_t reif_index;

        [[nodiscard]] auto operator==(const SeenLinear &) const -> bool = default;
    };

    struct SeenComparison final
    {
        string id;
        IntegerVariableID left, right;
        bool or_equal;
        size_t reif_index;

        [[nodiscard]] auto operator==(const SeenComparison &) const -> bool = default;
    };

    // Deliberately takes a const Problem &: enumeration must work on one.
    [[nodiscard]] auto collect_linears(const Problem & problem) -> vector<SeenLinear>
    {
        vector<SeenLinear> result;
        for (const auto & c : problem.each_constraint_of_type<ReifiedLinearInequality>())
            result.push_back(
                SeenLinear{as_string(c.constraint_id()), c.coefficients_and_variables().terms, c.value(), c.reification_condition().index()});
        return result;
    }

    [[nodiscard]] auto collect_comparisons(const Problem & problem) -> vector<SeenComparison>
    {
        vector<SeenComparison> result;
        for (const auto & c : problem.each_constraint_of_type<ReifiedCompareLessThanOrMaybeEqual>())
            result.push_back(
                SeenComparison{as_string(c.constraint_id()), c.left_variable(), c.right_variable(), c.or_equal(), c.reification_condition().index()});
        return result;
    }

    // Blank the constraint identities, for the copied-Problem check: a copy
    // re-posts, and re-posting renumbers.
    template <typename Seen_>
    [[nodiscard]] auto without_ids(vector<Seen_> v) -> vector<Seen_>
    {
        for (auto & s : v)
            s.id.clear();
        return v;
    }

    // Catch2 would otherwise try to stream these, and the generic
    // `operator<<(ostream &, Weighted<Var_>)` does not compile for an
    // IntegerVariableID; go through debug_string instead, which also makes a
    // failure readable.
    [[nodiscard]] auto describe(const SeenLinear & s) -> string
    {
        string result = s.id + ":";
        for (const auto & [coeff, var] : s.terms)
            result += " " + coeff.to_string() + "*" + debug_string(var);
        return result + " <= " + s.value.to_string() + " [reif " + to_string(s.reif_index) + "]";
    }

    [[nodiscard]] auto describe(const SeenComparison & s) -> string
    {
        return s.id + ": " + debug_string(s.left) + (s.or_equal ? " <= " : " < ") + debug_string(s.right) + " [reif " + to_string(s.reif_index) + "]";
    }

    struct MixedProblemVariables final
    {
        SimpleIntegerVariableID x, y, z, w, b, c;
    };

    // A Problem exercising every shape the accessors have to report: several
    // linears and several comparisons, in both the constructor and the
    // expression form, with constant and view operands and with each
    // reification form, interleaved with constraints of other kinds that
    // enumeration must skip. It is satisfiable, and its root propagation does
    // not fail, so that a solve over it actually reaches the presolvers.
    auto build_mixed_problem(Problem & p) -> MixedProblemVariables
    {
        MixedProblemVariables v{.x = p.create_integer_variable(0_i, 10_i, "x"s),
            .y = p.create_integer_variable(0_i, 10_i, "y"s),
            .z = p.create_integer_variable(0_i, 10_i, "z"s),
            .w = p.create_integer_variable(0_i, 10_i, "w"s),
            .b = p.create_integer_variable(0_i, 1_i, "b"s),
            .c = p.create_integer_variable(0_i, 1_i, "c"s)};

        // _1: a two-term difference constraint, posted as a constraint object.
        p.post(LinearLessThanEqual{WeightedSum{} + 1_i * v.x + -1_i * v.y, 3_i});
        // _2: the same shape posted as an expression, which routes through
        // Problem::post(SumLessThanEqual<...>).
        p.post(WeightedSum{} + 1_i * v.y + -1_i * v.z <= 4_i);
        // _3: an equality, not an inequality, so it must not be enumerated.
        p.post(LinearEquality{WeightedSum{} + 1_i * v.x + 1_i * v.y + 1_i * v.z, 12_i});
        // _4: greater-than-equal, which its constructor normalises to a <=.
        p.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * v.z + -1_i * v.x, 2_i});
        // _5: a constant term, which stays a ConstantIntegerVariableID.
        p.post(LinearLessThanEqual{WeightedSum{} + 1_i * v.x + 2_i * 5_c, 15_i});
        // _6 and _7: half-reified and fully reified.
        p.post(LinearLessThanEqualIf{WeightedSum{} + 1_i * v.w + -1_i * v.x, 1_i, v.b == 1_i});
        p.post(LinearLessThanEqualIff{WeightedSum{} + 1_i * v.w + -1_i * v.y, 0_i, v.c == 1_i});

        // _8 to _12: the comparison family, including the swapped and the
        // view-operand forms, and one constraint that is not a comparison.
        p.post(LessThan{v.x, v.y});
        p.post(LessThanEqual{v.y, v.z + 2_i});
        p.post(GreaterThan{v.z, v.x});
        p.post(NotEquals{v.x, v.z});
        p.post(LessThanEqualIff{v.x, 7_c, v.b == 1_i});

        return v;
    }

    // Rebuild a Problem from an existing one by re-posting everything it
    // yields. Variables are recreated in the same order, so their ids line up;
    // constraint ids do not, because post() renumbers.
    auto copy_problem(const Problem & from, Problem & to) -> void
    {
        for (const auto & [id, lower, upper, name] : from.each_variable_with_bounds_and_name()) {
            // Deliberately anonymous: the `_N` names the original handed out to
            // unnamed variables are reserved and cannot be passed back in.
            (void)to.create_integer_variable(lower, upper, nullopt);
        }

        for (const auto & c : from.each_constraint())
            to.post(c);
    }

    // The toy presolver from the issue's validation plan: it drives the whole
    // API, at the point in a solve where a real presolver runs.
    struct RecordingPresolver final : Presolver
    {
        shared_ptr<vector<SeenLinear>> linears;
        shared_ptr<vector<SeenComparison>> comparisons;

        explicit RecordingPresolver(shared_ptr<vector<SeenLinear>> l, shared_ptr<vector<SeenComparison>> c) :
            linears(std::move(l)), comparisons(std::move(c))
        {
        }

        [[nodiscard]] virtual auto run(Problem & problem, innards::Propagators &, innards::State &, innards::ProofLogger * const) -> bool override
        {
            *linears = collect_linears(problem);
            *comparisons = collect_comparisons(problem);
            return true;
        }

        [[nodiscard]] virtual auto clone() const -> unique_ptr<Presolver> override
        {
            return make_unique<RecordingPresolver>(linears, comparisons);
        }
    };

    // Posts a new constraint from inside presolving, for the timing guarantee.
    struct PostingPresolver final : Presolver
    {
        [[nodiscard]] virtual auto run(Problem & problem, innards::Propagators &, innards::State &, innards::ProofLogger * const) -> bool override
        {
            const auto & vars = problem.all_normal_variables();
            problem.post(LinearLessThanEqual{WeightedSum{} + 1_i * vars[0] + -1_i * vars[1], 9_i});
            return true;
        }

        [[nodiscard]] virtual auto clone() const -> unique_ptr<Presolver> override
        {
            return make_unique<PostingPresolver>();
        }
    };
}

namespace Catch
{
    template <>
    struct StringMaker<SeenLinear>
    {
        [[nodiscard]] static auto convert(const SeenLinear & s) -> string
        {
            return describe(s);
        }
    };

    template <>
    struct StringMaker<SeenComparison>
    {
        [[nodiscard]] static auto convert(const SeenComparison & s) -> string
        {
            return describe(s);
        }
    };
}

TEST_CASE("Typed enumeration finds nothing in an empty problem")
{
    Problem p;
    (void)p.create_integer_variable(0_i, 10_i);

    CHECK(collect_linears(p).empty());
    CHECK(collect_comparisons(p).empty());
}

TEST_CASE("Typed enumeration finds a single constraint")
{
    Problem p;
    auto x = p.create_integer_variable(0_i, 10_i);
    auto y = p.create_integer_variable(0_i, 10_i);
    p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x + -1_i * y, 3_i});

    CHECK(collect_linears(p) == vector<SeenLinear>{{"_1", {{1_i, x}, {-1_i, y}}, 3_i, must_hold}});
    CHECK(collect_comparisons(p).empty());
}

TEST_CASE("Typed enumeration recovers every posted argument exactly once")
{
    Problem p;
    auto v = build_mixed_problem(p);

    CHECK(collect_linears(p) ==
        vector<SeenLinear>{
            {"_1", {{1_i, v.x}, {-1_i, v.y}}, 3_i, must_hold},
            {"_2", {{1_i, v.y}, {-1_i, v.z}}, 4_i, must_hold},
            // LinearGreaterThanEqual negates both sides in its constructor.
            {"_4", {{-1_i, v.z}, {1_i, v.x}}, -2_i, must_hold},
            {"_5", {{1_i, v.x}, {2_i, IntegerVariableID{5_c}}}, 15_i, must_hold},
            {"_6", {{1_i, v.w}, {-1_i, v.x}}, 1_i, if_cond},
            {"_7", {{1_i, v.w}, {-1_i, v.y}}, 0_i, iff_cond},
        });

    CHECK(collect_comparisons(p) ==
        vector<SeenComparison>{
            {"_8", v.x, v.y, false, must_hold},
            {"_9", v.y, v.z + 2_i, true, must_hold},
            // GreaterThan{z, x} normalises to x < z.
            {"_10", v.x, v.z, false, must_hold},
            {"_12", v.x, 7_c, true, iff_cond},
        });

    // The reification conditions come back with the right variable attached.
    optional<IntegerVariableCondition> half_reified, fully_reified;
    for (const auto & c : p.each_constraint_of_type<ReifiedLinearInequality>()) {
        if (auto i = std::get_if<reif::If>(&c.reification_condition()))
            half_reified = i->cond;
        if (auto i = std::get_if<reif::Iff>(&c.reification_condition()))
            fully_reified = i->cond;
    }
    CHECK(half_reified == optional<IntegerVariableCondition>{v.b == 1_i});
    CHECK(fully_reified == optional<IntegerVariableCondition>{v.c == 1_i});
}

TEST_CASE("Typed enumeration matches the stored type, not the posted type")
{
    // Problem stores what clone() returns, and every member of these families
    // clones to its family base. Asking for the user-facing type is not an
    // error, it just matches nothing -- which is the documented footgun, so
    // pin it down here.
    Problem p;
    (void)build_mixed_problem(p);

    CHECK(count_of(p.each_constraint_of_type<ReifiedLinearInequality>()) == 6);
    CHECK(count_of(p.each_constraint_of_type<LinearLessThanEqual>()) == 0);
    CHECK(count_of(p.each_constraint_of_type<ReifiedCompareLessThanOrMaybeEqual>()) == 4);
    CHECK(count_of(p.each_constraint_of_type<LessThan>()) == 0);

    // Enumerating the base of everything is each_constraint().
    CHECK(count_of(p.each_constraint_of_type<Constraint>()) == count_of(p.each_constraint()));
    CHECK(count_of(p.each_constraint()) == 12);
}

TEST_CASE("Typed enumeration is stable across a solve")
{
    Problem p;
    (void)build_mixed_problem(p);

    auto linears_before = collect_linears(p);
    auto comparisons_before = collect_comparisons(p);

    auto stats = solve(p, [&](const CurrentState &) -> bool { return true; });
    CHECK(stats.solutions > 0);

    CHECK(collect_linears(p) == linears_before);
    CHECK(collect_comparisons(p) == comparisons_before);

    // And again, after a second search over the same Problem.
    (void)solve(p, [&](const CurrentState &) -> bool { return false; });
    CHECK(collect_linears(p) == linears_before);
    CHECK(collect_comparisons(p) == comparisons_before);
}

TEST_CASE("Typed enumeration is correct on a copied problem")
{
    Problem original;
    (void)build_mixed_problem(original);

    Problem copy;
    copy_problem(original, copy);

    // Constraint ids are freshly assigned by the copy's own post() calls, but
    // everything else, variable handles included, must be identical.
    CHECK(without_ids(collect_linears(copy)) == without_ids(collect_linears(original)));
    CHECK(without_ids(collect_comparisons(copy)) == without_ids(collect_comparisons(original)));
    CHECK(collect_linears(copy) == collect_linears(original));

    // The copy is a working Problem, and enumerating it after solving it still
    // gives the same picture.
    auto before = collect_linears(copy);
    auto stats = solve(copy, [&](const CurrentState &) -> bool { return true; });
    CHECK(stats.solutions > 0);
    CHECK(collect_linears(copy) == before);
}

TEST_CASE("A presolver sees every posted constraint")
{
    Problem p;
    (void)build_mixed_problem(p);

    auto expected_linears = collect_linears(p);
    auto expected_comparisons = collect_comparisons(p);

    auto seen_linears = make_shared<vector<SeenLinear>>();
    auto seen_comparisons = make_shared<vector<SeenComparison>>();
    p.add_presolver(RecordingPresolver{seen_linears, seen_comparisons});

    (void)solve(p, [&](const CurrentState &) -> bool { return true; });

    CHECK(*seen_linears == expected_linears);
    CHECK(*seen_comparisons == expected_comparisons);
}

TEST_CASE("A presolver sees constraints posted by an earlier presolver")
{
    // The documented guarantee: each_constraint() keeps up to date during
    // presolving. (Such a constraint gets no propagator and no OPB row, which
    // is why a presolver that wants propagation installs it rather than
    // posting; that is not what is being checked here.)
    Problem p;
    auto v = build_mixed_problem(p);

    auto seen_linears = make_shared<vector<SeenLinear>>();
    auto seen_comparisons = make_shared<vector<SeenComparison>>();
    p.add_presolver(PostingPresolver{});
    p.add_presolver(RecordingPresolver{seen_linears, seen_comparisons});

    (void)solve(p, [&](const CurrentState &) -> bool { return true; });

    REQUIRE(seen_linears->size() == 7);
    CHECK(seen_linears->back() == SeenLinear{"_13", {{1_i, v.x}, {-1_i, v.y}}, 9_i, must_hold});
}
