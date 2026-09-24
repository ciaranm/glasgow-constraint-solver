/* Multiply, Divide, Modulus and Power over operands whose corner products
 * leave Integer's range (issue #1064). Each of these threw IntegerOverflow
 * from product_bounds during propagation, even where every solution is small.
 *
 * Proofs are off throughout: at these widths the proof model's bit-product
 * grid cannot be written (its largest sum does not fit in an Integer), which
 * is the proof side's own limit. The instances are built so that the solutions
 * can be listed directly, and the solver's are compared with that list.
 */

#include <gcs/constraints/divide.hh>
#include <gcs/constraints/multiply.hh>
#include <gcs/constraints/power.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <exception>
#include <functional>
#include <iostream>
#include <set>
#include <string>
#include <tuple>
#include <variant>
#include <vector>

using namespace gcs;

using std::cerr;
using std::endl;
using std::function;
using std::set;
using std::string;
using std::tuple;
using std::variant;
using std::vector;

namespace
{
    using Solution = tuple<long long, long long, long long>;
    using Level = variant<consistency::Auto, consistency::BC, consistency::Tabulated>;
    using Build = function<auto(Problem &, IntegerVariableID, IntegerVariableID, IntegerVariableID)->void>;

    const auto two_to_the_32 = 4294967296_i;
    const auto two_to_the_60 = 1152921504606846976_i;

    auto check(bool x, const auto &... explain) -> void
    {
        if (! x) {
            (cerr << ... << explain) << endl;
            exit(EXIT_FAILURE);
        }
    }

    // Post over three fresh variables a, b and c, list every solution, and
    // compare the list with the expected one.
    auto run(const string & name, Integer a_lo, Integer a_hi, Integer b_lo, Integer b_hi, Integer c_lo, Integer c_hi, const Build & build,
        const set<Solution> & expected) -> void
    {
        Problem p;
        auto a = p.create_integer_variable(a_lo, a_hi, "a");
        auto b = p.create_integer_variable(b_lo, b_hi, "b");
        auto c = p.create_integer_variable(c_lo, c_hi, "c");
        build(p, a, b, c);

        set<Solution> actual;
        try {
            solve_with(p, SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                actual.emplace(s(a).raw_value, s(b).raw_value, s(c).raw_value);
                return true;
            }});
        }
        catch (const std::exception & e) {
            check(false, name, ": threw ", e.what());
        }
        check(actual == expected, name, ": ", actual.size(), " solutions, but ", expected.size(), " expected");
    }

    auto test_multiply(const Level & level) -> void
    {
        auto post = [&](Problem & p, IntegerVariableID x, IntegerVariableID y, IntegerVariableID z) {
            p.post(Multiply{x, y, z}.with_consistency(level));
        };

        // Operands that could reach 2^64, and a small product.
        set<Solution> small;
        for (long long x = 1; x <= 20; ++x)
            for (long long y = 1; x * y <= 20; ++y)
                small.emplace(x, y, x * y);
        run("multiply, small product", 1_i, two_to_the_32 - 1_i, 1_i, two_to_the_32 - 1_i, 0_i, 20_i, post, small);

        // Every corner overflows, on either side of zero: no solutions.
        run("multiply, every corner too big", two_to_the_32 - 3_i, two_to_the_32 - 1_i, two_to_the_32 - 3_i, two_to_the_32 - 1_i, 0_i,
            Integer::max_bounded_value(), post, {});
        run("multiply, every corner too small", -two_to_the_32 + 1_i, -two_to_the_32 + 3_i, two_to_the_32 - 3_i, two_to_the_32 - 1_i,
            Integer::min_bounded_value(), 0_i, post, {});

        // Some corners overflow and some do not, with solutions near 2^60: y
        // takes one of two values, and x is whatever lands the product in range.
        auto z_lo = two_to_the_60, z_hi = two_to_the_60 + 2147483648_i;
        set<Solution> near;
        for (auto y : {1073741824_i, 1073741825_i})
            for (auto x = (z_lo + y - 1_i) / y; x * y <= z_hi; ++x)
                near.emplace(x.raw_value, y.raw_value, (x * y).raw_value);
        check(! near.empty(), "multiply, near 2^60: nothing expected, so the case tests nothing");
        run("multiply, near 2^60", 1_i, two_to_the_32, 1073741824_i, 1073741825_i, z_lo, z_hi, post, near);

        // A square, whose bounds come from square_bounds instead. b is a
        // fixed bystander.
        set<Solution> squares;
        for (long long x = -7; x <= 7; ++x)
            squares.emplace(x, 0, x * x);
        run(
            "multiply, square", -two_to_the_32 + 1_i, two_to_the_32 - 1_i, 0_i, 0_i, 0_i, 50_i,
            [&](Problem & p, IntegerVariableID x, IntegerVariableID, IntegerVariableID z) { p.post(Multiply{x, x, z}.with_consistency(level)); },
            squares);
    }

    auto test_divide_modulus(const Level & level) -> void
    {
        auto divide = [&](Problem & p, IntegerVariableID x, IntegerVariableID y, IntegerVariableID q) {
            p.post(Divide{x, y, q}.with_consistency(level));
        };
        auto modulus = [&](Problem & p, IntegerVariableID x, IntegerVariableID y, IntegerVariableID r) {
            p.post(Modulus{x, y, r}.with_consistency(level));
        };

        // The issue's shape: a dividend around 10^12 and a divisor around 10^7,
        // so the quotient's magnitude (Modulus: its 2^40 - 1 bit maximum) times
        // the divisor's is past 2^63. Positive and negative dividends and
        // divisors, as truncated division rounds towards zero.
        const auto big = 1000000000000_i, div = 10000000_i;
        for (auto x_sign : {1_i, -1_i})
            for (auto y_sign : {1_i, -1_i}) {
                auto x_lo = x_sign == 1_i ? big - 30_i : -big, x_hi = x_sign == 1_i ? big : -big + 30_i;
                auto y_lo = y_sign == 1_i ? div - 3_i : -div, y_hi = y_sign == 1_i ? div : -div + 3_i;
                set<Solution> quotients, remainders;
                for (auto x = x_lo; x <= x_hi; ++x)
                    for (auto y = y_lo; y <= y_hi; ++y) {
                        quotients.emplace(x.raw_value, y.raw_value, (x / y).raw_value);
                        remainders.emplace(x.raw_value, y.raw_value, (x % y).raw_value);
                    }
                auto suffix = string{x_sign == 1_i ? " +x" : " -x"} + (y_sign == 1_i ? " +y" : " -y");
                run("divide," + suffix, x_lo, x_hi, y_lo, y_hi, -big, big, divide, quotients);
                run("modulus," + suffix, x_lo, x_hi, y_lo, y_hi, -div, div, modulus, remainders);
            }

        // The issue's other rows: 32-bit operands, which the quotient's
        // magnitude takes after the dividend.
        set<Solution> wide_quotients, wide_remainders;
        for (auto x = two_to_the_32 - 3_i; x <= two_to_the_32 - 1_i; ++x)
            for (auto y = two_to_the_32 - 5_i; y <= two_to_the_32 - 1_i; ++y) {
                wide_quotients.emplace(x.raw_value, y.raw_value, (x / y).raw_value);
                wide_remainders.emplace(x.raw_value, y.raw_value, (x % y).raw_value);
            }
        run("divide, 32-bit operands", two_to_the_32 - 3_i, two_to_the_32 - 1_i, two_to_the_32 - 5_i, two_to_the_32 - 1_i, 0_i, two_to_the_32 - 1_i,
            divide, wide_quotients);
        run("modulus, 32-bit operands", two_to_the_32 - 3_i, two_to_the_32 - 1_i, two_to_the_32 - 5_i, two_to_the_32 - 1_i, 0_i, two_to_the_32 - 1_i,
            modulus, wide_remainders);

        // Magnitudes whose smallest product is already past 2^63: no solutions.
        run("divide, every corner too big", 0_i, Integer::max_bounded_value(), two_to_the_32, two_to_the_32 + 3_i, two_to_the_32, two_to_the_32 + 3_i,
            divide, {});
    }

    auto test_power(const Level & level) -> void
    {
        // A cube whose chain's links multiply a result-sized auxiliary by a
        // 2^31 base. b is a fixed bystander.
        const auto mag_lo = two_to_the_60, mag_hi = two_to_the_60 + 10000000000000_i;
        for (auto sign : {1_i, -1_i}) {
            set<Solution> cubes;
            for (auto x = 1048576_i; x * x * x <= mag_hi; ++x)
                if (x * x * x >= mag_lo)
                    cubes.emplace((sign * x).raw_value, 0, (sign * x * x * x).raw_value);
            check(! cubes.empty(), "power: nothing expected, so the case tests nothing");
            auto base_lo = sign == 1_i ? 0_i : -2147483648_i, base_hi = sign == 1_i ? 2147483648_i : 0_i;
            auto r_lo = sign == 1_i ? mag_lo : -mag_hi, r_hi = sign == 1_i ? mag_hi : -mag_lo;
            run(
                sign == 1_i ? "power, positive" : "power, negative", base_lo, base_hi, 0_i, 0_i, r_lo, r_hi,
                [&](Problem & p, IntegerVariableID x, IntegerVariableID, IntegerVariableID r) { p.post(Power{x, 3_c, r}.with_consistency(level)); },
                cubes);
        }
    }
}

auto main(int, char *[]) -> int
{
    // Tabulated would enumerate the domains, and Auto does not choose it at
    // these widths.
    for (const auto & level : vector<Level>{consistency::Auto{}, consistency::BC{}}) {
        test_multiply(level);
        test_divide_modulus(level);
        test_power(level);
    }

    return EXIT_SUCCESS;
}
