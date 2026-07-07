#include <gcs/constraints/innards/product_bounds.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::cerr;
using std::endl;
using std::nullopt;
using std::optional;
using std::pair;

namespace
{
    auto check(bool x, const auto &... explain) -> void
    {
        if (! x) {
            (cerr << ... << explain) << endl;
            exit(EXIT_FAILURE);
        }
    }
}

auto main(int, char *[]) -> int
{
    // div_floor and div_ceil against the defining inequalities
    for (long long a = -50; a <= 50; ++a)
        for (long long b = -7; b <= 7; ++b) {
            if (0 == b)
                continue;
            auto qf = div_floor(Integer{a}, Integer{b}), qc = div_ceil(Integer{a}, Integer{b});
            // q = floor(a/b) iff q <= a/b < q+1; multiplying by negative b reverses
            if (b > 0)
                check(qf.raw_value * b <= a && (qf.raw_value + 1) * b > a, "div_floor(", a, ", ", b, ") = ", qf.raw_value, " wrong");
            else
                check(qf.raw_value * b >= a && (qf.raw_value + 1) * b < a, "div_floor(", a, ", ", b, ") = ", qf.raw_value, " wrong");
            if (b > 0)
                check(qc.raw_value * b >= a && (qc.raw_value - 1) * b < a, "div_ceil(", a, ", ", b, ") = ", qc.raw_value, " wrong");
            else
                check(qc.raw_value * b <= a && (qc.raw_value - 1) * b > a, "div_ceil(", a, ", ", b, ") = ", qc.raw_value, " wrong");
        }

    // isqrt and ceil_isqrt against the defining inequalities
    for (long long n = 0; n <= 20000; ++n) {
        auto r = isqrt(Integer{n}), c = ceil_isqrt(Integer{n});
        check(r.raw_value * r.raw_value <= n && (r.raw_value + 1) * (r.raw_value + 1) > n, "isqrt(", n, ") = ", r.raw_value, " wrong");
        check(c.raw_value * c.raw_value >= n && (c.raw_value == 0 || (c.raw_value - 1) * (c.raw_value - 1) < n), "ceil_isqrt(", n,
            ") = ", c.raw_value, " wrong");
    }

    // product_bounds against enumeration
    for (long long x_lo = -6; x_lo <= 6; ++x_lo)
        for (long long x_hi = x_lo; x_hi <= 6; ++x_hi)
            for (long long y_lo = -6; y_lo <= 6; ++y_lo)
                for (long long y_hi = y_lo; y_hi <= 6; ++y_hi) {
                    auto [lo, hi] = product_bounds(Integer{x_lo}, Integer{x_hi}, Integer{y_lo}, Integer{y_hi});
                    auto expect_lo = x_lo * y_lo, expect_hi = x_lo * y_lo;
                    for (auto x = x_lo; x <= x_hi; ++x)
                        for (auto y = y_lo; y <= y_hi; ++y) {
                            expect_lo = std::min(expect_lo, x * y);
                            expect_hi = std::max(expect_hi, x * y);
                        }
                    check(lo.raw_value == expect_lo && hi.raw_value == expect_hi, "product_bounds([", x_lo, ",", x_hi, "], [", y_lo, ",", y_hi,
                        "]) = [", lo.raw_value, ",", hi.raw_value, "] but enumeration gives [", expect_lo, ",", expect_hi, "]");
                }

    // square_bounds is exact
    for (long long lo = -20; lo <= 20; ++lo)
        for (long long hi = lo; hi <= 20; ++hi) {
            auto [z_lo, z_hi] = square_bounds(Integer{lo}, Integer{hi});
            auto expect_lo = lo * lo, expect_hi = lo * lo;
            for (auto x = lo; x <= hi; ++x) {
                expect_lo = std::min(expect_lo, x * x);
                expect_hi = std::max(expect_hi, x * x);
            }
            check(z_lo.raw_value == expect_lo && z_hi.raw_value == expect_hi, "square_bounds([", lo, ",", hi, "]) = [", z_lo.raw_value, ",",
                z_hi.raw_value, "] but enumeration gives [", expect_lo, ",", expect_hi, "]");
        }

    // square_filter is the exact hull of the supported set
    for (long long x_lo = -15; x_lo <= 15; ++x_lo)
        for (long long x_hi = x_lo; x_hi <= 15; ++x_hi)
            for (long long z_lo = -5; z_lo <= 230; z_lo += 3)
                for (long long z_hi = z_lo; z_hi <= 230; z_hi += 7) {
                    auto [lo, hi] = square_filter(Integer{x_lo}, Integer{x_hi}, Integer{z_lo}, Integer{z_hi});
                    optional<long long> expect_lo, expect_hi;
                    for (auto x = x_lo; x <= x_hi; ++x)
                        if (x * x >= z_lo && x * x <= z_hi) {
                            if (! expect_lo)
                                expect_lo = x;
                            expect_hi = x;
                        }
                    if (expect_lo)
                        check(lo.raw_value == *expect_lo && hi.raw_value == *expect_hi, "square_filter x=[", x_lo, ",", x_hi, "] z=[", z_lo, ",",
                            z_hi, "] = [", lo.raw_value, ",", hi.raw_value, "] but hull is [", *expect_lo, ",", *expect_hi, "]");
                    else
                        check(lo > hi, "square_filter x=[", x_lo, ",", x_hi, "] z=[", z_lo, ",", z_hi, "] = [", lo.raw_value, ",", hi.raw_value,
                            "] but nothing is supported");
                }

    // quotient_filter: sound on every box, and the documented outcomes fire
    for (long long y_lo = -8; y_lo <= 8; ++y_lo)
        for (long long y_hi = y_lo; y_hi <= 8; ++y_hi)
            for (long long z_lo = -8; z_lo <= 8; ++z_lo)
                for (long long z_hi = z_lo; z_hi <= 8; ++z_hi) {
                    auto result = quotient_filter(Integer{y_lo}, Integer{y_hi}, Integer{z_lo}, Integer{z_hi});
                    using Kind = QuotientFilter::Kind;

                    auto supported = [&](long long x) {
                        for (auto y = y_lo; y <= y_hi; ++y)
                            if (x * y >= z_lo && x * y <= z_hi)
                                return true;
                        return false;
                    };

                    switch (result.kind) {
                    case Kind::NoFilter:
                        check(y_lo <= 0 && 0 <= y_hi && z_lo <= 0 && 0 <= z_hi, "quotient_filter y=[", y_lo, ",", y_hi, "] z=[", z_lo, ",", z_hi,
                            "] claims NoFilter");
                        break;
                    case Kind::EmptyBecauseYZero:
                        check(y_lo == 0 && y_hi == 0 && (z_lo > 0 || z_hi < 0), "quotient_filter y=[", y_lo, ",", y_hi, "] z=[", z_lo, ",", z_hi,
                            "] claims EmptyBecauseYZero");
                        break;
                    case Kind::Bounds:
                        for (long long x = -100; x <= 100; ++x)
                            if (supported(x))
                                check(result.lo.raw_value <= x && x <= result.hi.raw_value, "quotient_filter y=[", y_lo, ",", y_hi, "] z=[", z_lo,
                                    ",", z_hi, "] = [", result.lo.raw_value, ",", result.hi.raw_value, "] excludes supported ", x);
                        break;
                    }
                }

    // pin the known inexactness so a future "improvement" is a deliberate choice:
    // y=[2,3], z=[7,7] leaves the unsupported endpoint x=3 (BC-Z corners, not BC-D)
    {
        auto result = quotient_filter(2_i, 3_i, 7_i, 7_i);
        check(result.kind == QuotientFilter::Kind::Bounds && result.lo == 3_i && result.hi == 3_i,
            "quotient_filter(2, 3, 7, 7) no longer gives the JaCoP corner bounds [3,3]");
    }

    return EXIT_SUCCESS;
}
