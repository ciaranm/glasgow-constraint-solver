

#include <gcs/gcs.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <iostream>
#include <string>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::string;
using std::vector;

auto main(int, char *[]) -> int
{
    Problem p;
    auto a = p.create_integer_variable(-100_i, 100_i);
    //    auto b = p.create_integer_variable(-100_i, 100_i);
    //    auto c = p.create_integer_variable(-100_i, 100_i);
    auto n = p.create_integer_variable(0_i, 5_i);
    auto m = p.create_integer_variable(0_i, 5_i);

    auto two_pow_m = p.create_integer_variable(0_i, 32_i);
    auto two_pow_np1 = p.create_integer_variable(0_i, 64_i);
    auto two_pow_n = p.create_integer_variable(0_i, 32_i);
    auto two_pow_np1_minus_two_pow_m = p.create_integer_variable(-32_i, 64_i);

    p.post(Power{2_c, n, two_pow_n});
    p.post(Power{2_c, m, two_pow_m});
    p.post(Power{2_c, n + 1_i, two_pow_np1});
    p.post(Plus{two_pow_np1, -two_pow_m, two_pow_np1_minus_two_pow_m});

    p.post(LessThan{a, two_pow_m});
    //    p.post(LessThan{b, two_pow_n});
    //    p.post(LessThan{b, two_pow_np1_minus_two_pow_m});
    //    p.post(LessThan{c, -two_pow_n + 1_i});
    //    p.post(LinearEquality{Linear{{1_i,a}, {1_i, b}, {1_i, c}}, 1_i});
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "-------" << endl;
                cout << "n = " << s(n) << "; m = " << s(m) << endl;
                cout << "2^n = " << s(two_pow_n) << "; 2^m = " << s(two_pow_m) << "; 2^(n+1) = " << s(two_pow_np1) << endl;
                cout << "2^(n+1) - 2^m = " << s(two_pow_np1_minus_two_pow_m) << endl;
                //                cout << "a  = " << s(a) << "; b = " << s(b) << ";c = " << s(c) << endl;
                return true;
            },
        },
        make_optional<ProofOptions>("up_proof"));

    cout << stats;

    return EXIT_SUCCESS;
}
