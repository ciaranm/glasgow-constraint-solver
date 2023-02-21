
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/extensional.hh>
#include <gcs/problem.hh>
#include <gcs/smart_entry.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>
#include <gcs/constraints/regular.hh>

using namespace gcs;

using std::cout;
using std::endl;
using std::iota;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::shuffle;
using std::ssize;
using std::string;
using std::stringstream;
using std::uniform_int_distribution;
using std::vector;

using namespace innards;

auto index_of(const IntegerVariableID & val, const vector<IntegerVariableID> & vec) -> int
{
    ptrdiff_t pos = distance(vec.begin(), find(vec.begin(), vec.end(), val));
    return (int)pos;
}


auto test_regular(const int & n, mt19937 & rng)
{
    stringstream string_rep;


    Problem p;

    auto x = p.create_integer_variable_vector(n, 0_i, Integer{n-1}, "x");
    uniform_int_distribution<> dist_2_to_4n(2, 4*n);
    uniform_int_distribution<> dist_m1_to_nm1(-1, n-1);
    auto num_states = dist_2_to_4n(rng);
    uniform_int_distribution<> dist_1_to_num_states(1, num_states-1);
    uniform_int_distribution<> dist_m1_to_num_states(-1, num_states-1);



    string_rep << "#states\n";
    for(int i = 0; i < num_states; i++)
        string_rep << "s" << i << "\n";
    string_rep << "#initial\ns0\n";

    auto num_final_states = dist_1_to_num_states(rng);

    vector<long> states(num_states);
    iota(states.begin(), states.end(), 0);
    shuffle(states.begin(), states.end(), rng);
    vector<long> final_states(states.begin(), states.begin() + num_final_states);

    string_rep << "#accepting\n";
    for(const auto& i : final_states)
        string_rep << "s" << i << "\n";

    string_rep << "#alphabet\n";
    vector<Integer> symbols{};
    for(int i = 0; i < n; i ++) {
        symbols.emplace_back(i);
        string_rep << i << "\n";
    }

    string_rep << "#transitions\n";
    vector<vector<long>> transitions(num_states, vector<long>(n));
    for(int i = 0; i < num_states; i++) {
        for(int j = 0; j < n; j++) {
            transitions[i][j] = dist_m1_to_num_states(rng);
            if(transitions[i][j] != -1)
                string_rep << "s" << i << ":" << j << ">s" << transitions[i][j] << "\n";
        }
    }

    p.post(Regular{x, symbols, num_states, transitions, final_states});

    auto stats = solve_with(p,
                            SolveCallbacks{
                                    .solution = [&](const CurrentState &s) -> bool {
                                        return true;
                                    }},
                            ProofOptions{"random_regular.opb", "random_regular.veripb"});

    cout << "Num solutions: " << stats.solutions << endl;
    if (0 != system("veripb random_regular.opb random_regular.veripb")) {
        cout << string_rep.str() << endl;
        return false;
    }

    return true;
}
auto main(int, char *[]) -> int
{
    // random_device rand_dev;
    // std::mt19937 rng(rand_dev());
    mt19937 rng(0); // Same every time, for now
    for (int n = 3; n < 6; n++) {
        for (int r = 0; r < 240 / n; r++) {
            if (!test_regular(n, rng)) {
                cout << "n == " << n << " r == " << r << endl;
                return EXIT_FAILURE;
            }
        }
    }

    return EXIT_SUCCESS;
}
