#include <iostream>
#include <gcs/gcs.hh>

using namespace std;
using namespace gcs;

int main() {
    Problem p{ProofOptions{"compare.opb", "compare.veripb"}};
    auto x = p.create_integer_variable(1_i, 3_i, "x");
    auto w = 3_c;
    p.post(LessThanIff(x, w, FalseLiteral{}));
    auto stats = solve_with(p,
                            SolveCallbacks{
                                    .solution = [&](const CurrentState & s) -> bool {
                                        cout << s(x) << endl;
                                        return true;
                                    },});
    cout << stats;
    return 0;
}