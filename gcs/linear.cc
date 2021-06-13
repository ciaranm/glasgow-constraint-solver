/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "gcs/linear.hh"

#include <algorithm>

using namespace gcs;

using std::remove_if;
using std::sort;

auto gcs::sanitise_linear(Linear & coeff_vars) -> void
{
    sort(coeff_vars.begin(), coeff_vars.end(), [] (const CoefficientAndVariable & a, const CoefficientAndVariable & b) {
            return a.second < b.second;
            });

    // same variable appears twice? bring in its coefficient, and rewrite future
    // coefficients to be zero
    auto c = coeff_vars.begin();
    while (c != coeff_vars.end()) {
        auto c_next = next(c);
        while (c_next != coeff_vars.end() && c_next->second == c->second) {
            c->first += c_next->first;
            c_next->first = 0_i;
            ++c_next;
        }
        c = c_next;
    }

    // remove zero coefficients
    coeff_vars.erase(remove_if(coeff_vars.begin(), coeff_vars.end(), [] (const CoefficientAndVariable & cv) {
                return cv.first == 0_i;
                }), coeff_vars.end());
}

