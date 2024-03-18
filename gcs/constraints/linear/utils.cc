#include <gcs/constraints/linear/utils.hh>

#include <gcs/exception.hh>
#include <gcs/innards/state.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <cstdlib>
#include <sstream>
#include <type_traits>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::is_same_v;
using std::pair;
using std::remove_if;
using std::sort;
using std::string;
using std::stringstream;
using std::to_string;
using std::variant;
using std::vector;

auto gcs::innards::tidy_up_linear(const WeightedSum & coeff_vars) -> pair<TidiedUpLinear, Integer>
{
    SumOf<Weighted<SimpleIntegerVariableID>> simplified_sum;
    Integer modifier{0_i};
    for (const auto & [c, v] : coeff_vars.terms)
        overloaded{
            [&, &c = c](const SimpleIntegerVariableID & v) { simplified_sum += c * v; },
            [&, &c = c](const ConstantIntegerVariableID & v) { modifier -= c * v.const_value; },
            [&, &c = c](const ViewOfIntegerVariableID & v) {
                simplified_sum += (v.negate_first ? -c : c) * v.actual_variable;
                modifier -= c * v.then_add;
            }}
            .visit(v);

    sort(simplified_sum.terms.begin(), simplified_sum.terms.end(),
        [](const Weighted<SimpleIntegerVariableID> & a, const Weighted<SimpleIntegerVariableID> & b) {
            return a.variable < b.variable;
        });

    // same variable appears twice? bring in its coefficient, and rewrite future
    // coefficients to be zero
    auto c = simplified_sum.terms.begin();
    while (c != simplified_sum.terms.end()) {
        auto c_next = next(c);
        while (c_next != simplified_sum.terms.end() && c_next->variable == c->variable) {
            c->coefficient += c_next->coefficient;
            c_next->coefficient = 0_i;
            ++c_next;
        }
        c = c_next;
    }

    // remove zero coefficients
    simplified_sum.terms.erase(remove_if(simplified_sum.terms.begin(), simplified_sum.terms.end(),
                                   [](const Weighted<SimpleIntegerVariableID> & cv) {
                                       return cv.coefficient == 0_i;
                                   }),
        simplified_sum.terms.end());

    if (simplified_sum.terms.end() == find_if(simplified_sum.terms.begin(), simplified_sum.terms.end(), [](const Weighted<SimpleIntegerVariableID> & cv) -> bool {
            return cv.coefficient != 1_i;
        })) {
        SumOf<SimpleIntegerVariableID> simple_result;
        for (auto & [_, v] : simplified_sum.terms)
            simple_result.terms.emplace_back(v);
        return pair{simple_result, modifier};
    }
    else if (simplified_sum.terms.end() == find_if(simplified_sum.terms.begin(), simplified_sum.terms.end(), [](const Weighted<SimpleIntegerVariableID> & cv) -> bool {
                 return cv.coefficient != 1_i && cv.coefficient != -1_i;
             })) {
        SumOf<PositiveOrNegative<SimpleIntegerVariableID>> sum_result;
        for (auto & [c, v] : simplified_sum.terms)
            sum_result.terms.push_back(PositiveOrNegative<SimpleIntegerVariableID>{c == 1_i, v});
        return pair{sum_result, modifier};
    }
    else
        return pair{simplified_sum, modifier};
}
