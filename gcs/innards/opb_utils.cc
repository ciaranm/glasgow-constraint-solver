/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/innards/opb_utils.hh>

#include <algorithm>
#include <ostream>
#include <string>

using namespace gcs::innards::opb_utils;

using std::max;
using std::move;
using std::ostream;
using std::pair;
using std::string;
using std::vector;

auto gcs::innards::opb_utils::operator>=(OPBExpression x, Integer v) -> OPBInequality
{
    return OPBInequality{move(x), v};
}

auto gcs::innards::opb_utils::operator<(OPBExpression x, Integer v) -> OPBInequality
{
    OPBInequality result{move(x), -v + 1_i};
    for (auto & [c, _] : result.expr.weighted_terms)
        c = -c;
    return result;
}

auto gcs::innards::opb_utils::opb_sum(vector<pair<Integer, string>> w) -> OPBExpression
{
    return OPBExpression{move(w)};
}

auto gcs::innards::opb_utils::opb_var_as_sum(const string & v) -> OPBInequality
{
    return OPBInequality{OPBExpression{vector{pair{1_i, v}}}, 1_i};
}

auto gcs::innards::opb_utils::negate_opb_var_name(const string & s) -> string
{
    if (s.starts_with("~"))
        return s.substr(1);
    else
        return "~" + s;
}

auto gcs::innards::opb_utils::implied_by(OPBInequality x, const string & v) -> OPBInequality
{
    OPBInequality result{move(x.expr), x.value};
    Integer k = x.value;
    for (auto & [c, _] : result.expr.weighted_terms)
        k += max(0_i, -c);
    result.expr.weighted_terms.emplace_back(k, negate_opb_var_name(v));
    return result;
}

auto gcs::innards::opb_utils::implies(OPBInequality x, const string & v) -> OPBInequality
{
    Integer k = -x.value + 1_i;
    OPBInequality result{move(x.expr), -x.value + 1_i};
    for (auto & [c, _] : result.expr.weighted_terms) {
        k += max(0_i, c);
        c = -c;
    }
    result.expr.weighted_terms.emplace_back(k, v);
    return result;
}

auto gcs::innards::opb_utils::operator<<(ostream & s, const OPBInequality & e) -> ostream &
{
    for (auto & [c, v] : e.expr.weighted_terms)
        s << c << " " << v << " ";
    s << ">= " << e.value;
    return s;
}
