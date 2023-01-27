#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_OPB_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_OPB_UTILS_HH

#include <gcs/integer.hh>

#include <iosfwd>
#include <string>
#include <utility>
#include <vector>

namespace gcs::innards::opb_utils
{
    /**
     * \defgroup OPBUtils Helpers for writing OPB format files
     * \ingroup Innards
     */

    /**
     * An OPB expression (that is, the things to the left of an inequality).
     *
     * \ingroup OPBUtils
     */
    struct OPBExpression
    {
        std::vector<std::pair<Integer, std::string>> weighted_terms;
    };

    /**
     * An OPB inequality, in greater-or-equal form.
     *
     * \ingroup OPBUtils
     */
    struct OPBInequality
    {
        OPBExpression expr;
        Integer value;
    };

    /**
     * Turn an OPBExpression into an OPBInequality.
     *
     * \ingroup OPBUtils
     */
    [[nodiscard]] auto operator>=(OPBExpression x, Integer v) -> OPBInequality;

    /**
     * Turn an OPBExpression into an OPBInequality.
     *
     * \ingroup OPBUtils
     */
    [[nodiscard]] auto operator<(OPBExpression x, Integer v) -> OPBInequality;

    /**
     * Create an OPBExpression from a weighted sum.
     *
     * \ingroup OPBUtils
     */
    [[nodiscard]] auto opb_sum(std::vector<std::pair<Integer, std::string>> w) -> OPBExpression;

    /**
     * Create an OPBExpression just saying this literal is true.
     *
     * \ingroup OPBUtils
     */
    [[nodiscard]] auto opb_var_as_sum(const std::string & v) -> OPBInequality;

    [[nodiscard]] auto negate_opb_var_name(const std::string &) -> std::string;

    /**
     * Give an OPBInequality <code>x &lt;== v</code>.
     *
     * \ingroup OPBUtils
     */
    [[nodiscard]] auto implied_by(OPBInequality x, const std::string & v) -> OPBInequality;

    /**
     * Give an OPBInequality <code>x ==&gt; v</code>.
     *
     * \ingroup OPBUtils
     */
    [[nodiscard]] auto implies(OPBInequality x, const std::string & v) -> OPBInequality;

    /**
     * Write an OPBInequality to a stream.
     *
     * \ingroup OPBUtils
     */
    auto operator<<(std::ostream & s, const OPBInequality & e) -> std::ostream &;
}

#endif
