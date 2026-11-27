# MiniZinc rewrites `x = y` and `x != y` between two variables into a two-term
# int_lin_eq / int_lin_ne rather than emitting int_eq / int_ne, and the FlatZinc
# reader recovers the shape so the specialised propagators are reached at all.
# Both guards are load-bearing: --fzn-pattern pins that MiniZinc really does hand
# us the linear form (if a future version emits int_eq instead, the recovery is
# dead code and this says so), and the required output pattern pins that the
# recovery actually fired, counting the four sign patterns and *not* the
# variable-right-hand-side constraint, which is three terms and must fall through
# to LinearEquality. Without the second guard the test passes against a binary
# that does no recovery at all; without the enumeration diff a sign error in the
# normalisation passes too.
gcs_minizinc_test(minizinc-two-term-lin-eq two_term_eq.mzn true true
    OPTIONS --fzn-pattern int_lin_eq
    FLAGS "-s"
    REQUIRE "propagatorCallsEqualsConstraints=4")
set_tests_properties(minizinc-two-term-lin-eq PROPERTIES ENVIRONMENT "GCS_PROPAGATOR_STATS=calls")

gcs_minizinc_test(minizinc-two-term-lin-ne two_term_ne.mzn true true
    OPTIONS --fzn-pattern int_lin_ne
    FLAGS "-s"
    REQUIRE "propagatorCallsNotEqualsConstraints=4")
set_tests_properties(minizinc-two-term-lin-ne PROPERTIES ENVIRONMENT "GCS_PROPAGATOR_STATS=calls")

# The same for `x - y <= d`, which is the most common of the three shapes. The
# second lane is the one that matters: it pins that the recovered LessThanEqual
# still reaches the difference-logic presolver, which enumerates
# ReifiedCompareLessThanOrMaybeEqual donors as well as ReifiedLinearInequality
# ones -- six edges lifted either way, and through the comparison family after
# the rewrite, which is what differenceLogicComparisonEdgesLifted counts.
gcs_minizinc_test(minizinc-two-term-lin-le two_term_le.mzn true true
    OPTIONS --fzn-pattern int_lin_le
    FLAGS "-s"
    REQUIRE "propagatorCallsLessEqualConstraints=8")
set_tests_properties(minizinc-two-term-lin-le PROPERTIES ENVIRONMENT "GCS_PROPAGATOR_STATS=calls")

gcs_minizinc_test(minizinc-two-term-lin-le-difference-logic two_term_le.mzn true true
    OPTIONS --fzn-pattern int_lin_le
    FLAGS "-s --difference-logic"
    REQUIRE "propagatorCallsLessEqualConstraints=8" "differenceLogicEdgesLifted=6" "differenceLogicComparisonEdgesLifted=6")
set_tests_properties(minizinc-two-term-lin-le-difference-logic PROPERTIES ENVIRONMENT "GCS_PROPAGATOR_STATS=calls")

# The difference-logic presolver is invisible to solution equivalence and to
# proof verification alike, so this one also asserts on its counters: four
# lifted edges over four nodes, and the two constraints that are not
# difference-shaped classified rather than quietly ignored. All four arrive
# as `int_lin_le`, which is the whole reason this needs no predicate of its
# own, and the reader recovers each as a LessThanEqual, so they are counted
# as comparison edges (below).
#
# These names are also the contract between ComponentStats::entries() and the
# generic %%%mzn-stat loop in fzn_glasgow.cc: each is component_name() and an
# entry name camel-cased together, so a rename on either side fails here rather
# than in whatever is parsing the output. differenceLogicPropagatorInstalled is
# one of the two fields that were filled in and reported to nobody until the
# loop replaced the hand-written list, and is here so that stays fixed.
gcs_minizinc_test(minizinc-differencelogic difference_logic.mzn true true
    FLAGS "-s --difference-logic"
    REQUIRE
    "^%%%mzn-stat: differenceLogicEdgesLifted=4$"
    # Four via the comparison family, because the FlatZinc reader recovers a
    # two-term int_lin_le as LessThanEqual: the presolver enumerates both donor
    # families, so the same four edges lift, and this counter is what says which
    # way in. It was 0 before that recovery existed.
    "^%%%mzn-stat: differenceLogicComparisonEdgesLifted=4$"
    "^%%%mzn-stat: differenceLogicNodes=4$"
    "^%%%mzn-stat: differenceLogicSkippedNotTwoTerms=1$"
    "^%%%mzn-stat: differenceLogicSkippedCoefficients=1$"
    "^%%%mzn-stat: differenceLogicPropagatorInstalled=1$"
    "^%%%mzn-stat: differenceLogicSimplifyRan=1$")
