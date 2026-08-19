#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_RULE_COUNTERS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_RULE_COUNTERS_HH

#include <cstddef>
#include <initializer_list>
#include <string>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief What one propagation rule did, over a whole solve.
     *
     * Four numbers rather than one, because "how often did the rule fire" is
     * several different questions and telling them apart is the entire reason
     * these exist:
     *
     * - \c calls --- how many times the rule's sweep ran at all. A rule that is
     *   switched on is paid for here whether or not anything comes of it, which
     *   is why several of these rules are off by default.
     *
     * - \c firings --- how many times it moved a bound. This is *work done*: an
     *   inference that was not already true, that the solver had to justify and
     *   that a proof has a line for.
     *
     * - \c already_true --- how many candidates it skipped because the
     *   conclusion it was about to draw already held. Every rule here tests the
     *   live bound before working out its own condition, that test being much
     *   the cheaper of the two, so this counts **candidates the rule passed
     *   over, not detections it made**: whether the rule's condition would also
     *   have held for them is not evaluated and is not what this says. It is
     *   the cheap, exactly-defined half of "the rule fired but changed
     *   nothing".
     *
     * - \c contradictions --- how many times it proved the node infeasible.
     *
     * \par Why not count detections
     *
     * A detection count --- the rule's condition holding, whether or not the
     * conclusion was already true --- is what a standalone simulation of a rule
     * counts, because a simulation has no propagation fixpoint to compare
     * against. Getting the same number here would mean evaluating each rule's
     * condition for candidates it currently skips, which is the expensive half
     * of the sweep, and every solve would pay for a number only a measurement
     * wants.
     *
     * So these are deliberately not that. \c firings is the better quantity for
     * the question anyway: it is the work the rule actually caused. What it
     * means is that **a simulated firing count and one of these are not the
     * same measurement**, however natural it is to put them in one sentence.
     *
     * \ingroup Innards
     */
    struct RuleCounters
    {
        unsigned long long calls = 0, firings = 0, already_true = 0, contradictions = 0;
    };

    /**
     * \brief Per-rule counters for one constraint, printed to \c stderr at exit
     * when \c GCS_SCHEDULING_RULE_STATS is set in the environment.
     *
     * Indexed by a plain enum, and the increments are unconditional integer
     * adds on a vector element --- no environment lookup, no map, no atomic, no
     * lock. That is deliberate. These numbers are meant to be read off the same
     * benchmark sweep that produces the recursion counts, so the instrumentation
     * has to be cheap enough that switching it on does not change which
     * instances close inside a timeout. Anything per-firing that allocates or
     * locks would fail that test on a rule that fires in the millions.
     *
     * Nothing is thread safe, because nothing here is threaded: a propagator
     * runs inside one solve. Two solves in one process would share these, which
     * is what a whole-run total is wanted to mean anyway.
     *
     * \sa RuleCounters, and \c dev_docs/rule-counters.md for what the numbers
     * are for and how to read them.
     *
     * \ingroup Innards
     */
    class RuleInstrumentation
    {
    private:
        std::string _prefix;
        std::vector<const char *> _names;
        std::vector<RuleCounters> _counters;

    public:
        /**
         * \param prefix printed before each rule name, so that two constraints'
         *   counters can be told apart in one stream.
         * \param names one per rule, in the order of the enum used to index
         *   this. Held by pointer: pass string literals.
         */
        explicit RuleInstrumentation(std::string prefix, std::initializer_list<const char *> names);

        ~RuleInstrumentation();

        RuleInstrumentation(const RuleInstrumentation &) = delete;
        auto operator=(const RuleInstrumentation &) -> RuleInstrumentation & = delete;

        [[nodiscard]] auto operator[](std::size_t rule) -> RuleCounters &
        {
            return _counters[rule];
        }
    };
}

#endif
