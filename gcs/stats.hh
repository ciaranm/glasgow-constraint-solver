#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATS_HH

#include <gcs/constraint_id.hh>
#include <gcs/lifetime.hh>

#include <chrono>
#include <functional>
#include <iosfwd>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/ostream.h>
#endif

namespace gcs
{
    /**
     * \brief How loudly a StatsNote is to be said.
     *
     * A rung is justified by a distinct *default behaviour*, not by a distinct
     * shade of importance --- otherwise the ladder grows names faster than it
     * grows meaning and nobody can tell where to put a new note. There are
     * three behaviours and so, at most, four rungs:
     *
     * | Behaviour                                              | Rung        |
     * |--------------------------------------------------------|-------------|
     * | Goes to `cerr` live, unprompted, via the default callback | Important |
     * | Appears in the default `operator<<`                     | General     |
     * | Only when asked                                         | Detailed, Debug |
     *
     * Detailed and Debug share a behaviour and are a filter granularity; the
     * split is kept because "meaningful only alongside a proof" is a stable
     * distinction. A fifth rung should have to earn a fourth behaviour.
     *
     * \ref Important is defined by **audience**, not by provenance: things a
     * user needs to know even if they are a non-expert arriving through
     * MiniZinc. It does not mean "something went wrong" --- everything it
     * reports is the solver working correctly --- which is why it is not called
     * `Warning` or `Severe`. Two consequences follow, and are the rule for
     * deciding where a note goes:
     *
     *   - An Important note is written for a different reader than a
     *     ComponentStats::summary(). It names the model-level thing --- the
     *     constraint, the option the caller passed --- and states the
     *     consequence, without naming the component's internals. "Cumulative
     *     strengthening was skipped on 2 of 12 constraints because a
     *     proof-size limit was reached; answers are still correct, but search
     *     may be slower" is Important. "2 donors passed over, largest needed
     *     41000 states against a budget of 20000, see
     *     with_dynamic_programming_budget" is the same fact at General. Both
     *     exist.
     *   - An Important note therefore renders *without* the component label:
     *     `cumulative_strengthening:` means nothing to the reader it is for.
     *     The label prefix applies at General and below.
     *
     * A state that cannot happen does not go on this ladder at all: it should
     * throw. A note for a bug is a note nobody reads, and keeping such things
     * here is what would let Important fill up with things to scroll past.
     *
     * \ingroup Core
     */
    enum class StatsLevel
    {
        /// Only means something to someone reading the emitted proof.
        Debug,
        /// The breakdown behind a summary.
        Detailed,
        /// An expert reading solver output wants it; the default.
        General,
        /// A non-expert would draw a false conclusion without it.
        Important
    };

    /**
     * \brief One leaf of a ComponentStats block, flattened for tabulating a
     * sweep.
     *
     * A derived *view*, never a record: nothing reads an entry to decide
     * anything, so its stringly-typed name costs nothing that matters, and a
     * typo shows up in a dump rather than in a result.
     *
     * \ingroup Core
     */
    struct StatsEntry final
    {
        std::string name;
        long long value;
    };

    /**
     * \brief What one component of the solver did, as the component itself
     * records it.
     *
     * The blocks are the source of truth --- the precise machine-readable
     * record a test asserts on --- and this narrow base is what lets Stats
     * render them without knowing their types. Deriving from it is how a
     * component in its own directory joins the report without any Core header
     * learning that the component exists.
     *
     * A component allocates its block whether or not a caller asked for one, so
     * that a component which did nothing still says so: "nothing" is the answer
     * worth being able to see, and it is the one every other check passes
     * without noticing.
     *
     * \ingroup Core
     */
    class ComponentStats
    {
    public:
        virtual ~ComponentStats() = 0;

        /**
         * \brief A stable identifier in the style of the header it lives in:
         * `cumulative_strengthening`, `auto_table`, `difference_logic`.
         */
        [[nodiscard]] virtual auto component_name() const -> std::string = 0;

        /**
         * \brief One line, always shown, saying what the component did ---
         * including when the answer is "nothing".
         */
        [[nodiscard]] virtual auto summary() const -> std::string = 0;

        /**
         * \brief The whole block, flattened. Not shown by default.
         *
         * Every field of the block belongs here: a field that never reaches the
         * flat view is invisible to anything tabulating a sweep, and nothing
         * else would notice.
         */
        [[nodiscard]] virtual auto entries() const -> std::vector<StatsEntry> = 0;
    };

    /**
     * \brief One thing a component decided, reported when it decided it.
     *
     * Notes are not a second copy of the counters: a counter says *how many*,
     * and the notes say *which ones, and with what figures*. That is the
     * relationship a proof comment used to have to its counter, and it is the
     * part of that arrangement worth keeping.
     *
     * \ingroup Core
     */
    struct StatsNote final
    {
        StatsLevel level;

        /// Which component said it; the ComponentStats::component_name() of the
        /// block this note goes with.
        std::string component;

        /// The constraint it is about, where there is one. Typed, so that a
        /// caller can filter and a test can assert, rather than baked into
        /// \ref text.
        std::optional<ConstraintID> constraint;

        /// What happened, in the component's own words, with the figures in it.
        std::string text;
    };

    /**
     * \brief Render a note as one line, as the default callback and the default
     * `operator<<` both do it.
     *
     * The component label prefixes the text at General and below, and is
     * omitted at Important; the constraint, if there is one, is named at the
     * end. Phrasing a note is the renderer's job and not the reporting site's,
     * which is why StatsNote carries the ConstraintID rather than a string with
     * it already in.
     *
     * \ingroup Core
     */
    [[nodiscard]] auto render(const StatsNote &) -> std::string;

    /**
     * \brief Called by gcs::solve_with() as each StatsNote is reported, which
     * is at the moment the component decided the thing it is about.
     *
     * \warning Unlike every other callback, leaving this unset does **not** mean
     * "do nothing": unset gets default_stats_report(). A silent default is the
     * thing this channel exists to fix, so silence has to be asked for, by
     * setting a callback that does nothing.
     *
     * \warning May eventually be called from any search thread, once there is a
     * parallel search. It is called during solving, not at teardown, which is
     * the point of it: a presolver's decision is reported while it is being
     * made.
     *
     * \ingroup SolveCallbacks
     */
    using StatsReportCallback = std::function<auto(const StatsNote &)->void>;

    /**
     * \brief The default StatsReportCallback: writes notes at `level` and above
     * to `cerr`, rendered by render().
     *
     * \ingroup Core
     */
    [[nodiscard]] auto default_stats_report(StatsLevel level = StatsLevel::Important) -> StatsReportCallback;

    /**
     * \brief A StatsReportCallback that does nothing, for a caller that wants
     * the notes accumulated on Stats but nothing written anywhere.
     *
     * Spelled out rather than left to `StatsReportCallback{}`, which means "use
     * the default" instead.
     *
     * \ingroup Core
     */
    [[nodiscard]] auto silent_stats_report() -> StatsReportCallback;

    /**
     * \brief Statistics from solving.
     *
     * Deliberately not an aggregate, despite the plain counters: what happens
     * to a note at the moment it is reported has to stay a decision this class
     * makes, rather than one every caller has already made by writing into a
     * public vector.
     *
     * \sa gcs::solve()
     * \sa gcs::solve_with()
     * \ingroup Core
     */
    struct Stats final
    {
        unsigned long long recursions = 0;
        unsigned long long failures = 0;
        unsigned long long propagations = 0;
        unsigned long long effectful_propagations = 0;
        unsigned long long contradicting_propagations = 0;
        unsigned long long solutions = 0;
        unsigned long long max_depth = 0;
        unsigned long long restarts = 0;
        unsigned long long learned_nogoods = 0;

        unsigned long long n_propagators = 0;

        /// How many propagators had their EnableButIdempotent claims ignored
        /// because their trigger scope aliases a variable (directly or
        /// through a view). A downgraded propagator just keeps today's
        /// always-requeue behaviour; this counter makes the downgrade
        /// observable.
        unsigned long long idempotence_downgrades = 0;

        std::chrono::microseconds solve_time;

        /**
         * \brief Register a component's block, so that its summary and entries
         * are reported.
         *
         * Registering the same block twice does nothing: a component installed
         * many times reports one aggregate rather than one entry per install.
         * The block is registered *empty* --- the numbers arrive later, and are
         * read when the report is rendered.
         */
        auto add_component(std::shared_ptr<const ComponentStats>) -> void;

        /**
         * \brief Report one decision, now.
         *
         * Forwards to the handler and then accumulates. The handler is what
         * solve_with() installs from SolveCallbacks::stats_report, which is why
         * this is a method and not a public vector.
         */
        auto report(StatsNote) -> void;

        /**
         * \brief Install the handler report() forwards to, or clear it.
         *
         * For gcs::solve_with(), which sets it before anything can report and
         * clears it before returning, so that a caller holding the result is
         * not holding a live callback into a finished search.
         */
        auto set_report_handler(StatsReportCallback) -> void;

        [[nodiscard]] auto components() const GCS_LIFETIME_BOUND -> const std::vector<std::shared_ptr<const ComponentStats>> &;

        [[nodiscard]] auto notes() const GCS_LIFETIME_BOUND -> const std::vector<StatsNote> &;

    private:
        std::vector<std::shared_ptr<const ComponentStats>> _components;
        std::vector<StatsNote> _notes;
        StatsReportCallback _handler;
    };

    /**
     * \brief Stats can be written to an ostream, for convenience.
     *
     * Writes the counters, then every registered component's summary, then
     * every note at StatsLevel::General and above. The Important ones appear
     * here as well as having gone to the handler when they happened, on
     * purpose: a note reported during presolve has scrolled off the top of an
     * hour-long run by the time anyone reads the counters.
     *
     * \sa Stats
     * \ingroup Core
     */
    auto operator<<(std::ostream &, const Stats &) -> std::ostream &;
}

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
template <>
struct std::formatter<gcs::Stats> : std::formatter<std::string>
{
    auto format(const gcs::Stats & s, std::format_context & ctx) const
    {
        std::ostringstream oss;
        oss << s;
        return std::formatter<std::string>::format(oss.str(), ctx);
    }
};
#else
template <>
struct fmt::formatter<gcs::Stats> : ostream_formatter
{
};
#endif

#endif
