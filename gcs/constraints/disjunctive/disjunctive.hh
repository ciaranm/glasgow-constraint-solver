#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_DISJUNCTIVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_DISJUNCTIVE_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/innards/disjunctive_mutations.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <cstdint>
#include <map>
#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
    /**
     * \brief Which of Disjunctive's propagation rules are enabled.
     *
     * Both are on by default. Turning one off weakens propagation but never
     * changes the solutions found, and never changes the OPB encoding: these
     * select propagation strength only, and exist so that a test can attribute
     * an inference to the rule that made it (and so that a fixture can show a
     * rule is load-bearing by watching the other one fail to make its
     * inference).
     *
     * \ingroup Constraints
     */
    struct DisjunctiveRules
    {
        /// Time-table: the mandatory-part load profile, its overflow
        /// contradiction and the bound pushes away from blocked times.
        bool time_table = true;

        /// Detectable precedences: a pair whose ordering is forced by bounds
        /// alone pushes the successor's lower bound up to the predecessor's
        /// earliest end, and the predecessor's upper bound down to the
        /// successor's latest start less its own duration.
        bool detectable_precedences = true;

        /// The overload check: a window whose fully-contained tasks carry more
        /// duration than the window is wide is infeasible. Conflict-only, and
        /// the capacity-one case of what CumulativeRules::overload does.
        ///
        /// Certified by re-encoding time *in the proof*: an activity flag per
        /// (task, time) introduced by redundance over order literals the
        /// encoding already has, a pol per ordered pair and time bridging the
        /// pairwise separation rows to a per-time at-most-one, that folded by
        /// recover_am1_from_pairs, and the tasks' energies telescoped against
        /// it. The OPB is untouched: see #730, and \ref overload_vocabulary_at
        /// for where the re-encoding lives.
        bool overload = false;

        /// Refuse an overload conflict whose smallest window holds more than
        /// this many tasks; zero, the default, takes every conflict. Measured
        /// on generated RCPSP (#730), every cap closes fewer instances *and*
        /// costs more proof lines than no cap, declining a conflict deferring
        /// the work rather than removing it --- so this exists to reproduce
        /// that result, not because some cap is expected to pay.
        std::size_t overload_max_window = 0;

        /// Where the overload certificate's activity flags and their per-time
        /// at-most-ones are introduced.
        ///
        /// `Top` derives each once and lets every later firing cite it, which
        /// costs a standing database; `Temporary` derives them per firing and
        /// lets backtracking delete them, which pays for them again every
        /// time. The received objection to `Top` is that hint-free RUP costs
        /// O(live database), so anything left standing taxes the rest of the
        /// proof --- but measured, that tax is flat to within noise from 4,692
        /// to 38,460 standing rows, and `Top` wins on lines and on checking
        /// time by a margin that grows with the firing count. Hence the
        /// default. The switch stays so the measurement can be repeated
        /// in-solver rather than believed.
        innards::ProofLevel overload_vocabulary_at = innards::ProofLevel::Top;
    };

    /**
     * \brief Disjunctive (1D non-overlap) constraint: tasks with variable
     * origins; the durations may each be variables or constants (constants pass
     * through as ConstantIntegerVariableID). No two tasks may occupy the same
     * time point. In non-strict mode, durations must currently be constant
     * (variable non-strict durations are future work).
     *
     * A task <em>i</em> is active at time <em>t</em> iff
     * <em>starts[i] &le; t &lt; starts[i] + lengths[i]</em>. For every pair of
     * distinct tasks one of them must finish before the other starts: either
     * <em>starts[i] + lengths[i] &le; starts[j]</em> or
     * <em>starts[j] + lengths[j] &le; starts[i]</em>.
     *
     * The <em>strict</em> flag controls how zero-length tasks are handled.
     * In strict mode (the default), zero-length tasks must still respect the
     * pairwise non-overlap clause &mdash; equivalent to MiniZinc's
     * <code>disjunctive_strict</code>, XCSP3's <code>zeroIgnored = false</code>,
     * and CPMpy's <code>NoOverlap</code>. In non-strict mode, zero-length
     * tasks are dropped at install time and place no constraint on the other
     * tasks &mdash; equivalent to MiniZinc's <code>disjunctive</code> and
     * XCSP3's <code>zeroIgnored = true</code>. With constant durations the
     * distinction is fully resolved at construction; with variable durations a
     * task may become zero-length during search.
     *
     * Tasks may also be <em>optional</em>: the constructor taking a `presences`
     * array makes task <em>i</em> conditional on a {0, 1} variable. A task with
     * <em>presences[i] = 0</em> is absent &mdash; it occupies no time, so it may
     * overlap anything and its start is unconstrained. The presence appears in
     * the encoding as one more disjunct on each separation clause the task takes
     * part in, and nowhere else, so a task posted with
     * <em>presences[i] = 1</em> and one posted without presences at all produce
     * the same OPB.
     *
     * Propagation is time-table consistent at heights = 1, capacity = 1:
     * mandatory parts of distinct tasks may not overlap, and each task's
     * bounds are pushed away from time points already mandatorily occupied
     * by another. On top of that, <em>detectable precedences</em> order the
     * pairs whose ordering the bounds already force &mdash; which needs no
     * mandatory part on either task, so it prunes where time-tabling cannot.
     * Stronger reasoning (an overload check, not-first / not-last,
     * edge-finding) is left for future work.
     *
     * A task whose presence is still undecided is left out of the profile and
     * out of every push, in either role: it blocks nothing, and nothing is
     * inferred about its start, since a prune that is only valid when the task
     * is present would be wrong if it turns out absent. If no start at all is
     * left for such a task under the profile, its presence is inferred to be 0.
     *
     * \ingroup Constraints
     */
    class Disjunctive : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _starts;
        std::vector<IntegerVariableID> _lengths;
        bool _strict = true;
        std::vector<std::size_t> _active_tasks;

        // Per-task presence, as posted; empty for the constructors that take no
        // presences, where every task is unconditionally present. Resolved into
        // _presence by prepare(); this copy exists for clone() and s_expr().
        std::vector<IntegerVariableID> _presences;

        // Per-task presence as resolved by innards::task_presence: nullopt for a
        // task that is unconditionally present --- the non-optional
        // constructors, or a presence argument that is the constant 1 --- which
        // then needs no disjunct in its separation clauses and no presence
        // literal in a reason, so it encodes and propagates exactly as it did
        // before optional tasks existed. A task whose presence is the constant 0
        // is dropped from _active_tasks and appears nowhere at all. Only
        // *constant* presences resolve: a checker reads the OPB, not the initial
        // State, so a variable whose domain happens to be a singleton keeps its
        // disjunct.
        std::vector<std::optional<IntegerVariableID>> _presence;

        // Length snapshots resolved in prepare(). _length_vals holds the
        // constant value for a constant duration (0 placeholder for a variable
        // one, where _lengths[i] is read from the state instead).
        std::vector<Integer> _length_vals;

        // Encoded pairwise reified before-flags. The OPB stays purely
        // declarative: for each ordered pair (i, j) of active tasks,
        // before_{i,j} <-> s_i + l_i <= s_j, plus one clause per unordered
        // pair. Line numbers are stored so the propagator's justifications
        // can pol against them.
        struct BeforeFlagData
        {
            innards::ProofFlag flag;
            innards::ProofLine forward_line;
            innards::ProofLine reverse_line;
        };
        std::map<std::pair<std::size_t, std::size_t>, BeforeFlagData> _before_flags;
        std::map<std::pair<std::size_t, std::size_t>, innards::ProofLine> _clause_lines;

        // Non-strict mode: whether each task gets a zero-length escape in the
        // separation clause -- every variable-duration task does, matching
        // cake_pb_cp (std::uint8_t rather than the vector<bool> bitset
        // specialisation) -- and, for those tasks, the reified "duration <= 0"
        // escape flag itself (a zero-length task does not constrain in
        // non-strict mode).
        std::vector<std::uint8_t> _zero_escape;
        std::vector<std::optional<innards::ProofFlag>> _zero;

        DisjunctiveRules _rules;
        innards::DisjunctiveProofMutation _proof_mutation = innards::disjunctive_proof_mutation::None{};
        innards::DisjunctivePresenceMutation _presence_mutation = innards::disjunctive_presence_mutation::None{};

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        /**
         * \brief General form: durations may be variables or constants
         * (constants pass through as ConstantIntegerVariableID).
         */
        explicit Disjunctive(std::vector<IntegerVariableID> starts, std::vector<IntegerVariableID> lengths);

        /**
         * \brief Convenience form for constant durations. Delegates to the
         * general constructor.
         */
        explicit Disjunctive(std::vector<IntegerVariableID> starts, std::vector<Integer> lengths);

        /**
         * \brief Optional-task form: `presences[i]` is a {0, 1} variable saying
         * whether task `i` happens at all. An absent task occupies no time and
         * has an unconstrained start.
         *
         * Each presence must be a variable whose domain is within {0, 1}, or
         * the constant 0 or 1. A constant 1 is the same as leaving the task out
         * of the optional form entirely, and encodes identically.
         *
         * \throws InvalidProblemDefinitionException if a presence's domain is
         * not within {0, 1}, or if the arrays' sizes disagree.
         */
        explicit Disjunctive(std::vector<IntegerVariableID> starts, std::vector<IntegerVariableID> lengths, std::vector<IntegerVariableID> presences);

        /// Whether the tasks are strictly disjunctive (zero-length tasks also may
        /// not overlap); default true. Takes std::optional<bool> so a runtime flag
        /// can be passed straight through.
        auto with_strict(std::optional<bool> strict = true) -> Disjunctive &;

        /// Select which propagation rules are enabled (all of them, by
        /// default). Propagation strength only: the solutions found and the OPB
        /// encoding are the same whatever is selected.
        auto with_rules(DisjunctiveRules rules) -> Disjunctive &;

        /// Corrupt one step of the detectable-precedence derivation. For tests
        /// only, which assert that VeriPB rejects the result; see
        /// innards::DisjunctiveProofMutation.
        auto with_proof_mutation(innards::DisjunctiveProofMutation mutation) -> Disjunctive &;

        /// Corrupt one step of the presence-falsification derivation. For tests
        /// only, which assert that VeriPB rejects the result; see
        /// innards::DisjunctivePresenceMutation.
        auto with_presence_mutation(innards::DisjunctivePresenceMutation mutation) -> Disjunctive &;

        /**
         * \brief The presences this constraint was posted with.
         *
         * Empty for the non-optional constructors, which is how a caller asks
         * "is this an optional-task Disjunctive?".
         */
        [[nodiscard]] auto presences() const -> const std::vector<IntegerVariableID> &;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
