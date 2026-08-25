#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_CUMULATIVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_CUMULATIVE_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/innards/cumulative_mutations.hh>
#include <gcs/innards/proofs/constraint_proof_model_data.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_only_variables-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <map>
#include <optional>
#include <variant>
#include <vector>

namespace gcs
{
    /**
     * \brief Which OPB encoding a Cumulative writes.
     *
     * Unlike \ref CumulativeRules, this *does* change what goes into the OPB.
     * It changes nothing else: the solutions found, the inferences made and
     * the certificates emitted are the same whichever is chosen, because
     * nothing yet derives anything from what the second arm adds.
     *
     * \ingroup Constraints
     */
    enum class CumulativeEncoding
    {
        /// The per-time family alone: three fully reified flags per (task,
        /// time point) over each task's possible-active window, and one
        /// capacity row per time point. `O(n x horizon)`, and what every
        /// inference cites today.
        TimeIndexed,

        /// The per-time family, and the start-checkpoint family beside it:
        /// per ordered pair of tasks, flags saying whether one is running when
        /// the other starts, and one capacity row per task. `O(n^2)` and free
        /// of the horizon, which is the point of issue #780.
        ///
        /// Emitting both is how the second is checked before anything is
        /// derived from it --- a checkpoint row that says too much is a
        /// solution veripb refuses --- and it is not a state to stay in.
        /// Deriving the per-time rows from the checkpoints, and then dropping
        /// the per-time family, is the rest of #780; a `StartCheckpoint` arm
        /// arrives with that recovery, and cannot work before it, since an
        /// unconverted inference would have no per-time row left to cite.
        ///
        /// **What it costs to have both.** More model is more for unit
        /// propagation to reach, so a certificate step that was load-bearing
        /// against the per-time family alone need not be against the two
        /// together. That is not hypothetical: three of Cumulative's mutation
        /// fixtures write corrupted proofs that veripb rejects under
        /// \ref TimeIndexed and accepts under this. So a mutation lane is
        /// registered here only where it still discriminates, and an honest
        /// certificate developed under this arm has been checked more weakly
        /// than one developed under \ref TimeIndexed.
        Both
    };

    /**
     * \brief Which of Cumulative's propagation rules are enabled.
     *
     * All three are on by default. Turning one off weakens propagation but
     * never changes the solutions found, and never changes the OPB encoding:
     * these select propagation strength only, and exist so that a test can
     * attribute an inference to the rule that made it (and so that a fixture
     * can show a rule is load-bearing by watching the search get worse without
     * it).
     *
     * \ingroup Constraints
     */
    struct CumulativeRules
    {
        /// Time-table: the mandatory-part load profile, its overflow
        /// contradiction and the bound pushes away from blocked times.
        bool time_table = true;

        /// The overload check: a window whose fully-contained tasks carry more
        /// energy than the window supplies is infeasible. Conflict-only.
        bool overload = true;

        /// Strengthen the overload check with the mandatory-part load of tasks
        /// that are *not* fully contained in the window (rule (TTOC)). Has no
        /// effect unless \ref overload is also set.
        bool profile_overload = true;

        /// Cap what the window supplies at each individual time point by what
        /// the tasks there could actually take: the *horizontally elastic*
        /// overload check, combined with the time table (rule (TTHE-OC),
        /// Kameugne et al. 2024; the formulation is Cloutier & Quimper's
        /// equivalent one, CP 2026 §2.2.5).
        ///
        /// (TTOC) charges the whole window `capacity · width` and subtracts the
        /// profile. That over-supplies a time point which no task can reach
        /// with more than its own tasks' heights: a resource nobody can use is
        /// not available. Capping each time point separately is what makes this
        /// rule strictly stronger, and it is why the certificate sums a *line
        /// per time point* rather than one bulk supply term.
        ///
        /// Has no effect unless \ref overload is also set, and wants
        /// \ref profile_overload alongside it, since the cap is stated against
        /// what the profile leaves.
        bool elastic_overload = false;

        /// Cap the same per-time-point supply by *integrality* as well: the
        /// tasks that could run at a time point have integer heights, so the
        /// resource they can between them consume is the largest subset sum of
        /// those heights that fits under what the profile leaves --- not that
        /// figure itself. This is the knapsack-augmented overload check
        /// (Cloutier & Quimper, CP 2026), and it dominates \ref
        /// elastic_overload, which it therefore implies.
        ///
        /// The certificate is the same one, with each time point's line put
        /// through the subset-sum strengthening utility. Off by default: the
        /// cap has to be recomputed as the window's task set grows, and the
        /// derivation costs a layer of proof flags per reachable partial sum at
        /// every time point whose slack the conflict actually needs.
        bool knapsack_overload = false;

        /// Edge-finding: if a window's contained tasks plus one more task with
        /// one end inside it cannot all fit, that task must run past the end it
        /// hangs off, and the bound at that end moves by the energy the window
        /// has no room for. Unlike the overload check this moves a bound, and
        /// it runs over the same window sweep.
        ///
        /// Certified, in both directions. Off by default because the sweep that
        /// finds the firings is O(n^3) and taxes the solve whether or not
        /// anything fires (#742); the inferences themselves cost nothing
        /// measurable.
        bool edge_finding = false;

        /// Strengthen edge-finding with the mandatory-part load of the tasks
        /// that are *not* fully contained in the window, exactly as \ref
        /// profile_overload does for the overload check: time-table extended
        /// edge-finding (TTEF). Has no effect unless \ref edge_finding is also
        /// set, and wants \ref profile_overload set alongside it, since a
        /// window the profile already overloads is left to the overload check.
        ///
        /// Certified, by edge-finding's certificate plus the mandatory
        /// (task, time) pins the overload check already emits.
        bool time_table_edge_finding = false;

        /// Count every task's *guaranteed* energy inside the window --- the
        /// least overlap its execution interval can have with the window, over
        /// the start positions its bounds still allow --- rather than a
        /// contained task's whole energy plus a non-contained one's mandatory
        /// part. This subsumes \ref time_table_edge_finding: a contained task's
        /// guaranteed energy is its whole energy, and a non-contained one's is
        /// at least its mandatory part in the window, and usually more. It is
        /// also exactly what the window-energy lemma derives, so unlike the
        /// mandatory-part form it needs no per-(task, time) pins.
        ///
        /// Only tasks eligible for the overload check contribute --- which
        /// asks that a task's start (and a variable length) be a plain
        /// variable with an order encoding for the lemma's bridges to cancel
        /// against, and *not* that its length and height be constants: since
        /// #689 a variable length is counted over `[start, start + lb(length))`
        /// and a variable height at its guaranteed contribution. Takes
        /// precedence over \ref time_table_edge_finding when both are set.
        ///
        /// **Certified**, and more cheaply than \ref time_table_edge_finding:
        /// every contribution is one guarded window-energy row, guarded by the
        /// task's own bounds, which the reason carries whether or not the
        /// window contains the task. Where TTEF pays 2.93 reason-backed pin
        /// lines per firing for its profile term, this pays none.
        ///
        /// The rows it cites for a task the window does *not* contain are
        /// keyed on bounds that move, where a contained task's guards come
        /// from the window and are the same at every node. So they are derived
        /// far more often than they are reused, and whether weakening them
        /// deliberately --- buying reuse at the price of a looser bound --- is
        /// worth it is the experiment #755 leaves open.
        ///
        /// Off by default because it is a sweep a solve that never fires it
        /// still pays, not because it is weak: on `data_bl` + `data_pack` it
        /// is the strongest arm in the table at **0.667x** edge-finding's
        /// recursions against TTEF's 0.749x. Those are recursions rather than
        /// wall times, and `dev_docs/cumulative-proof-logging.md` records that
        /// recomputing the sum per window is not paid for on that family.
        bool energetic_edge_finding = false;

        /// Not-first / not-last: a task that cannot start before every task the
        /// window contains has ended must start after the earliest of those
        /// ends, and a task that cannot end after every one of them has started
        /// must end before the latest of those starts.
        ///
        /// The thresholds are the set's own `min ect` and `max lst` rather than
        /// a figure computed from the leftover energy, which is what makes this
        /// a different rule from edge-finding rather than a weaker one: it can
        /// fire on a task that *spans* the window, where edge-finding's closed
        /// form does not apply and which \ref edge_finding therefore skips.
        /// Where a task has one end inside the window, edge-finding pushes at
        /// least as far, and the live-bound check drops the duplicate: measured
        /// over the benchmark set, *every* firing is on a spanning task.
        ///
        /// Certified, by edge-finding's certificate unchanged. Off by default
        /// because it is not worth its scan: it fires in the millions and buys
        /// 0.3% of the search, and at a 60 s timeout it closes fewer instances
        /// than leaving it off.
        ///
        /// The detection is what the window-energy lemma can *derive* --- the
        /// least overlap the pushed task can have with the window over the
        /// negated conclusion's whole start range --- where the published rules
        /// take the overlap at one end of that range. So this is a weakening of
        /// them, sound and certified but firing less often. See #746.
        bool not_first_not_last = false;

        /// Run the **published** not-first / not-last detection instead of
        /// \ref not_first_not_last's, over the papers' own window.
        ///
        /// Schutt &amp; Wolf (CP 2010, Proposition 1) and Kameugne et al.
        /// (CPAIOR 2018, rule (NF)) take the pushed task's overlap at *one end*
        /// of the negated conclusion's start range, and do not clamp it against
        /// the task's own far bound; ours is the least overlap over that whole
        /// range, which is what the window-energy lemma derives. The two are
        /// **incomparable** --- each fires where the other does not --- so this
        /// replaces the rule rather than strengthening it.
        ///
        /// **Certified, and not by the window-energy lemma.** Its argument is
        /// not one `derive_guarded_window_energy` can make --- which is what
        /// #746 asked --- and what it is instead is contiguity.
        ///
        /// **Why it is sound, which is #746's answer.** Suppose the not-first
        /// conclusion fails, so some schedule has `s_i < ECT(Omega)`. Every
        /// task in `Omega` has `ect_j > s_i`, so any of them with energy before
        /// `s_i` is *running at* `s_i` beside `i` --- and the capacity row at
        /// that one time point then caps what `Omega` may use across the whole
        /// prefix at `C - c_i` rather than `C`. Summing that over the window is
        /// exactly the published inequality. It is a contiguity-plus-`ECT`
        /// argument at a single time point, not a window-energy one, and it is
        /// the mirror of the remark Schutt &amp; Wolf make about their
        /// pseudo-tasks. Neither paper states a standing assumption, and none
        /// is needed.
        ///
        /// **What the gap is worth**, measured here against
        /// \ref not_first_not_last over `data_bl` + `data_pack`: **0.991x the
        /// summed recursions, 0.999x the median**, better on 23 of the 37
        /// instances every arm closes and worse on none --- and on top of
        /// \ref time_table_edge_finding, 0.999x summed and 1.000x median,
        /// better on 13 and *worse on 3*. The single largest instance carries
        /// 46% of the summed saving. So the gap between the published detection
        /// and the certifiable one is worth **under 1% of the search**, which
        /// is what #757 found on the disjunctive encoding by a different route.
        /// Neither detection pays for its own sweep: at 60 s both close fewer
        /// instances than leaving the rule off --- which is why this is off by
        /// default, and the only reason it is.
        ///
        /// **What the certificate costs.** One row per (contained task, prefix
        /// time) saying a task running earlier is still running at the meeting
        /// point, plus a pin putting the pushed task there beside it. Where
        /// `ect_j >= ECT(Omega)` one pol does the whole rule. Where it does
        /// not, no single time point is where both are running --- the meeting
        /// point is `s_j` itself, which is a variable --- and the derivation
        /// becomes a chain walking the bound up `p_j` at a time, in the way the
        /// time-table push already does. The mirror reads the same sentence
        /// backwards, over `LST(Omega)` and the suffix.
        bool not_first_not_last_published = false;
    };

    /**
     * \brief Cumulative constraint: tasks with start times, durations, and
     * demands, sharing a resource of a given capacity. Any of the durations,
     * demands, and the capacity may be variables or constants (constants are
     * passed as ConstantIntegerVariableID). At every time point the sum of
     * demands of currently-active tasks must not exceed the capacity.
     *
     * A task <em>i</em> is active at time <em>t</em> iff
     * <em>starts[i] &le; t &lt; starts[i] + lengths[i]</em>.
     *
     * Tasks may also be <em>optional</em>: the constructor taking a `presences`
     * array gives each task a {0, 1} variable, and a task with
     * <em>presences[i] = 0</em> is absent &mdash; it is never active, so it
     * consumes no resource and its start time is unconstrained. The presence
     * variables are ordinary problem variables, so a model can constrain them
     * and optimise over them (maximising the number of scheduled tasks is the
     * motivating use). A task <em>i</em> is then active at <em>t</em> iff
     * <em>presences[i] = 1</em> and
     * <em>starts[i] &le; t &lt; starts[i] + lengths[i]</em>.
     *
     * Propagation is time-table consistent. For each task, the
     * <em>mandatory part</em> is the interval
     * <em>[ub(start), lb(start) + lb(length))</em> &mdash; the time it must
     * occupy regardless of where exactly it starts. Summing the guaranteed
     * demands (lb(height)) over mandatory parts gives a load profile; if that
     * profile exceeds the largest allowed capacity (ub) anywhere, the
     * constraint is infeasible. Each task's bounds are pushed away from any
     * time point where placing it would force the load over capacity. On top of
     * that an <em>overload check</em> runs by default, strengthened by the
     * profile (rule (TTOC)). Stronger reasoning still --- the knapsack and
     * horizontally elastic overload rungs, edge-finding, its time-table and
     * energetic forms, and not-first / not-last --- is behind the flags in
     * \ref CumulativeRules, off by default because each costs a sweep that a
     * solve never firing it still pays. What each rule's certificate rests on
     * --- and, where that is not the window-energy lemma, what it is instead
     * --- is stated on its own flag.
     *
     * A task whose presence is still undecided is left out of the profile and
     * out of the overload check's energy set entirely, and its own start bounds
     * are never pruned (there is no conditional-bounds store, so a prune valid
     * only if the task is present would be unsound). What it does get is the
     * mirror-image inference: when no start position left in its domain fits
     * under the profile, its presence is inferred to be 0.
     *
     * \ingroup Constraints
     */
    class Cumulative : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _starts;
        std::vector<IntegerVariableID> _lengths;
        std::vector<IntegerVariableID> _heights;
        IntegerVariableID _capacity;
        // Per-task presence, as posted; empty for the constructors that take no
        // presences, where every task is unconditionally present. Resolved into
        // _presence by prepare(); this copy exists for clone() and s_expr().
        std::vector<IntegerVariableID> _presences;
        // Snapshots resolved in prepare(). For each of lengths and heights,
        // _*_vals holds the constant value for a constant argument (and 0 for a
        // variable one, where the variable / _contrib_flags is used instead) and
        // _*_ub holds the initial upper bound (used to size the possible-active
        // window / contrib domain and to filter tasks that can never load).
        // _length_lb holds the initial length lower bound, used with lb(start)
        // to give the proof-only end = s + l proxy its true lower bound (which
        // is negative when a start can begin far enough before time 0).
        std::vector<Integer> _length_vals;
        std::vector<Integer> _length_lb;
        std::vector<Integer> _length_ub;
        std::vector<Integer> _height_vals;
        std::vector<Integer> _height_ub;
        Integer _capacity_val;
        // Resolved in prepare(). nullopt for a task that is unconditionally
        // present --- the non-optional constructors, or a presence argument that
        // is the constant 1 --- which then needs no presence conjunct in its
        // active flag and no presence literal in a reason, so it encodes and
        // propagates exactly as it did before optional tasks existed. A task
        // whose presence is the constant 0 is dropped from _active_tasks
        // instead: it can never be active, so it contributes nothing to any
        // capacity row. Only *constant* presences are resolved this way; a
        // variable that happens to be fixed at prepare() time keeps its
        // conjunct, because the OPB has to stand on its own and it is the OPB,
        // not the initial State, that a checker reads.
        std::vector<std::optional<IntegerVariableID>> _presence;
        innards::CumulativePresenceMutation _presence_mutation = innards::cumulative_presence_mutation::None{};
        std::vector<std::size_t> _active_tasks;
        std::vector<Integer> _per_task_t_lo;
        std::vector<Integer> _per_task_t_hi;
        CumulativeRules _rules;
        // nullopt until with_encoding() is called, which is how "take the
        // default" is told apart from "asked for the default": the default is
        // the environment's, and resolving it here in the constructor would
        // read it before a test had a chance to set it.
        std::optional<CumulativeEncoding> _encoding;
        innards::CumulativeProofMutation _proof_mutation = innards::cumulative_proof_mutation::None{};
        // Overload checking, resolved in prepare(). _overload_tasks lists the
        // tasks the window-energy lemma can speak about (constant length and
        // height, and a start whose order literals the lemma can bridge to);
        // _time_slot_prefix[t − _time_slot_lo] counts the time points strictly
        // below t at which some task can be active, which is exactly where
        // define_proof_model writes a per-time capacity line. A window's supply
        // is its capacity times that count: a time point no task can occupy
        // supplies nothing to the window's tasks and has no line to cite.
        std::vector<std::size_t> _overload_tasks;
        std::vector<Integer> _time_slot_prefix;
        Integer _time_slot_lo = 0_i;

        // Filled in by define_proof_model; consumed by install_propagators.
        // Each [task_idx] is indexed by t − _per_task_t_lo[i].
        std::vector<std::vector<innards::ProofFlag>> _before_flags;
        std::vector<std::vector<innards::ProofFlag>> _after_flags;
        std::vector<std::vector<innards::ProofFlag>> _active_flags;
        // Per (variable-height task, t) load contribution contrib = h·active,
        // linearised over cake's per-bit contribution flags v[id][i_t_k][cc]
        // (weight 2^k), so contrib = Σ 2^k·cc_k. Indexed [task][t_idx][bit];
        // empty middle vector for tasks whose height is constant (those use
        // h·active directly in C_t).
        std::vector<std::vector<std::vector<innards::ProofFlag>>> _contrib_flags;
        // For a task whose start AND length both vary, a proof-only end = s + l
        // introduced INSIDE the proof (a conservative extension, with no OPB
        // encoding): cake reifies `after` on s + l directly, so end has no cake
        // counterpart to match. The proof initialiser bit-defines end (via
        // ProofLogger::introduce_bits_of) and emits a per-(i,t) bridge lemma
        // `end ≥ t+1 → after`, which keeps the single-variable-in-end after pin
        // RUP-closable even though `after` is reified on the two-variable s + l.
        // nullopt for all other tasks.
        std::vector<std::optional<innards::ProofOnlySimpleIntegerVariableID>> _end;
        std::map<Integer, innards::ProofLine> _capacity_lines; // t -> proof line for the per-t time-table constraint

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        /**
         * \brief General form: lengths, heights, and capacity may be variables
         * or constants (constants pass through as ConstantIntegerVariableID).
         */
        explicit Cumulative(std::vector<IntegerVariableID> starts, std::vector<IntegerVariableID> lengths, std::vector<IntegerVariableID> heights,
            IntegerVariableID capacity);

        /**
         * \brief Convenience form for the all-constant case (variable starts,
         * constant lengths, heights, and capacity). Delegates to the general
         * constructor.
         */
        explicit Cumulative(std::vector<IntegerVariableID> starts, std::vector<Integer> lengths, std::vector<Integer> heights, Integer capacity);

        /**
         * \brief Optional-task form: `presences[i]` is a {0, 1} variable saying
         * whether task <em>i</em> is scheduled at all. An absent task is never
         * active, consumes no resource, and has an unconstrained start.
         *
         * Each presence must be a variable whose domain is within {0, 1}, or
         * the constant 0 or 1. Passing the constant 1 is the same constraint as
         * leaving the task out of the optional form entirely, and encodes
         * identically; the constant 0 drops the task.
         *
         * \throws InvalidProblemDefinitionException if a presence's domain is
         * not within {0, 1}, or if the array lengths disagree.
         */
        explicit Cumulative(std::vector<IntegerVariableID> starts, std::vector<IntegerVariableID> lengths, std::vector<IntegerVariableID> heights,
            std::vector<IntegerVariableID> presences, IntegerVariableID capacity);

        /// Select which propagation rules are enabled (all of them, by
        /// default). Propagation strength only: the solutions found and the OPB
        /// encoding are the same whatever is selected.
        auto with_rules(CumulativeRules rules) -> Cumulative &;

        /**
         * \brief Select which OPB encoding is written (see
         * CumulativeEncoding). Proof model only: the solutions found and the
         * inferences made are the same either way.
         *
         * Takes precedence over the `GCS_CUMULATIVE_ENCODING` environment
         * variable, which is what selects the encoding for a constraint that
         * does not call this --- and so is how a whole fixture set is run
         * under the other arm without touching the places it builds its
         * Cumulatives.
         */
        auto with_encoding(CumulativeEncoding encoding) -> Cumulative &;

        /// Corrupt one step of the overload check's derivation. For tests
        /// only, which assert that VeriPB rejects the result; see
        /// innards::CumulativeProofMutation.
        auto with_proof_mutation(innards::CumulativeProofMutation mutation) -> Cumulative &;

        /// Corrupt one step of the presence-falsification derivation. For tests
        /// only, which assert that VeriPB rejects the result; see
        /// innards::CumulativePresenceMutation.
        auto with_presence_mutation(innards::CumulativePresenceMutation mutation) -> Cumulative &;

        /**
         * \name The arguments this constraint was posted with.
         *
         * As posted, not as resolved: a constant length, height or presence
         * comes back as the ConstantIntegerVariableID it went in as. A caller
         * wanting bounds should ask the State, which is the only thing that
         * knows them at the point the caller is asking.
         */
        ///@{
        [[nodiscard]] auto starts() const -> const std::vector<IntegerVariableID> &;
        [[nodiscard]] auto lengths() const -> const std::vector<IntegerVariableID> &;
        [[nodiscard]] auto heights() const -> const std::vector<IntegerVariableID> &;
        /// Empty for the non-optional constructors, which is how a caller asks
        /// "is this an optional-task Cumulative?" --- and what a deriver hands
        /// straight to derived_cumulative_tasks_from, whose default argument
        /// says the same thing.
        [[nodiscard]] auto presences() const -> const std::vector<IntegerVariableID> &;
        [[nodiscard]] auto capacity() const -> IntegerVariableID;
        ///@}

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };

    /**
     * \brief What Cumulative publishes for other proof steps to build on: its
     * per-time capacity rows, and the keys of its per-(task, time) flags.
     *
     * Public API, in the sense #603 established: a derived Cumulative
     * (install_derived_cumulative) builds `pol`s on the capacity rows and pins
     * the flags, so changing what these name is a breaking change. cake_pb_cp
     * re-derives the same names, so it is a cross-tool break rather than merely
     * an internal one.
     *
     * Unlike a comparison or a linear inequality, there is no single primary
     * row to publish --- the capacity rows are a family, one per time point ---
     * so primary_row_role is honestly nullopt and \ref capacity_row_role is
     * what a citer wants.
     */
    template <>
    struct innards::ConstraintProofModelData<Cumulative>
    {
        /**
         * \brief Always nullopt: a Cumulative's rows are a per-time family, and
         * no one of them is the row a citer could mean.
         */
        [[nodiscard]] static auto primary_row_role(const Cumulative &) -> std::optional<std::string>;

        /**
         * \brief The role of the row saying the load at time `t` is within the
         * capacity: `Σ heights[i]·active[i,t] ≤ capacity`.
         *
         * A row exists for each time point some task can occupy; ask
         * NamesAndIDsTracker::constraint_row_label whether this one did.
         */
        [[nodiscard]] static auto capacity_row_role(Integer t) -> std::string;

        /**
         * \name The keys of the per-(task, time) flags.
         *
         * `before` is `start[i] <= t`, `after` is `start[i] + length[i] > t`,
         * and `active` is their conjunction. Ask
         * NamesAndIDsTracker::find_proof_flag_values for the flag: a key
         * outside the task's possible-active window has none, which is how a
         * citer discovers it is asking about a window the constraint did not
         * encode.
         */
        ///@{
        [[nodiscard]] static auto before_flag_key(std::size_t task, Integer t) -> innards::ProofFlagKey;
        [[nodiscard]] static auto after_flag_key(std::size_t task, Integer t) -> innards::ProofFlagKey;
        [[nodiscard]] static auto active_flag_key(std::size_t task, Integer t) -> innards::ProofFlagKey;
        ///@}

        /**
         * \brief The key of one bit of a variable-height task's linearised load
         * contribution at time `t`: the row's terms for such a task are
         * `2^bit` times these, rather than `height x active`.
         *
         * How many bits there are is a fact about the height's initial upper
         * bound, and is not published separately: ask
         * NamesAndIDsTracker::find_proof_flag_values for bit zero, one, two and
         * so on until it has none, which is the same "is it there?" question a
         * citer asks about every other key here. A constant-height task has
         * none at all.
         */
        [[nodiscard]] static auto contribution_flag_key(std::size_t task, Integer t, Integer bit) -> innards::ProofFlagKey;

        /**
         * \name The rows defining a variable-height task's linearised load
         * contribution at time `t`.
         *
         * Three halves of one statement: `ge` and `le` say the contribution
         * *is* the height while the task is active, and `zero` says it is
         * nothing while it is not. The `ge` one is what converts such a task's
         * bit terms back into `lb(height) x active` for a constraint derived
         * over this one, which is all anything cites today; the other two are
         * published because they are the same family, in the way `before` and
         * `after` are published beside `active`.
         *
         * These are `cake_pb_cp`'s own names for the rows, as
         * \ref capacity_row_role is: cake emits all three under the same
         * labels, over the same terms, so a proof citing one resolves against
         * its re-derived OPB as well as against ours. Renaming them is
         * therefore a cross-tool break rather than an internal one.
         *
         * A constant-height task has none. Ask
         * NamesAndIDsTracker::constraint_row_label, which is how a citer
         * discovers that.
         */
        ///@{
        [[nodiscard]] static auto contribution_ge_row_role(std::size_t task, Integer t) -> std::string;
        [[nodiscard]] static auto contribution_le_row_role(std::size_t task, Integer t) -> std::string;
        [[nodiscard]] static auto contribution_zero_row_role(std::size_t task, Integer t) -> std::string;
        ///@}

        /**
         * \brief The role of the line saying the proof-only end proxy for this
         * task is at least its start plus its length.
         *
         * This is the one publication here that is not about the OPB: a task
         * whose start and length both vary has its `after` flag reified on the
         * two-variable `start + length`, which no RUP reaches from the
         * operands' bounds, so the propagator goes through a proof-only
         * `end = start + length` instead --- and the line handing it that
         * variable's lower bound is what any pin of `after` has to be built on.
         * The install initialiser derives it, so ask
         * NamesAndIDsTracker::find_derived_line rather than
         * constraint_row_label.
         *
         * Nullopt from there means the same thing it means for a flag: there is
         * nothing to cite, so do not do the thing that would need citing. A
         * constant length or a constant start needs no proxy and publishes
         * none; nor does a proof written with assertions on, which omits the
         * definition along with everything else it asserts.
         */
        [[nodiscard]] static auto end_lower_bound_role(std::size_t task) -> std::string;

        /**
         * \name The start-checkpoint encoding (issue #780).
         *
         * A second, `O(n^2)` and horizon-free statement of the same
         * constraint, emitted alongside the per-time family above: rather than
         * checking the capacity at every time point, check it at every time
         * point that is the start of a task which could occupy the resource.
         * The load profile is a step function that only rises at such a start,
         * so a time point over capacity is dominated by the last one at or
         * before it, and checking every start checks every peak.
         *
         * Nothing cites these yet --- they are here to be checked against the
         * family that is load-bearing before anything is derived from them.
         * Deriving the per-time rows from these, and deleting the per-time
         * block, is the rest of #780.
         *
         * These are not `cake_pb_cp`'s names, as
         * \ref capacity_row_role and the contribution roles are: cake has no
         * start-checkpoint encoder to conform to. When one is asked for, these
         * are the names to offer it.
         */
        ///@{

        /**
         * \brief The role of the row saying the load at the time task `j`
         * starts is within the capacity:
         * `Sum_i heights[i] . active[i,j] <= capacity`.
         *
         * A row exists for each task that could raise the load profile at all;
         * ask NamesAndIDsTracker::constraint_row_label whether this one did.
         */
        [[nodiscard]] static auto checkpoint_row_role(std::size_t task) -> std::string;

        /**
         * \name The keys of the per-(task, task) flags.
         *
         * `before[i,j]` is `start[i] <= start[j]`, `after[i,j]` is
         * `start[i] + length[i] > start[j]`, and `active[i,j]` is their
         * conjunction (with the presence of `i`, where it has one): task `i`
         * is running at the moment task `j` starts.
         *
         * The diagonal is the exception. `before[j,j]` is a tautology and
         * `after[j,j]` is `length[j] >= 1`, so neither is minted, and
         * `active[j,j]` is minted only when it says something --- when `j` has
         * a variable length, or a presence. Where it says nothing, task `j` is
         * on its own row unconditionally and there is no flag to ask for. So
         * nullopt from here carries its usual meaning for `i != j` (the
         * constraint did not encode that pair) and means "the term is there
         * without a flag" on the diagonal.
         */
        ///@{
        [[nodiscard]] static auto pair_before_flag_key(std::size_t i, std::size_t j) -> innards::ProofFlagKey;
        [[nodiscard]] static auto pair_after_flag_key(std::size_t i, std::size_t j) -> innards::ProofFlagKey;
        [[nodiscard]] static auto pair_active_flag_key(std::size_t i, std::size_t j) -> innards::ProofFlagKey;
        ///@}

        /**
         * \brief The key of one bit of a variable-height task's linearised
         * load contribution at the moment task `j` starts, and the roles of
         * the three rows defining it.
         *
         * The per-time family's counterparts, said over a pair of tasks rather
         * than over a task and a time; see \ref contribution_flag_key and
         * \ref contribution_ge_row_role for what they mean. A constant-height
         * task has none, and neither does a variable-height task on a diagonal
         * whose activity flag was not minted: its contribution is its height,
         * unconditionally, and the row carries the height itself.
         */
        ///@{
        [[nodiscard]] static auto pair_contribution_flag_key(std::size_t i, std::size_t j, Integer bit) -> innards::ProofFlagKey;
        [[nodiscard]] static auto pair_contribution_ge_row_role(std::size_t i, std::size_t j) -> std::string;
        [[nodiscard]] static auto pair_contribution_le_row_role(std::size_t i, std::size_t j) -> std::string;
        [[nodiscard]] static auto pair_contribution_zero_row_role(std::size_t i, std::size_t j) -> std::string;
        ///@}

        ///@}
    };
}

#endif
