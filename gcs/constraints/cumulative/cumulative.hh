#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_CUMULATIVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_CUMULATIVE_HH

#include <gcs/constraint.hh>
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
    };

    /**
     * \brief Deliberate corruptions of the overload check's derivation, for
     * testing only.
     *
     * A proof that verifies is necessary but not sufficient: if the honest
     * derivation has slack in it, a wrong one verifies too, and the rule's
     * arithmetic is then not being checked by anything. Each of these breaks
     * one step of the emitted derivation in a way that must make VeriPB
     * *reject* the proof; a mutation that still verifies is a finding about the
     * honest derivation, not about the mutation.
     *
     * These change nothing but the proof: the same conflicts are found, the
     * same solutions reported, and the OPB is untouched.
     *
     * \ingroup Constraints
     */
    namespace cumulative_proof_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Claim one more unit of activity than the window-energy lemma
        /// derived, for the first task in the window.
        struct OverstateWindowEnergy
        {
        };

        /// Leave the last time point's capacity line out of the conflict's
        /// pol, so the window appears to supply one time point less than the
        /// energy argument was told.
        struct OmitCapacityLine
        {
        };

        /// Derive each task's window energy over a window one time point
        /// short, which is honest but weaker than the conflict needs.
        struct ShrinkLemmaWindow
        {
        };
    }

    using CumulativeProofMutation = std::variant<cumulative_proof_mutation::None, cumulative_proof_mutation::OverstateWindowEnergy,
        cumulative_proof_mutation::OmitCapacityLine, cumulative_proof_mutation::ShrinkLemmaWindow>;

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
     * Propagation is time-table consistent. For each task, the
     * <em>mandatory part</em> is the interval
     * <em>[ub(start), lb(start) + lb(length))</em> &mdash; the time it must
     * occupy regardless of where exactly it starts. Summing the guaranteed
     * demands (lb(height)) over mandatory parts gives a load profile; if that
     * profile exceeds the largest allowed capacity (ub) anywhere, the
     * constraint is infeasible. Each task's bounds are pushed away from any
     * time point where placing it would force the load over capacity. Stronger
     * reasoning (edge-finding, energetic) is left for future work.
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
        std::vector<std::size_t> _active_tasks;
        std::vector<Integer> _per_task_t_lo;
        std::vector<Integer> _per_task_t_hi;
        CumulativeRules _rules;
        CumulativeProofMutation _proof_mutation = cumulative_proof_mutation::None{};
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

        /// Select which propagation rules are enabled (all of them, by
        /// default). Propagation strength only: the solutions found and the OPB
        /// encoding are the same whatever is selected.
        auto with_rules(CumulativeRules rules) -> Cumulative &;

        /// Corrupt one step of the overload check's derivation. For tests
        /// only, which assert that VeriPB rejects the result; see
        /// CumulativeProofMutation.
        auto with_proof_mutation(CumulativeProofMutation mutation) -> Cumulative &;

        /**
         * \name The arguments this constraint was posted with.
         *
         * As posted, not as resolved: a constant length or height comes back as
         * the ConstantIntegerVariableID it went in as. A caller wanting bounds
         * should ask the State, which is the only thing that knows them at the
         * point the caller is asking.
         */
        ///@{
        [[nodiscard]] auto starts() const -> const std::vector<IntegerVariableID> &;
        [[nodiscard]] auto lengths() const -> const std::vector<IntegerVariableID> &;
        [[nodiscard]] auto heights() const -> const std::vector<IntegerVariableID> &;
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
    };
}

#endif
