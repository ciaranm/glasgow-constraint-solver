#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIABLE_WEIGHTING_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIABLE_WEIGHTING_HH

#include <gcs/constraint.hh>
#include <gcs/innards/conflict_observer.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <unordered_map>
#include <vector>

namespace gcs
{
    class CurrentState;

    /**
     * \brief A portable, copyable snapshot of per-constraint weights, keyed by
     * ConstraintID.
     *
     * This is the value-object seam of the dom/wdeg design: a VariableWeighting
     * can be snapshotted out to one of these, a fresh one loaded from it, and two
     * merged. Being keyed by the stable ConstraintID --- the identity a proof log
     * also names --- rather than a live dense index, it survives leaving one
     * search/thread and entering another: the basis for share-nothing parallel
     * sync and for seeding a search with proof-mined weights.
     *
     * v1 holds only global per-constraint weights; a per-(constraint, variable)
     * map for AbsCon-local schemes is a later additive extension.
     *
     * \ingroup SearchHeuristics
     */
    class WeightingState
    {
    public:
        /**
         * \brief How two WeightingStates combine, for parallel/merge sync.
         */
        enum class MergePolicy
        {
            Sum,
            Max,
            Average
        };

        /**
         * The weight recorded for a constraint, or 0.0 if it has none.
         */
        [[nodiscard]] auto weight_of(const ConstraintID &) const -> double;

        /**
         * The weight recorded for a constraint, or nullopt if it has none.
         */
        [[nodiscard]] auto optional_weight_of(const ConstraintID &) const -> std::optional<double>;

        /**
         * Set (or overwrite) the weight for a constraint.
         */
        auto set_weight(const ConstraintID &, double) -> void;

        /**
         * Combine another WeightingState into this one. For every constraint in
         * \p other, this one's weight (taken as 0 if absent) is combined with
         * other's under \p policy: Sum adds, Max keeps the larger, Average takes
         * the mean. Constraints present only in this one are left unchanged.
         */
        auto merge(const WeightingState & other, MergePolicy policy) -> void;

        /**
         * The full ConstraintID -> weight map, for iteration / serialisation.
         */
        [[nodiscard]] auto constraint_weights() const -> const std::unordered_map<ConstraintID, double> &;

    private:
        std::unordered_map<ConstraintID, double> _constraint_weights;
    };

    /**
     * \brief Live, per-search variable weighting: what a dom/wdeg-style brancher
     * reads, and what propagation notifies on a conflict.
     *
     * Implements innards::ConflictObserver (the write side, fired by
     * Propagators::propagate on a domain wipeout) and adds weighted_degree_of
     * (the read side, summed by the brancher). A VariableWeighting is owned by
     * the search driver (solve_with, or a parallel orchestrator), borrowed by
     * State for the write side and captured by the brancher for the read side.
     * Implementations store weights densely by constraint index for speed;
     * snapshot()/load() bridge that to the portable, ConstraintID-keyed
     * WeightingState.
     *
     * \ingroup SearchHeuristics
     */
    class VariableWeighting : public innards::ConflictObserver
    {
    public:
        ~VariableWeighting() override = default;

        /**
         * The weighted degree W(x) of a variable, to be combined with dom(x) by
         * the brancher. Sums the live weight over the constraints the variable
         * is in that still have at least two unassigned variables (the |fut|>1
         * filter).
         */
        [[nodiscard]] virtual auto weighted_degree_of(const CurrentState & state,
            const innards::Propagators & propagators, IntegerVariableID var) const -> double = 0;

        /**
         * Called at each restart boundary (for smoothing / decay schemes).
         * Inert until restarts land.
         */
        virtual auto on_restart() -> void = 0;

        /**
         * Read the live weights out into a portable WeightingState.
         */
        [[nodiscard]] virtual auto snapshot(const innards::Propagators & propagators) const -> WeightingState = 0;

        /**
         * Replace the live weights with those from a WeightingState (constraints
         * absent from it revert to the scheme's default).
         */
        virtual auto load(const WeightingState & state, const innards::Propagators & propagators) -> void = 0;
    };

    /**
     * \brief Common storage for weighting schemes that keep one weight per
     * constraint, indexed densely by constraint index.
     *
     * Provides the dense vector and the read / snapshot / load machinery;
     * concrete schemes supply note_conflict (the update) and on_restart, and may
     * override contribution_of to map a stored weight to a variable's weighted
     * degree (the default is the weight itself).
     *
     * \ingroup SearchHeuristics
     */
    class DenseConstraintWeighting : public VariableWeighting
    {
    public:
        [[nodiscard]] auto weighted_degree_of(const CurrentState & state,
            const innards::Propagators & propagators, IntegerVariableID var) const -> double override;

        [[nodiscard]] auto snapshot(const innards::Propagators & propagators) const -> WeightingState override;

        auto load(const WeightingState & state, const innards::Propagators & propagators) -> void override;

    protected:
        /**
         * One weight per constraint, each initialised to (and reset by load to)
         * default_weight.
         */
        DenseConstraintWeighting(const innards::Propagators & propagators, double default_weight);

        /**
         * What constraint_index contributes to a variable's weighted degree.
         * Default is its stored weight; a scheme can override (for example to add
         * an offset).
         */
        [[nodiscard]] virtual auto contribution_of(int constraint_index) const -> double;

        std::vector<double> _weights;
        double _default_weight;
    };

    /**
     * \brief Classic dom/wdeg (Boussemart, Hemery, Lecoutre, Sais, ECAI 2004):
     * one weight per constraint, initialised to 1, bumped by 1 on every domain
     * wipeout.
     *
     * weighted_degree_of(x) sums w(c) over the constraints on x with at least two
     * unassigned variables, so at the root --- every weight 1, every variable
     * unassigned --- it equals the variable's degree, and the heuristic
     * specialises as conflicts accumulate.
     *
     * \ingroup SearchHeuristics
     */
    class ClassicDomWDeg final : public DenseConstraintWeighting
    {
    public:
        explicit ClassicDomWDeg(const innards::Propagators & propagators);

        auto note_conflict(int constraint_index, const std::vector<SimpleIntegerVariableID> & scope,
            const std::optional<innards::ReasonFunction> & reason, const innards::State & state) -> void override;

        auto on_restart() -> void override;
    };

    /**
     * \brief Conflict-History Search (Habet & Terrioux, SAC 2019 / J. Heuristics
     * 2021): a recency-weighted per-constraint score.
     *
     * Each constraint has a score q(c), initialised to 0. On a conflict wiping a
     * variable of c, q(c) moves towards r(c) = 1 / (#Conflicts - Conflict(c) + 1)
     * by an exponential recency-weighted average q(c) <- (1 - alpha) q(c) + alpha
     * r(c), where alpha starts at 0.4 and decays towards 0.06 over conflicts.
     * weighted_degree_of(x) sums q(c) + delta over x's constraints with at least
     * two unassigned variables, so early on (all q(c) = 0) it orders by degree.
     * on_restart resets alpha and smooths the scores; it is inert until restarts
     * land.
     *
     * \ingroup SearchHeuristics
     */
    class ConflictHistorySearch final : public DenseConstraintWeighting
    {
    public:
        explicit ConflictHistorySearch(const innards::Propagators & propagators);

        auto note_conflict(int constraint_index, const std::vector<SimpleIntegerVariableID> & scope,
            const std::optional<innards::ReasonFunction> & reason, const innards::State & state) -> void override;

        auto on_restart() -> void override;

        auto load(const WeightingState & state, const innards::Propagators & propagators) -> void override;

    protected:
        [[nodiscard]] auto contribution_of(int constraint_index) const -> double override;

    private:
        std::vector<long long> _conflict_of; // Conflict(c): #Conflicts when c last conflicted
        long long _number_of_conflicts = 0;
        double _alpha;
    };

    /**
     * \brief Selects which weighting scheme gcs::variable_order::dom_wdeg uses.
     *
     * \ingroup SearchHeuristics
     */
    enum class WeightingScheme
    {
        Classic,              ///< ClassicDomWDeg
        ConflictHistorySearch ///< ConflictHistorySearch (recency-weighted)
    };
}

#endif
