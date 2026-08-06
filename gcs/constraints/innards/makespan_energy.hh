#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_MAKESPAN_ENERGY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_MAKESPAN_ENERGY_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/reason.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <optional>
#include <variant>
#include <vector>

namespace gcs::innards::makespan_energy
{
    /**
     * \brief Deliberate corruptions of a makespan bound's derivation, for
     * testing only. VeriPB must reject each of them.
     *
     * A makespan bound is not conflict-shaped, which makes it easier to test
     * than the rest of this family: the context its derivation runs under is
     * the tasks' own bounds plus the negated conclusion, and that is
     * satisfiable, so a corrupted route reaches a line that says less than the
     * conclusion needs rather than one that is vacuously valid. What it does
     * need is a fixture whose energy beats its supply by exactly one, or an
     * understatement of a unit survives.
     *
     * \ingroup Innards
     */
    namespace makespan_energy_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Claim a makespan one larger than the energy supports. This is the
        /// signature test of a bound: a derivation with slack in it verifies
        /// whatever it concludes, and only a refused `+1` says the honest
        /// number is the one the arithmetic reaches.
        ///
        /// Two shapes, because neither works everywhere. Where a wider window
        /// would have another capacity row in it, the argument moves to that
        /// window, and comes up exactly one unit of supply short. Where it
        /// would not --- the honest window already reaching the last row ---
        /// widening changes nothing at all, so instead the honest window keeps
        /// its honest contradiction and only the *conclusion* moves: the `pol`
        /// then contradicts under `[M <= bound - 1]` while the wrapping RUP
        /// asserts under `[M <= bound]`, which is one order literal short of
        /// firing.
        ///
        /// It says that only where the honest bound is an inference rather than
        /// a refutation. Give the model a horizon *below* the bound and the
        /// honest derivation reaches a contradiction, after which every claim
        /// follows and this one verifies too --- so run it against a horizon of
        /// at least the bound, and read a verifying run there as a finding.
        struct ClaimHigherBound
        {
        };

        /// Leave the window's last capacity row out of the supply, so the
        /// resource is counted as having one time point less than the
        /// derivation argues over.
        ///
        /// Not a weakening, which is why it is worth having: the omitted row's
        /// activity terms have nothing to cancel against, so they survive with
        /// a *positive* sign and the line reached is `sum_i h_i a_{i,t} >= k`
        /// rather than a contradiction. The reverse mutation --- deriving a
        /// task's energy over a narrower window than the rows cover --- is not
        /// here for the same reason read the other way: its leftovers survive
        /// negatively, so the line stays contradictory and VeriPB rightly
        /// accepts a derivation that is merely longer than it needed to be.
        struct OmitCapacityRow
        {
        };

        /// Leave the negated conclusion out of the context the window-energy
        /// lemma derives under, so that a task's end-of-window literals are
        /// claimed without the deadline that gives them. That deadline is what
        /// makes this an argument about the makespan at all, rather than one
        /// about what the tasks' own domains already say.
        struct ForgetTheDeadline
        {
        };
    }

    using MakespanEnergyMutation = std::variant<makespan_energy_mutation::None, makespan_energy_mutation::ClaimHigherBound,
        makespan_energy_mutation::OmitCapacityRow, makespan_energy_mutation::ForgetTheDeadline>;

    /**
     * \brief The model's reason for believing a task must finish by the
     * makespan: a posted row saying `makespan - start >= bound`.
     *
     * Nothing else will do. Reverse unit propagation does not cross from the
     * makespan's bits to a start's through a linear row, whatever the bounds
     * say --- the classic reason a cutting-planes step is needed where a RUP
     * looks like it should work --- so the row itself has to be summed into the
     * derivation, and a task without one keeps only whatever energy its own
     * domain gives.
     *
     * `bound` is decided from the model and so is the same with proofs off,
     * which is what keeps the inferred bound the same either way; `row` is the
     * label naming it, and only a logger can have that.
     *
     * \ingroup Innards
     */
    struct MakespanLink
    {
        Integer bound;
        std::optional<ProofLineLabel> row;
    };

    /**
     * \brief One task of the constraint whose energy bounds a makespan.
     *
     * The flag vectors and the link's label are the only proof-dependent things
     * here, and nothing the bound search reads: \ref makespan_energy_bound
     * works entirely off the geometry, so it reaches the same answer with
     * proofs off, and the same bound is inferred either way.
     *
     * \ingroup Innards
     */
    struct EnergyTask
    {
        SimpleIntegerVariableID start;

        /// Constant, as the window-energy lemma requires; `height` is what this
        /// task contributes to the constraint's capacity rows.
        Integer length, height;

        /// The window the constraint gave this task, and so the range its
        /// activity flags cover: `[lb(start), ub(start) + length - 1]` as it
        /// was when the constraint was installed.
        Integer t_lo, t_hi;

        /// What the start is currently known to lie within.
        Integer start_lb, start_ub;

        /// The model row confining this task to the window, if there is one:
        /// under a makespan of `hi` the start is at most `hi - link->bound`.
        /// Without it the task is confined only by `start_ub`, and every time
        /// point between that and the window's end costs a unit of its energy
        /// --- as does every unit by which the row's `bound` falls short of the
        /// task's own length.
        std::optional<MakespanLink> link = std::nullopt;

        /// The task's per-time flags, as window_energy::ConstantLengthTask
        /// describes them, or null with proofs off.
        const std::vector<ProofFlag> * before = nullptr;
        const std::vector<ProofFlag> * after = nullptr;
        const std::vector<ProofFlag> * active = nullptr;
    };

    /**
     * \brief A makespan lower bound the energy argument reaches, and the window
     * it reaches it over.
     *
     * \ingroup Innards
     */
    struct MakespanBound
    {
        /// What to infer: the makespan is at least this.
        Integer bound;

        /// The window the derivation argues over, half-open. `hi` is
        /// `bound - 1`: the largest makespan the argument refutes.
        Integer lo, hi;

        /// Whether a window one time point wider would have a capacity row to
        /// go with it. False when the window already reaches the last row ---
        /// which is only of interest to \ref makespan_energy_mutation::ClaimHigherBound,
        /// whose whole trick is that a wider window supplies more.
        bool wider_supplies_more;
    };

    /**
     * \brief The strongest makespan lower bound this constraint's energy
     * supports, or nothing when it supports none better than `known_bound`.
     *
     * A schedule finishing at `mu` confines every task to `[lo, mu)`, where
     * `lo` is the earliest time any of them can be running. Between them they
     * need `sum_i height_i * length_i` units of a resource supplying `capacity`
     * per time point --- and only at the time points the constraint has a
     * capacity row for, which is what `time_slot_prefix` counts and why the
     * window's width is not what is divided by. Where the need beats the
     * supply, `mu` is refuted, and the largest refuted `mu` gives the bound.
     *
     * Both sides move with `mu`, and not in lockstep: a wider window supplies
     * more, but may also be the one that finally admits another task's whole
     * duration. So this walks every candidate rather than assuming the first
     * failure is the last. It stops at `search_up_to` or at the last time point
     * with a row, whichever is smaller: past the rows nothing changes on either
     * side, so a bound that would keep climbing there is one saying the
     * constraint has no schedule at all, and the caller's inference is what
     * should say so.
     *
     * `time_slot_prefix` and `time_slot_lo` are
     * CumulativeOverloadData's, whose prefix sums count exactly the times some
     * task can be running.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto makespan_energy_bound(const std::vector<EnergyTask> &, Integer capacity, const std::vector<Integer> & time_slot_prefix,
        Integer time_slot_lo, Integer known_bound, Integer search_up_to) -> std::optional<MakespanBound>;

    /**
     * \brief Derive a makespan lower bound from a Cumulative's capacity rows
     * and its tasks' energy.
     *
     * Everything is emitted under `reason` extended with the negated
     * conclusion, so the caller must be inferring `makespan >= bound` with
     * ThenRUP::Yes: it is that deadline which confines the tasks to the window,
     * and without it the lemma's end-of-window literals do not hold. The model
     * has to entail `start + length <= makespan` for every task, or those
     * literals are not RUP and VeriPB will say so.
     *
     * One `pol`, over the capacity rows inside the window and each task's
     * window energy scaled by its height. Every task's activity terms cancel
     * against its terms in the rows, leaving a line with nothing but negative
     * coefficients on the left and a positive right hand side --- a
     * contradiction exactly when the bound is one \ref makespan_energy_bound
     * accepted.
     *
     * \ingroup Innards
     */
    auto derive_makespan_bound(ProofLogger &, const ReasonLiterals & reason, IntegerVariableID makespan, const std::vector<EnergyTask> &,
        const std::map<Integer, ProofLine> & capacity_rows, const MakespanBound &, MakespanEnergyMutation, ProofLevel) -> void;
}

#endif
