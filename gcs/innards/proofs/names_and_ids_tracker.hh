#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/proof.hh>
#include <gcs/reification.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>
#include <version>

#ifdef __cpp_lib_generator
#include <generator>
#else
#include <__generator.hpp>
#endif

namespace gcs::innards
{
    class PolBuilder;

    /**
     * Represents the lowest level of a raw PB literal that appears in an OPB file
     * or proof log.
     *
     * \ingroup Innards
     */
    struct XLiteral
    {
        long long id;
        bool negated;

        [[nodiscard]] auto operator<=>(const XLiteral &) const noexcept = default;
    };

    [[nodiscard]] inline auto operator!(const XLiteral & lit) -> XLiteral
    {
        return XLiteral{lit.id, ! lit.negated};
    }

    enum class EqualsOrGreaterEqual
    {
        Equals,
        GreaterEqual
    };

    /**
     * Why a real variable's proof-time `ge` order literal is resident (for
     * GuessHoist, transiently resident at a positive backtrack level), under
     * OrderEncodingDeletion::Literals. Threaded from the residency-deciding call sites
     * (creation in need_gevar, and the hoist primitives).
     *
     * Two consumers, with different rules:
     *
     *  - The **always-on Top-pin bookkeeping** (`ge_top_pins`), which counts how many
     *    permanent references of each cause pin a *hoisted* ge at Top. This is
     *    `evict_order_literal`'s precondition -- "the cause the caller names is the only
     *    one" -- so it cannot be diagnostic-gated, and it counts every reference rather
     *    than only the first.
     *  - The `GCS_ORDER_ENCODING_STATS` **pin-apportionment diagnostic**, which
     *    attributes each Top-resident literal to the cause that pinned it *first*, and
     *    also covers the born-Top causes (boundary, model_time, aux/view pin, frontier
     *    exemption, gate) that never hoist and so never take a pin. It splits the pins into the
     *    classes the bridge-lifetime redesign (dev_docs step 3) would free (view_pin,
     *    aux_pin) versus those it would not (eq/invar/nogood/soli hoists) versus
     *    structural ones.
     *
     * Attribution is exact (set at the deciding site) in both, never inferred from level
     * numbers.
     */
    enum class OrderEncodingResidencyCause
    {
        ModelTime,      ///< born Top: the ge atom was created before the logger attached.
        Boundary,       ///< born Top: a trivially-derivable boundary literal (need_gevar's `boundary`).
        ViewPin,        ///< born Top: whole encoding resident because the variable is a view underlying (views_of_variable).
        AuxPin,         ///< born Top: whole encoding resident via order_encoding_stays_resident (aux magnitudes).
        FrontierExempt, ///< born Top: the frontier owner exempted the variable from deletion (note_deletion_exempt).
        GateResident,   ///< born Top: the variable had not crossed the min-chain gate (order_encoding_deletion_min_chain).
        EqHoist,        ///< hoisted to Top from an eq atom's Top def (need_direct_encoding_for).
        InvarHoist,     ///< hoisted to Top from an interval-partition atom's Top def (define_plain_invar).
        NogoodHoist,    ///< hoisted to Top by emit_learned_nogood.
        SoliHoist,      ///< hoisted to Top by the objective-improvement hoist in ProofLogger::solution.
        GuessHoist      ///< hoisted to a positive backtrack level by ProofLogger::backtrack (transient; never a Top cause).
    };

    /**
     * Provides access to information about flags and variables being used in a proof.
     *
     * This is for information that is shared between a ProofModel and a ProofLogger,
     * because the lazy encoding can be introduced either in the model or inside a
     * log using extension variables.
     *
     * \ingroup Innards
     */
    class NamesAndIDsTracker
    {
    public:
        /**
         * \brief Scoped request that eq atoms minted inside it be **windowed** rather
         * than permanent, under OrderEncodingDeletion::Literals.
         *
         * A permanent eq definition -- what every caller outside this scope gets, and the
         * only thing any other mode can give -- lands at ProofLevel::Top, outlives every
         * backtrack, and pins the two `ge` thresholds it names at Top with it. A windowed
         * definition lands at ProofLevel::Current instead, so a backtrack (or the window's
         * own tidy) deletes it and retires the atom, and leaves the two `ge` thresholds it
         * names deletable. That is what bounds the resident proof objects per branched
         * variable at O(1) instead of O(domain width); see dev_docs/brancher-design.md,
         * "The eq-atom window".
         *
         * The scope is the narrow API the design asks for: only the frontier owner -- the
         * branch layer, around the guess mint -- may ask for a windowed atom, because a
         * windowed atom must not be named by any surviving Top line. **Every** other caller
         * (propagator reasons, reified constraints, need_pol_item_defining_literal) runs
         * with the scope closed and gets today's byte-identical Top behaviour, so no other
         * call site knows lifetimes exist. The request is honoured only where a deletable
         * definition is meaningful -- Literals mode, proof-writing time, assertions off, a
         * real variable, and not a variable the eq-by-interval guard refuses -- and is
         * silently ignored (leaving the definition permanent) anywhere else, which is
         * always correct and merely wins nothing.
         *
         * Has no effect on an atom that already exists: residency is decided once, when the
         * definition is emitted.
         */
        struct WindowedEqScope
        {
            explicit WindowedEqScope(NamesAndIDsTracker &);
            ~WindowedEqScope();

            WindowedEqScope(const WindowedEqScope &) = delete;
            auto operator=(const WindowedEqScope &) -> WindowedEqScope & = delete;

        private:
            NamesAndIDsTracker & _tracker;
            bool _saved;
        };

    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

        [[nodiscard]] auto allocate_flag_index() -> unsigned long long;

        // Record the PB-file rendering of a freshly-allocated XLiteral (and its
        // negation, as `~name`). Every allocate_* path calls this exactly once,
        // in both naming modes, so pb_file_string_for is a plain index.
        auto store_xlit_names(const XLiteral &, std::string name) -> void;

        // Allocate the XLiteral backing a flag, registering `verbose_name` (and
        // its negation) as the PB-file rendering. Shared by create_proof_flag
        // (which passes the `f[index][stem]` form) and make_proof_flag_named
        // (which passes a fully-formed two-level name verbatim).
        [[nodiscard]] auto allocate_flag_xliteral(ProofFlag flag, const std::string & verbose_name) -> XLiteral;

        // Create a flag whose PB-file variable name is `full_name` verbatim
        // (rather than wrapped in `f[index][...]`). The cake-conforming
        // create_proof_flag overloads build cake's `x[...]` (etc.) names and call this.
        [[nodiscard]] auto make_proof_flag_named(const std::string & full_name) -> ProofFlag;

        auto emit_proof_line_now_or_at_start(const std::function<auto(ProofLogger * const)->void> &) -> void;

        // The @label base for a variable's encoding definitions (bounds, ge/eq
        // atom reifications): `i[name]` for a real variable (matching cake_pb_cp,
        // including vector names like `i[scene[0]]` -- veripb's @label parser
        // accepts the nested brackets), `po[index]` for a proof-only variable
        // (which cake never sees, so the invented index-keyed base just has to be
        // unique -- proof-only names are not). Callers append `[role]`.
        [[nodiscard]] auto definitional_label_base(const SimpleOrProofOnlyIntegerVariableID & id) const -> std::string;

        // Emit containment edges between a newly-introduced literal [lo, hi] and its
        // immediate neighbours in the containment order among the existing range and eq
        // literals on `id`: minimal containers above (self -> parent) and, when self is
        // wider than one value, maximal contained literals below (child -> self).
        // Skip-level edges are left to transitivity. Each edge is a rup line.
        auto link_immediate_containment(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> void;

        // Define the bare range literal [lo, hi] (lo < hi): allocate its xliteral,
        // register the InRange / NotInRange condition pair, emit the red reification pair
        // against the variable's two order cuts, and add containment edges. No partition
        // maintenance and no covering; everyone other than the partition machinery goes
        // through need_invar.
        auto define_plain_invar(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> void;

        // Append the positive literal for the partition cell [lo, hi] to a covering
        // being built: the eq atom for a width-1 cell, the range literal otherwise.
        auto append_cell_literal_to(WPBSum & sum, SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> void;

        // Make `p` a cell boundary in id's interval partition, splitting the cell it
        // falls strictly inside (no-op if already a boundary): define the two halves and
        // emit the split covering `cell -> left OR right`. Requires the partition to
        // exist and lb <= p <= ub+1.
        auto ensure_partition_cut(SimpleOrProofOnlyIntegerVariableID id, Integer p) -> void;

        // First interval request for `id`: set up the always-covered partition, with a
        // singleton cell for every pre-existing eq atom (earlier per-value conclusions
        // must be reachable from later coverings), define a literal for every cell, and
        // emit the at-least-one clause over the top-level partition.
        auto init_interval_partition(SimpleOrProofOnlyIntegerVariableID id, Integer request_lo, Integer request_hi) -> void;

        // Build the pol line deriving the order-encoding chain link clause
        // (cond1 OR cond2) from the resident (Top) bit-definitions of ~cond1 and
        // ~cond2. Shared by the initial chain-link emission in need_gevar and the
        // on-demand re-emission used by the order-link deletion mode.
        [[nodiscard]] auto make_pol_chain_line(IntegerVariableCondition cond1, IntegerVariableCondition cond2) -> std::shared_ptr<PolBuilder>;

        // Emit the adjacent-threshold (lo < hi) order-encoding chain link
        // ge(hi) -> ge(lo) for a real variable. With order-link deletion on and the
        // logger attached the link lands at ProofLevel::Current (so a backtrack
        // deletes it) and is recorded as live tagged with the active proof level;
        // otherwise it lands at Top exactly as before. Model-building emissions
        // (logger not yet attached) always land at Top.
        auto emit_and_maybe_track_order_link(const SimpleIntegerVariableID & id, Integer lo, Integer hi) -> void;

        // Fast-path helper for need_gevar when a real variable's ge atom already
        // exists: reconnect the variable's entire order chain by re-emitting every
        // currently-missing adjacent-threshold link across its existing thresholds,
        // so a RUP needing multi-hop order propagation has the full chain available
        // (as the baseline keeps permanently resident). Emission fires only for
        // genuinely-missing links. No-op unless the order-link deletion mode is on.
        auto ensure_order_chain_connected(const SimpleIntegerVariableID & id) -> void;

        // --- Literals mode (OrderEncodingDeletion::Literals) ---

        // Record a real variable's ge threshold v as live. top => its def is resident
        // at Top (a model-time atom or a boundary literal): tagged level 0, never
        // forgotten, not indexed for deletion. Otherwise tagged with the active proof
        // level and indexed under it, so a forget of that level deletes and stitches it.
        auto record_live_order_literal(const SimpleIntegerVariableID & id, Integer v, bool top) -> void;

        // Record a real variable's eq atom v as a live *deletable* (windowed) definition,
        // tagged with the active proof level and indexed under it, so a forget of that
        // level deletes its def lines and retires the atom. A permanent (Top) eq
        // definition is deliberately NOT recorded: absence from live_eq_literals means
        // "resident forever", which is what every eq atom outside a window is, so the
        // index costs nothing until something windows a variable.
        auto record_live_eq_literal(const SimpleIntegerVariableID & id, Integer v) -> void;

        // Retirement pass for windowed eq definitions, driven from
        // forget_order_links_at_level alongside the ge sweep: for every eq atom whose def
        // was recorded at `level`, drop it from the live set and retire its atom out of
        // the lookup table (mirroring the ge sweep -- see forget_order_literals_at_level
        // for why retirement, rather than liveness tracking, is what enforces the naming
        // rule). Emits nothing: forget_proof_level has already del'd the lines. Eq atoms
        // carry no chain, so unlike the ge sweep there is nothing to stitch.
        auto forget_eq_literals_at_level(int level) -> void;

        // The (i-dynamic) half of the eq-by-interval guard (dev_docs/brancher-design.md,
        // "The one hidden pin"): an interval literal has just been requested on `id`, and
        // the partition / containment machinery is about to walk its eq_defs table and
        // name every eq atom from Top lines (singleton partition cells, containment
        // edges). A windowed definition sits at Current, so those Top lines would name a
        // literal the next backtrack deletes. Collapse the window first -- hoist every
        // live windowed eq definition on `id`, and the ge thresholds each names, out to
        // Top -- and leave the variable unwindowed, so nothing windows it again. The
        // static half (refusing to window a variable that already has a partition or a
        // containment tree) is in need_direct_encoding_for. A no-op for a variable with
        // no live window, which is every variable but a currently-branched one.
        auto collapse_eq_window(const SimpleOrProofOnlyIntegerVariableID & id) -> void;

        // Record a permanent (Top) reference to real variable `id`'s ge threshold `v`,
        // from the *reference site* -- the caller that is about to make (or has just
        // made) a Top line name the literal. `evict_order_literal` refuses to evict a
        // Top-resident literal unless the cause the caller names is the only one counted
        // here, so this must run on every reference, always-on under Literals.
        //
        // Two rules, both of which cost a debugging cycle to find:
        //
        //  - It runs at the reference site, NOT inside the hoist. Both
        //    hoist_order_literal_to_level (when the def is already at the target level)
        //    and hoist_order_literal_to_top_if_live (at level 0) early-return, so a
        //    second permanent atom naming an already-Top ge does no hoisting at all --
        //    and eq(v) and eq(v+1) both name ge(v+1). First-cause-wins is right for the
        //    diagnostic and fatal for an eviction precondition.
        //  - Only a ge whose Top residency a hoist *caused* gets an entry. A hoist never
        //    fires on a level-0 ge, so "level 0 with no entry" means structurally
        //    resident (model-time / boundary / aux / view / gate) -- never evictable, and
        //    needing no record. That keeps this map proportional to hoists rather than to
        //    the resident majority.
        auto note_order_literal_top_pin(const SimpleIntegerVariableID & id, Integer v, OrderEncodingResidencyCause cause) -> void;

        // Record that a chain-link (or stitch) clause over real variable `id`'s threshold
        // pair (lo, hi) was just emitted as `line`, landing at proof level `at_level`, so
        // eviction can delete every clause that names an evicted threshold. Top clauses are
        // recorded too: eviction, not forgetting, is what removes them. Always-on under
        // Literals, on the hot path of every chain emission, and emits nothing.
        auto record_live_chain_line(const SimpleIntegerVariableID & id, Integer lo, Integer hi, int at_level, const ProofLine & line) -> void;

        // Drop the record of every chain clause recorded at `level`, called from the forget
        // sweep once forget_proof_level has del'd that level's lines.
        auto forget_chain_clauses_at_level(int level) -> void;

        // Emit, at ProofLevel::Current, the two chain links joining a real variable's
        // ge threshold v to its immediate *live* neighbours (below and above). Call
        // with v not yet in the live set. Used both for a fresh proof-time literal and
        // for a re-introduced one; linking to live (not gevars) neighbours keeps the
        // chain valid across deleted thresholds.
        auto link_order_literal_to_live_neighbours(const SimpleIntegerVariableID & id, Integer v) -> void;

        // Emit the stitch link ge(hi) -> ge(lo) skipping a deleted run of thresholds,
        // recorded at at_level (= max(level(lo), level(hi))), restoring the logger's
        // active proof level to restore_level afterwards.
        auto emit_order_stitch(const SimpleIntegerVariableID & id, Integer lo, Integer hi, int at_level, int restore_level) -> void;

        // Deletion + stitch pass for the Literals mode, driven from
        // forget_order_links_at_level: for every threshold whose def was recorded at
        // `level`, stitch the surviving neighbours around each deleted run and drop the
        // thresholds from the live set.
        auto forget_order_literals_at_level(int level) -> void;

        // Part 2 of a hoist (the load-bearing caveat): re-link the just-hoisted ge
        // threshold v of a real variable to its neighbours. The links are pol-derived
        // from the two residents' defs (sound to re-emit; no witness). Assumes v is
        // already retagged to target_level in live_order_literals.
        //
        // Two neighbour policies:
        //  - !immediate_neighbours (the backtrack/nogood hoist): link to the nearest
        //    live neighbours whose level is <= target_level -- the literals that survive
        //    a forget of every deeper level -- landing each link at target_level. Right
        //    when the caller is about to forget everything deeper than target_level.
        //  - immediate_neighbours (the eq/interval-def hoist to Top): link to the
        //    *immediate* live neighbours at ANY level, landing each link at
        //    max(target_level, neighbour_level). Needed because here the deeper levels
        //    are NOT being forgotten -- interior survivors between v and its nearest
        //    Top neighbour remain live, and linking only to the Top neighbour would skip
        //    them, fragmenting the chain (a deleted-but-not-restitched adjacent link
        //    breaks the ~ge(lo) -> ~ge(hi) propagation a later backtrack-clause RUP
        //    needs). Landing the link at the neighbour's level makes it deleted together
        //    with the deletable endpoint and re-stitched by forget_order_literals_at_level.
        auto stitch_hoisted_order_literal(const SimpleIntegerVariableID & id, Integer v, int target_level, bool immediate_neighbours) -> void;

        // Hoist a real variable's ge threshold v to Top (level 0) *if* it is currently
        // a live, deletable (level > 0) order literal; otherwise a no-op. Used when an
        // eq atom's permanent (Top) definition names ge(v)/ge(v+1): those ge defs must
        // stay resident for the eq def -- and any solx / backtrack clause over the eq
        // atom -- to keep naming a live literal after a backtrack forget. Skips a
        // literal that is not live for id (never referenced here, e.g. the ge not named
        // by the compact-encoding form) or already permanent at Top.
        auto hoist_order_literal_to_top_if_live(
            const SimpleIntegerVariableID & id, Integer v, std::optional<OrderEncodingResidencyCause> stats_cause = std::nullopt) -> void;

        // Keep the two ge thresholds a permanent (Top) reifying atom names resident at
        // Top. An eq atom eq(v) <=> ge(v) & ~ge(v+1) names (v, v+1); an interval atom
        // in[lo,hi] <=> ge(lo) & ~ge(hi+1) names (lo, hi+1). Under Literals mode those
        // atom definitions are emitted at Top and outlive any backtrack, so the ge defs
        // they name must not be deleted underneath them (which would leave the Top atom
        // -- and any solx / covering / backtrack clause over it -- naming a deleted
        // literal, or force a pinned re-introduction that VeriPB rejects). A no-op
        // unless the mode is Literals, the logger is attached, assertions are off, and
        // id is a real SimpleIntegerVariableID; harmlessly skips a threshold that is a
        // boundary/model-time literal (already Top) or not live.
        auto hoist_ges_named_by_top_atom(SimpleOrProofOnlyIntegerVariableID id, Integer lower_ge, Integer upper_ge,
            std::optional<OrderEncodingResidencyCause> cause = std::nullopt) -> void;

        // --- GCS_ORDER_ENCODING_STATS pin-apportionment diagnostic (Literals mode only) ---
        // Every one of these is a pure-bookkeeping no-op unless _imp->collect_order_encoding_stats
        // is set (Literals mode AND the env var present); none of them emit proof bytes, so
        // the .opb/.pbp are byte-identical whether or not the diagnostic runs.

        // Register a real-variable ge threshold v as seen (proof-time), and, if it is born
        // resident at Top, attribute that residency to born_cause (first-cause-wins).
        auto stats_note_ge_recorded(const SimpleIntegerVariableID & id, Integer v, std::optional<OrderEncodingResidencyCause> born_cause) -> void;

        // Note that a chain-link/stitch clause over the threshold pair (lo, hi) was just
        // emitted for id, landing at proof level at_level. forget_path counts it as a
        // forget-driven stitch; a link landing at Top (at_level == 0) whose pair was
        // already Top-linked is counted as a duplicate-Top-stitch (a known inefficiency).
        auto stats_note_stitch_emitted(const SimpleIntegerVariableID & id, Integer lo, Integer hi, int at_level, bool forget_path) -> void;

    public:
        /**
         * \name Constructors, destructors, and the like.
         */
        ///@{

        explicit NamesAndIDsTracker(const ProofOptions &);
        ~NamesAndIDsTracker();

        /**
         * Must be called after all proof writing is complete to flush and
         * close any supplementary output files (e.g. the variables map).
         * Must not be called from a destructor.
         */
        auto finalise() -> void;

        auto operator=(const NamesAndIDsTracker &) -> NamesAndIDsTracker & = delete;
        NamesAndIDsTracker(const NamesAndIDsTracker &) = delete;

        NamesAndIDsTracker(NamesAndIDsTracker &&) noexcept;
        auto operator=(NamesAndIDsTracker &&) noexcept -> NamesAndIDsTracker &;

        ///@}

        /**
         * Must be called after initialisation, before anything is done using the ProofModel,
         * to direct output to the model.
         */
        auto start_writing_model(ProofModel * const) -> void;

        /**
         * Must be called after the model is finalised and before the proof logging starts,
         * to direct output to the proof.
         */
        auto switch_from_model_to_proof(ProofLogger * const) -> void;

        /**
         * Must be called after the proof header has been written, to write out any delayed
         * proof steps that were generated during model creation.
         */
        auto emit_delayed_proof_steps() -> void;

        /**
         * Say that we will need the greater-than-or-equal literal for a given variable.
         */
        auto need_gevar(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> void;

        /**
         * Drop from the live order-link structure every order-encoding chain link
         * tagged with the given proof level. Emits nothing: the matching `del` lines
         * are produced by ProofLogger::forget_proof_level's own deletion loop (the
         * links were recorded at Current == that level). This just keeps the live
         * structure in sync so a later need_gevar re-emits any that are needed again.
         * A cheap no-op when the order-link deletion mode is off. Intended to be
         * called from ProofLogger::forget_proof_level.
         *
         * Note: in `Literals` mode this dispatches to forget_order_literals_at_level
         * (which deletes literals and re-stitches the chain around each deleted run),
         * not links. The `_links_` in this name predates the Literals mode; it is left
         * unchanged until the planned Brancher refactor renames it.
         */
        auto forget_order_links_at_level(int level) -> void;

        /**
         * Hoist a search-introduced ge threshold `v` of real variable `id`
         * (Literals order-encoding-deletion mode) from its current, deep proof
         * level to the shallower `target_level`, so a later `forget` deletes it
         * later -- or, for `target_level == 0` (Top), never. Two parts, both
         * required:
         *
         *  1. **Move the definition** -- a pure bookkeeping relocation, emitting
         *     NOTHING. The literal's two reification proof lines are moved from
         *     their current level bucket to `target_level`'s (via
         *     ProofLogger::move_proof_lines_to_level), and the tracker's live/level
         *     index for `v` is retagged. Re-emitting the `red` is exactly what
         *     fails VeriPB (the falsify-witness collides with a pin), which is why
         *     hoisting relocates rather than recreates.
         *
         *  2. **Re-stitch** -- emit fresh chain links joining `v` to its neighbours,
         *     so it stays unit-propagating (the Ch.3 invariant); see
         *     stitch_hoisted_order_literal for the neighbour policy selected by
         *     \p immediate_neighbours. Chain links are pol-derived from the
         *     residents' defs, so re-emitting them is sound.
         *
         * Requires the mode to be Literals, the logger attached, and `v` to be
         * currently live for `id`. A no-op if `v` is already at `target_level`.
         *
         * \p immediate_neighbours (default false): pass false when the caller is about
         * to forget every level deeper than \p target_level (backtrack / nogood hoist),
         * true when it is not (the eq/interval-def hoist to Top, whose deeper interior
         * survivors must stay chained). See stitch_hoisted_order_literal.
         */
        auto hoist_order_literal_to_level(const SimpleIntegerVariableID & id, Integer v, int target_level, bool immediate_neighbours = false,
            std::optional<OrderEncodingResidencyCause> stats_cause = std::nullopt) -> void;

        /**
         * Hoist a search-introduced ge threshold to Top (proof level 0), where its
         * definition stays resident permanently and is never forgotten. Equivalent
         * to hoist_order_literal_to_level(id, v, 0). This is the form restart
         * nogoods and parallel-search shared nogoods want.
         */
        auto hoist_order_literal_to_top(
            const SimpleIntegerVariableID & id, Integer v, std::optional<OrderEncodingResidencyCause> cause = std::nullopt) -> void;

        /**
         * Hoist every literal in \p lits that is a live, deletable real-variable
         * order literal (a `ge`/`<` condition over a SimpleIntegerVariableID) up to
         * \p target_level, using hoist_order_literal_to_level. Literals that are not
         * such an order literal, are not currently live, or already sit at
         * \p target_level or shallower are skipped -- hoisting only ever moves a
         * definition to a shallower level, never deeper. A no-op unless the mode is
         * Literals and the logger is attached.
         *
         * This is the backtrack/nogood entry point: on a normal backtrack the guess
         * stack is hoisted to the backtrack level (so the backtrack clause never
         * names a literal the following forget deletes), and a learned nogood hoists
         * its decision literals to Top (so they survive the restart forget). Both
         * replace the old delete-then-reintroduce path for the pinned case.
         */
        auto hoist_live_order_literals_toward_level(
            const std::vector<Literal> & lits, int target_level, std::optional<OrderEncodingResidencyCause> cause = std::nullopt) -> void;

        /**
         * The mirror of hoist: take real variable \p id's live ge threshold \p v out of
         * the proof. Hoist moves a definition *to* a level and stitches it *in*; eviction
         * deletes it and stitches the chain *over* it.
         *
         * Emits `del` for the threshold's two reification lines and for every chain
         * clause naming it, then stitches its surviving immediate neighbours with a skip
         * link `ge(hi) -> ge(lo)` (the run-stitch of the forget sweep, run for one
         * literal on demand, landing at the deeper neighbour's level exactly as there).
         * Drops \p v from the live/level bookkeeping and **retires its atom**, so
         * `find_condition` stops answering and the only route back to the literal is
         * `need_gevar`, which re-introduces the definition as a deletable interior one and
         * takes the retired `XLiteral` back -- the same structural enforcement of the
         * naming rule the backtrack sweep relies on.
         *
         * \p expected_sole_top_cause is the residency precondition, checked against the
         * always-on Top-pin bookkeeping rather than asserted blindly, because VeriPB
         * polices a wrongly-evicted literal only at a later point of use:
         *
         *  - For a Top-resident (level 0) \p v the caller must name the cause it believes
         *    pins it, and eviction happens only if that cause is the *only* pin and it is
         *    held exactly once. A ge that two permanent atoms name, or one that is
         *    structurally resident (boundary / model-time / aux / view / gate, which take
         *    no pin), is refused.
         *  - For a deletable (level > 0) \p v -- the eq-atom window's mid-level tidy --
         *    pass `std::nullopt`: no Top line can name it, and eviction just deletes it
         *    early instead of waiting for the backtrack that would.
         *
         * Returns whether \p v was evicted. A refusal emits nothing and changes nothing:
         * the literal stays resident, which is always correct and merely wins less.
         * Requires the mode to be Literals, the logger attached, and \p v to be currently
         * live for \p id (all three throw, being caller errors rather than policy).
         */
        auto evict_order_literal(const SimpleIntegerVariableID & id, Integer v, std::optional<OrderEncodingResidencyCause> expected_sole_top_cause)
            -> bool;

        /**
         * How many order-encoding chain clauses currently present in the proof name real
         * variable \p id's ge threshold \p v. Always 0 unless the mode is Literals.
         *
         * This exists because it is `evict_order_literal`'s postcondition -- it must leave
         * none -- and because **VeriPB cannot check that postcondition**. A chain clause
         * left naming an evicted threshold is still a valid derived constraint: it was
         * derived from definitions that the atom's stable identity lets a later
         * `need_gevar` restore, and re-introducing that definition verifies with the stale
         * clause present (measured against veripb 3.0.2, not assumed). So a missed
         * deletion is silent, and costs exactly the resident-database shrinkage the mode
         * exists for. This is a third instance of the pattern the design records for
         * eviction ordering and ge-under-eq residency: VeriPB polices the order encoding
         * only at a point of use, so the discipline has to be checked solver-side.
         */
        [[nodiscard]] auto chain_clauses_naming(const SimpleIntegerVariableID & id, Integer v) const -> long long;

        /**
         * Make a windowed (ProofLevel::Current) eq atom definition permanent: relocate its
         * two reification lines to Top, exactly as hoist_order_literal_to_level relocates
         * a ge definition (pure bookkeeping, emitting nothing -- re-emitting the `red` is
         * what collides with a pin), and hoist the two ge thresholds it names to Top with
         * it, so the now-permanent eq definition cannot be left naming a deleted literal.
         *
         * This is the eq-atom window's hoist-out rule (dev_docs/brancher-design.md): an
         * `eq(v)` that acquires a permanent reference -- a solx blocking clause, a learned
         * nogood's decision literal, a reified constraint naming `id == v` -- must be
         * retained instead of evicted when the window steps past it. Eq atoms carry no
         * chain, so there is nothing to re-stitch; the ges it names are re-stitched by
         * their own hoists.
         *
         * A no-op for an atom that is not a live windowed definition (every eq atom
         * outside a window is already permanent). Requires the mode to be Literals and the
         * logger attached.
         */
        auto hoist_eq_to_top(const SimpleIntegerVariableID & id, Integer v) -> void;

        /**
         * The hoist-out rule's **trigger**: note that a permanent (Top) line is about to
         * name real variable \p id's eq atom \p v -- a solx blocking clause, a soli
         * witness, a learned nogood's decision literal -- and so retain the atom instead
         * of letting the window evict it, by hoisting it (and the two ge thresholds it
         * names) out to Top. hoist_eq_to_top is the action; this is where the reference is
         * detected, at the reference site, exactly as note_order_literal_top_pin is for
         * the ge side.
         *
         * A cheap no-op whenever there is nothing to retain: any mode but Literals, no
         * logger, or -- the overwhelmingly common case -- an atom that is not a live
         * windowed definition, every eq atom outside a window being permanent already.
         */
        auto note_permanent_eq_reference(const SimpleIntegerVariableID & id, Integer v) -> void;

        /**
         * The eq mirror of evict_order_literal: take real variable \p id's live windowed
         * eq definition \p v out of the proof. Emits `del` for its two reification lines,
         * drops it from the windowed live/level bookkeeping, and **retires its atom**, so
         * find_condition stops answering and the only route back is
         * need_direct_encoding_for, which re-introduces the definition and takes the
         * retired XLiteral back with its identity intact. Eq atoms carry no chain, so
         * unlike the ge case there is nothing to stitch.
         *
         * This is the window's per-iteration tidy: the frontier has stepped past \p v, the
         * advance that needed \p v's reverse reification has already been emitted, and the
         * sibling clause naming the atom has already been deleted by the caller (which owns
         * that ordering -- deleting the definition first is exactly what driver control D2c
         * shows VeriPB rejecting).
         *
         * Returns whether the definition was evicted. `false` -- an atom that is not a live
         * windowed definition, including one the hoist-out rule has already taken to Top --
         * is a refusal, not an error: it means the atom is permanent, which is always
         * correct and merely wins less. Requires the mode to be Literals and the logger
         * attached (both throw, being caller errors rather than policy).
         */
        auto evict_eq_literal(const SimpleIntegerVariableID & id, Integer v) -> bool;

        /**
         * How many of real variable \p id's eq atoms are currently live *windowed*
         * definitions. Always 0 unless the mode is Literals, and 0 for every variable
         * nothing has windowed. Exposed because the window's headline invariant -- O(1)
         * resident eq definitions per branched variable, not O(domain width) -- is
         * solver-side and unobservable in the proof VeriPB checks.
         */
        [[nodiscard]] auto live_windowed_eq_count(const SimpleIntegerVariableID & id) const -> long long;

        /**
         * How many of real variable \p id's ge thresholds are currently live (resident in
         * the proof), at any level. Always 0 unless the mode is Literals. The ge half of
         * the same unobservable-in-the-proof invariant as live_windowed_eq_count.
         */
        [[nodiscard]] auto live_order_literal_count(const SimpleIntegerVariableID & id) const -> long long;

        /**
         * Is real variable \p id's ge threshold \p v currently resident in the proof, at
         * any level? Always false unless the mode is Literals. This is
         * evict_order_literal's one throwing precondition made askable, for a caller that
         * evicts opportunistically -- the eq window steps over a threshold that a one-sided
         * (compact-encoding) eq definition may never have named.
         */
        [[nodiscard]] auto order_literal_is_live(const SimpleIntegerVariableID & id, Integer v) const -> bool;

        /**
         * Is real variable \p id's eq atom \p v currently a live *windowed* definition —
         * one the window may evict? False for every permanent atom, which is every eq atom
         * a constraint (rather than the branch layer) defined first, and false once the
         * hoist-out rule has retained one. The window asks before doing any work behind a
         * frontier, because on a model whose constraints name the values it branches on
         * there is nothing behind the frontier to take out.
         */
        [[nodiscard]] auto eq_literal_is_windowed(const SimpleIntegerVariableID & id, Integer v) const -> bool;

        /**
         * If the `GCS_ORDER_ENCODING_STATS` diagnostic is active (OrderEncodingDeletion::Literals
         * mode AND the env var set), sweep the pin-apportionment bookkeeping and print a
         * compact summary to stderr, each line prefixed `%% oed-stats:`. Called once, from
         * ProofLogger::end_proof (the single conclude funnel). A no-op otherwise; emits no
         * proof bytes ever.
         */
        auto dump_order_encoding_stats() const -> void;

        /**
         * Ensure a proof-only binary-encoded variable exists for a given view.
         *
         * Returns the `ProofOnlySimpleIntegerVariableID` representing
         * `BinEnc(view)`. On first reference to a view during model writing,
         * this allocates a fresh proof-only integer variable sized to the
         * view's visible domain, emits its bound axioms, and emits the
         * linking constraint `BinEnc(view) = s*BinEnc(view.actual_variable) + c`
         * tying it back to the underlying. Repeated calls with the same view
         * return the same id (canonicalised on the `(actual_variable,
         * negate_first, then_add)` triple).
         *
         * Throws `UnimplementedException` if called during the proof-logging
         * phase for a view that wasn't registered during model writing; this
         * case is left unimplemented until empirical failures show it needed.
         */
        [[nodiscard]] auto need_view(const ViewOfIntegerVariableID & view) -> ProofOnlySimpleIntegerVariableID;

        /**
         * Look up an already-registered view's proof-only variable, or return
         * `std::nullopt` if no entry exists. Never triggers introduction;
         * never throws. Used by `emit_inequality_to` to decide whether to
         * emit in V's bits (registered) or fall back to deviewing through
         * the underlying (not registered — only happens for views first seen
         * during proof logging, which `need_view` doesn't yet support).
         */
        [[nodiscard]] auto find_view(const ViewOfIntegerVariableID & view) const -> std::optional<ProofOnlySimpleIntegerVariableID>;

        /**
         * The [lo, hi] a view's visible values span, from the underlying
         * variable's registered definition bounds. What need_view sizes a
         * view's proof-only bit vector by; exposed so the objective path can
         * first ask whether that bit vector is representable at all
         * (bits_encoding_fits) before registering the view.
         */
        [[nodiscard]] auto view_bounds(const ViewOfIntegerVariableID & view) const -> std::pair<Integer, Integer>;

        /**
         * Record that `deviewed_line` is the deview-form of `v_form_line`.
         * Lookup is via `deviewed_line_for`.
         */
        auto register_deviewed_line(const ProofLine & v_form_line, const ProofLine & deviewed_line) -> void;

        /**
         * Return the deview-form line for `line` if one has been registered,
         * otherwise `line` itself. Non-view-using constraints always return
         * the input unchanged. Used by `PolBuilder` in deview mode.
         */
        [[nodiscard]] auto deviewed_line_for(const ProofLine & line) const -> ProofLine;

        /**
         * The (LE-half, GE-half) proof-line IDs of the bit-vector link for a
         * registered view (allocated in `need_view`). Used by the
         * deview-derivation helper.
         */
        [[nodiscard]] auto view_link_lines_for(const ProofOnlySimpleIntegerVariableID & view_proof_id) const -> std::pair<ProofLine, ProofLine>;

        /**
         * Derive and register a deview-form for the constraint at
         * `v_form_line`. Walks the WPBSum's lhs for view terms; if any are
         * found, queues a `pol` line that substitutes each `BinEnc(V)` term
         * for `s*BinEnc(X) + c` (using the appropriate link half), emits at
         * the top of the proof, and records the line in the deviewed-form
         * registry so `deviewed_line_for(v_form_line)` returns it. No-op
         * if the constraint has no view terms.
         *
         * `le_half` indicates whether the OPB-form coefficients are
         * sign-flipped from the WPBSum's `lhs` (true for the LE half of an
         * equality, or any `<=` constraint that emit_inequality_to flips to
         * a `>=`). This is needed to pick the right link half for the
         * cancellation.
         */
        auto derive_deviewed_form_for(const ProofLine & v_form_line, const SumOf<Weighted<PseudoBooleanTerm>> & lhs, bool le_half) -> void;

        /**
         * Say that we will need the diect encoding to exist for a given variable.
         *
         * The eq atom's definition is permanent (at ProofLevel::Top) unless a
         * WindowedEqScope is open, which is the branch layer's request for a deletable
         * one; see that type for when the request is honoured.
         */
        auto need_direct_encoding_for(SimpleOrProofOnlyIntegerVariableID, Integer) -> void;

        /**
         * Say that we will need the range ("in") literal [lo, hi] for a variable,
         * meaning `lo <= var <= hi`, and return it. Idempotent on (id, lo, hi). A
         * width-1 interval IS the eq atom: `need_invar(id, v, v)` returns the
         * direct-encoding literal `id == v`, never a separate literal.
         *
         * A range literal is reified against the variable's own two order-encoding
         * cuts, `lit <=> (var >= lo) AND NOT (var >= hi+1)`. The reification alone
         * does not keep unit propagation strong enough for later proof steps (see
         * dev_docs/range_literals_spec.md): this call also maintains the
         * always-covered partition — the request's endpoints split existing cells,
         * the requested literal gets a covering over the cells it spans, containment
         * edges link it to its immediate neighbours, and the variable's first request
         * sets up the partition. All linking is state-independent, at
         * ProofLevel::Top.
         *
         * Requires a bits-encoded variable, and currently the proof-logging phase
         * (throws UnimplementedException during model writing).
         */
        [[nodiscard]] auto need_invar(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> ProofLiteral;

        /**
         * Does this variable have a bits encoding? Zero-one variables default to the
         * direct-only encoding, which cannot support order cuts or range literals;
         * callers wanting range literals must fall back to per-value reasoning when
         * this is false.
         */
        [[nodiscard]] auto has_bit_representation(const SimpleOrProofOnlyIntegerVariableID &) const -> bool;

        /**
         * Say that we are going to need an at-least-one constraint for a
         * variable.
         */
        [[nodiscard]] auto need_constraint_saying_variable_takes_at_least_one_value(IntegerVariableID) -> ProofLine;

        /**
         * Give the proof line specifying the definition of this literal in terms of its bit
         * representation. Will emit the reification, if it does not already exist. If this
         * is a zero-one variable, returns an actual literal.
         */
        [[nodiscard]] auto need_pol_item_defining_literal(const IntegerVariableCondition &) -> std::variant<ProofLine, XLiteral>;

        /**
         * Set things up internally as if the specified variable was a real
         * variable, so that proof_name() etc will work with it.
         */
        auto create_literals_for_introduced_variable_value(SimpleIntegerVariableID, Integer, const std::string &) -> void;

        /**
         * Ensure that a name exists for a given variable condition.
         */
        auto need_proof_name(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) -> void;

        /**
         * Ensure that need_proof_name() has been called for everything in a given sum.
         */
        auto need_all_proof_names_in(const SumOf<Weighted<PseudoBooleanTerm>> & sum) -> void;

        /**
         * Ensure that need_proof_name() has been called for everything in a given Literals.
         */
        auto need_all_proof_names_in(const Literals &) -> void;

        /**
         * Ensure that need_proof_name() has been called for everything in a given HalfReifyOnConjunctionOf.
         */
        auto need_all_proof_names_in(const HalfReifyOnConjunctionOf &) -> void;

        /**
         * Return the string used in PB files for a given XLiteral.
         */
        [[nodiscard]] auto pb_file_string_for(const XLiteral &) const -> const std::string &;

        /**
         * Return the raw proof literal representing a variable condition, for writing to a model or log.
         */
        [[nodiscard]] auto xliteral_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) const -> const XLiteral;

        /**
         * Like xliteral_for, but returns nullopt instead of throwing when the
         * condition has no registered XLiteral. A condition is registered iff it
         * (or its negation) has been introduced --- so "not found" means the
         * literal is fresh/unaliased, which callers can use to reason about
         * whether two atoms could be the same underlying bit.
         */
        [[nodiscard]] auto find_xliteral_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) const -> std::optional<XLiteral>;

        /**
         * Return a string form of a raw proof literal, for writing to a model or log.
         */
        [[nodiscard]] auto pb_file_string_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) const -> const std::string &;

        /**
         * As pb_file_string_for, but introduce the condition's proof name
         * first if it does not exist yet (need_proof_name), in one lookup for
         * the common already-known case. Only for use while assembling a
         * proof line in a buffer: an introduction emits definition lines.
         */
        [[nodiscard]] auto pb_file_string_for_ensuring(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) -> const std::string &;

        /**
         * As xliteral_for, but introduce the condition's proof name first if
         * it does not exist yet, like pb_file_string_for_ensuring. Both
         * polarities are always introduced together, so negating the result
         * is the negated condition's literal; the reified-line renderer uses
         * this to avoid negating whole condition objects.
         */
        [[nodiscard]] auto xliteral_for_ensuring(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) -> XLiteral;

        /**
         * Return a string form of the exact literals specifying a bit assignment for var == val, an alternative way to witness solutions.
         */
        [[nodiscard]] auto bit_assignment_string_for(const SimpleOrProofOnlyIntegerVariableID & var, const Integer & value) const -> std::string;

        /**
         * Return the raw proof literal representing a proof flag, for writing to a model or log.
         */
        [[nodiscard]] auto xliteral_for(const ProofFlag &) const -> const XLiteral;

        /**
         * Like xliteral_for, but returns nullopt instead of throwing when the flag
         * has no registered XLiteral.
         */
        [[nodiscard]] auto find_xliteral_for(const ProofFlag &) const -> std::optional<XLiteral>;

        /**
         * Return a string form of a proof flag, for writing to a model or log. Same as calling
         * raw_literal_as_string(raw_proof_literal(flag)).
         */
        [[nodiscard]] auto pb_file_string_for(const ProofFlag &) const -> const std::string &;

        /**
         * Call the supplied function for each bit making up the given variable, specifying
         * its raw PB literal and coefficient.
         */
        auto each_bit(const SimpleOrProofOnlyIntegerVariableID &) -> std::generator<std::pair<Integer, XLiteral>>;

        /**
         * Get the name and coefficient for the bit position in the representation of the given var.
         */
        [[nodiscard]] auto get_bit(const SimpleOrProofOnlyIntegerVariableID & var, Integer position) -> std::pair<Integer, XLiteral>;

        /**
         * Get the name and coefficient for the bit position in the representation of the given var.
         */
        [[nodiscard]] auto get_bit(const ProofBitVariable & bit) -> std::pair<Integer, XLiteral>;

        /**
         * How many bits are used to represent this variable, including the negative bit if there is one?
         */
        [[nodiscard]] auto num_bits(const SimpleOrProofOnlyIntegerVariableID & var) -> Integer;

        /**
         * If there is a negative bit for this variable, return its coefficient, otherwise
         * return zero.
         */
        [[nodiscard]] auto negative_bit_coefficient(const SimpleOrProofOnlyIntegerVariableID &) -> Integer;

        /**
         * Track that the associated literal exists, and has a string name.
         */
        auto associate_condition_with_xliteral(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &, const XLiteral &) -> void;

        /**
         * Track that a given variable's bits exist.
         */
        auto track_bits(const SimpleOrProofOnlyIntegerVariableID & id, Integer negative_coeff,
            const std::vector<std::pair<Integer, XLiteral>> & bit_vars) -> void;

        /**
         * Track that a given equality variable exists, and has a string name
         * and associated defining constraints.
         */
        auto track_eqvar(SimpleIntegerVariableID, Integer, const std::pair<std::variant<ProofLine, XLiteral>, std::variant<ProofLine, XLiteral>> &)
            -> void;

        /**
         * Track that an at-least-one constraint exists for a given variable.
         */
        auto track_variable_takes_at_least_one_value(const SimpleOrProofOnlyIntegerVariableID &, ProofLine) -> void;

        /**
         * Track that a given proof flag exists with this name.
         */
        auto track_flag(const ProofFlag &, const std::string &) -> void;

        /**
         * Track the lower and upper bounds for a given variable.
         */
        auto track_bounds(const SimpleOrProofOnlyIntegerVariableID & id, Integer, Integer) -> void;

        /**
         * The bounds recorded by track_bounds. For a model variable these are its
         * initial-domain bounds, letting a constraint's s_expr recover
         * domain-derived data (e.g. Regular's regex alphabet) at scp-writing
         * time, when no State is in reach.
         */
        [[nodiscard]] auto tracked_bounds(const SimpleOrProofOnlyIntegerVariableID & id) const -> std::pair<Integer, Integer>;

        /**
         * Track the OPB bound-row references (lower row, upper row) for a
         * bits-encoded variable, so that proof steps can combine them by pol
         * (ProofLogger::introduce_bits_of derives a linear form's own bound
         * lines this way). A state variable's rows are referenced by their
         * `i[name][lb]` / `i[name][ub]` labels (count-robust under
         * cake_pb_cp's re-derived OPB); a proof-only variable's unlabelled
         * rows by constraint number (it never appears in a cake chain).
         */
        auto track_bound_rows(const SimpleOrProofOnlyIntegerVariableID & id, ProofLine lower_row, ProofLine upper_row) -> void;

        /**
         * The bound-row references recorded by track_bound_rows, or nullopt
         * for a variable with no OPB bound rows (one made by
         * ProofModel::create_proof_only_integer_variable_in_proof, whose
         * meaning lives entirely inside the proof).
         */
        [[nodiscard]] auto bound_rows(const SimpleOrProofOnlyIntegerVariableID & id) const -> std::optional<std::pair<ProofLine, ProofLine>>;

        /**
         * Note that this variable's [lo, hi] bounds are not a trivial consequence of
         * the OPB (cake emits no bound line for it, and its bounds are only entailed
         * through conditional channels), so need_gevar must not pin its boundary order
         * literals as top-of-proof RUP lines. The owning constraint is responsible for
         * establishing the bounds explicitly. Used for ArgSort's cake-named free-bit-sum
         * sorted-value variables.
         */
        auto note_bounds_not_trivially_derivable(const SimpleOrProofOnlyIntegerVariableID & id) -> void;

        /**
         * Note that this variable's order encoding must stay RESIDENT under
         * OrderEncodingDeletion::Literals: every ge definition is emitted at Top (tagged
         * level 0) and never deleted on backtrack, exactly as in the deletion-off mode.
         * Called for the in-proof-bit auxiliary magnitude variables that
         * ProofModel::register_state_variable_bits_in_proof creates (divide / modulus),
         * whose ge order literals are named at ProofLevel::Top by the product-justification
         * caches: a deleted definition would strand those permanent Top lines on a deleted
         * literal, which VeriPB rejects. A pure model-build-time note; a no-op effect
         * unless the Literals mode is later active.
         */
        auto note_order_encoding_stays_resident(const SimpleOrProofOnlyIntegerVariableID & id) -> void;

        /**
         * Note that this variable is **exempt from order-encoding deletion**: under
         * OrderEncodingDeletion::Literals every one of its `ge` definitions stays resident
         * at Top, as in mode None, however long its chain grows.
         *
         * This is the frontier owner's call, and it is a *policy* note rather than a
         * correctness one — unlike note_order_encoding_stays_resident, nothing breaks if it
         * is omitted; the variable simply churns. It exists because the chain-length gate
         * cannot distinguish the two kinds of long chain: a **win-regime** one (a
         * weak-propagation split variable, whose stepped-over thresholds are exactly what
         * deletion should remove) from a **churn-regime** one (a perpetually re-tightened
         * bound, deleted and re-introduced forever for no shrinkage at all). Only whoever
         * owns the frontier knows which it is looking at.
         *
         * The measured instance is the **objective**: on seat-moving 2018 its objective and
         * cost variables carry essentially all of the residual 20 784 delete/reintroduce
         * churn at the default gate, verify-neutrally and for zero saving, because
         * branch-and-bound re-tightens the objective at every improving solution and every
         * backtrack relaxes it again. ProofModel::minimise exempts it.
         *
         * A pure note; a no-op unless the Literals mode is later active. Its residency slot
         * (`FrontierExempt`) sits just above the chain gate and just below the structural
         * pins, and is the exact opposite of the eq window's `WindowedFrontier` -- "resident
         * *despite* being frontier" against "deletable *because* frontier". The two never
         * apply to the same variable; see dev_docs/brancher-design.md.
         */
        auto note_deletion_exempt(const SimpleOrProofOnlyIntegerVariableID & id) -> void;

        /**
         * Note that this variable's order-encoding (ge) atom definitions carry @i[..][ge]
         * labels that a cake_pb_cp OPB does not create (it reifies each atom per value
         * under its own @c[peq..] labels). need_gevar then recovers those labels
         * in-proof: when it creates such a gevar it queues an `ia` (implies-add) line
         * re-declaring each half's reification under our @i label at proof start, checked
         * implied against whatever reifies the atom in the OPB (our own @i line in
         * workflow 1, cake's @c[peq..] in workflow 2). The order-chain `pol`s then resolve
         * against the recovered labels either way. Used for ArgSort's permutation
         * variables, whose eq atoms are OPB constraint terms/guards (matching cake) and so
         * are forced model-time under @i labels.
         */
        auto note_recover_atom_labels_in_proof(const SimpleOrProofOnlyIntegerVariableID & id) -> void;

        /**
         * \brief Claim each of these `c[id][role]` labels for rows about to be
         * emitted, throwing ProofError if any is already taken or if the pack
         * repeats one.
         *
         * Called only by ProofModel::add_labelled_constraint's ConstraintID
         * overloads, which is what confines the set to the `c[id][role]`
         * namespace; the variable-encoding namespaces are deliberately out of
         * scope, because those rows may be deleted and re-emitted. It lives here
         * rather than in ProofModel because \ref constraint_row_label reads it,
         * and its reader is a presolver, which holds a ProofLogger and no
         * ProofModel --- and both are constructed with this same tracker.
         */
        auto claim_constraint_row_labels(const std::vector<std::string> & labels) -> void;

        /**
         * \brief The label of the row this constraint emitted under this role,
         * or nullopt if it emitted none.
         *
         * Answers "can I cite this?", not "what does it say". A label is a pure
         * function of `(id, role)`, so this needs no per-solve state beyond the
         * claimed set, and every clone of a constraint in every thread computes
         * the same answer.
         *
         * A `yes` always names exactly one row:
         * \ref claim_constraint_row_labels rejects two rows under one label at
         * emission time (#613), so the ambiguity a "look it up" answer would
         * otherwise have to worry about cannot exist by the time this is asked.
         *
         * Pair it with innards::ConstraintProofModelData, which is how a
         * constraint publishes *which* role names the row a citer wants;
         * constructing a role string here instead would be guessing at another
         * constraint's naming scheme.
         */
        [[nodiscard]] auto constraint_row_label(const ConstraintID & id, const std::string & role) const -> std::optional<ProofLineLabel>;

        /**
         * Create a proof flag with a new identifier, named `f[index][stem]`.
         */
        [[nodiscard]] auto create_proof_flag(const std::string & stem) -> ProofFlag;

        /**
         * Create a position-indexed flag named `x[id][i1_i2..][annotation?]`,
         * conforming to cake_pb_cp's naming for verified encodings (workflow 2)
         * rather than the solver's default `f[index][stem]`.
         *
         * This mirrors cake's `Indices (num list) (annotation option)` flag
         * constructor (cp_to_ilpScript.sml `format_flag`): the indices are the
         * array positions the auxiliary ranges over, joined by `_`, and the
         * optional annotation is appended in its own brackets. So an
         * all_different pair selector is `create_proof_flag(id, {i, j})` ->
         * `x[id][i_j]`, and a count per-position flag is
         * `create_proof_flag(id, {i}, "eq")` -> `x[id][i][eq]`.
         *
         * cake's prefix encodes what the auxiliary is indexed by, not whether it
         * is reified: `x` = array positions (this method), `b` = a scalar flag
         * with only an annotation (`Flag`), `v` = values (`Values`). The `b` / `v`
         * families get their own entry points when their first consumers land.
         * Because VeriPB binds variables by name, a flag the solver's proof shares
         * with cake's re-derived OPB must be defined under cake's name. See #354.
         */
        [[nodiscard]] auto create_proof_flag(const ConstraintID & id, const std::vector<long long> & indices,
            const std::optional<std::string> & annotation = std::nullopt) -> ProofFlag;

        /**
         * Create a scalar flag named `b[id][annotation]`, conforming to
         * cake_pb_cp's naming for verified encodings (workflow 2). This mirrors
         * cake's `Flag annotation` constructor (cp_to_ilpScript.sml `format_flag`):
         * a per-constraint auxiliary carrying only an annotation, with no index
         * list -- in contrast to the position-indexed `x[id][...]` overload above.
         * not_equals' single selector is `create_proof_flag(id, "ne")` ->
         * `b[id][ne]`. See #354 for the `x` / `b` / `v` family split.
         */
        [[nodiscard]] auto create_proof_flag(const ConstraintID & id, const std::string & annotation) -> ProofFlag;

        /**
         * Create a value-indexed flag named `v[id][v1_v2..][annotation?]`,
         * conforming to cake_pb_cp's `Values` flag constructor
         * (cp_to_ilpScript.sml `format_flag`). The list holds domain values
         * (joined by '_'), in contrast to the array positions of the `x[...]`
         * overload above. nvalue's per-value occurrence flag is
         * `create_proof_flag_values(id, {v})` -> `v[id][v]`. A distinct name (not
         * an overload of create_proof_flag) because the value-list signature
         * would otherwise be indistinguishable from the `x[...]` one. Negative
         * values render as `-N`, matching cake (and the solver's eq/ge literals,
         * e.g. `i[X][eq-N]`); '-' is legal in both VeriPB variable names and
         * @labels (VeriPB-dev #191). See #354.
         */
        [[nodiscard]] auto create_proof_flag_values(const ConstraintID & id, const std::vector<long long> & values,
            const std::optional<std::string> & annotation = std::nullopt) -> ProofFlag;

        /**
         * Create a flag named `n[k][atom]`, conforming to cake_pb_cp's rendering
         * of a reified atom over a CONSTANT operand (cp_encScript.sml format_var
         * for `Ge`/`Eq` over a constant): e.g. `n[3][ge0]`, `n[-2][eq0]`. cake
         * reifies every operand's atoms uniformly, so a constant slot's atoms
         * exist by name, pinned to their truth values; the pin rows are the
         * ProofModel's job (cake_constant_atoms). See issue #483.
         */
        [[nodiscard]] auto create_proof_flag_for_constant(Integer k, const std::string & atom) -> ProofFlag;

        /**
         * The numbers that determine a half-reification of a PB constraint:
         * the (negative) coefficient each negated reifying term is given, and
         * the constraint's effective right-hand side (adjusted if the
         * conjunction contains a statically-false literal). The reified
         * constraint is `lhs + reif_coefficient * (each ~term) <=
         * effective_rhs`; reify() materialises exactly that, and
         * emit_reified_inequality_to renders it directly.
         */
        struct ReificationShape
        {
            Integer reif_coefficient;
            Integer effective_rhs;
        };

        [[nodiscard]] auto reification_shape(const WPBSumLE &, const HalfReifyOnConjunctionOf &) -> ReificationShape;

        /**
         * Reify a PB constraint on a conjunction of ProofFlags or ProofLiterals
         */
        [[nodiscard]] auto reify(const WPBSumLE &, const HalfReifyOnConjunctionOf &) -> WPBSumLE;

        /*
         * Allocate an XLiteral with the given semantic meaning.
         */
        [[nodiscard]] auto allocate_xliteral_meaning(SimpleOrProofOnlyIntegerVariableID id, const EqualsOrGreaterEqual & op, Integer value)
            -> XLiteral;

        /**
         * Allocate an XLiteral meaning `lo <= id <= hi`.
         */
        [[nodiscard]] auto allocate_xliteral_meaning(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> XLiteral;

        /**
         * Allocate an XLiteral with the given semantic meaning.
         */
        [[nodiscard]] auto allocate_xliteral_meaning(ProofFlag flag) -> XLiteral;

        /**
         * Allocate an XLiteral with the given semantic meaning.
         */
        [[nodiscard]] auto allocate_xliteral_meaning_negative_bit_of(
            SimpleOrProofOnlyIntegerVariableID flag, Integer power, const std::optional<std::string> & name_override = std::nullopt) -> XLiteral;

        /**
         * Allocate an XLiteral with the given semantic meaning.
         */
        [[nodiscard]] auto allocate_xliteral_meaning_bit_of(
            SimpleOrProofOnlyIntegerVariableID flag, Integer power, const std::optional<std::string> & name_override = std::nullopt) -> XLiteral;

        /**
         * Track a human-readable name for a variable.
         */
        auto track_variable_name(SimpleOrProofOnlyIntegerVariableID id, const std::string &) -> void;

        /**
         * Track a human-readable name for a variable.
         */
        auto track_variable_name(ProofFlag id, const std::string &) -> void;

        /**
         * Get the human-readable / s-expr name for a variable. Currently throws on views.
         */
        [[nodiscard]] auto s_expr_name_of(IntegerVariableID id) const -> std::string;

        /**
         * Get the human-readable / s-expr name for a literal. Currently not sure about VariableConditionFrom<IntegerVariableID>
         */
        [[nodiscard]] auto s_expr_name_of(Literal lit) const -> std::string;

        /**
         * Get the human-readable / s-expr name for a reification condition
         */
        [[nodiscard]] auto s_expr_name_of(ReificationCondition cond) const -> std::string;

        /**
         * Get the human-readable / s-expr name for a condition operator
         */
        [[nodiscard]] auto s_expr_name_of(VariableConditionOperator op) const -> std::string;

        /**
         * Render an objective variable as the `.scp` `prob_type` spec:
         * `(minimize <name>)` or `(maximize <name>)`, matching cake_pb_cp's
         * spelling (a view that negates its variable becomes a maximize).
         */
        [[nodiscard]] auto s_expr_render_of(IntegerVariableID id) const -> std::string;

        /**
         * Get the s-expr *term* for a variable: s_expr_name_of() parsed into an
         * SExpr, so a view like `(-_1 + 17)` becomes a list rather than an atom.
         * Prefer this over `parse_s_expr(s_expr_name_of(...))` at call sites so
         * the wrap can't be forgotten.
         */
        [[nodiscard]] auto s_expr_term_of(IntegerVariableID id) const -> SExpr;

        /**
         * Get the s-expr *term* for a literal: s_expr_name_of() parsed into an
         * SExpr (a bare atom like `_1` or `1`, or a list for a view literal).
         * The literal-list constraints (and / or / parity) write their inputs
         * with this. Prefer it over `parse_s_expr(s_expr_name_of(...))`.
         */
        [[nodiscard]] auto s_expr_term_of(Literal lit) const -> SExpr;

        /**
         * Get the s-expr term for a reification condition, or nullopt when the
         * condition is unconditional (MustHold / MustNotHold). Keeps the
         * "no condition" case explicit rather than leaking the empty string that
         * the s_expr_name_of(ReificationCondition) overload returns.
         */
        [[nodiscard]] auto s_expr_term_of(ReificationCondition cond) const -> std::optional<SExpr>;

        /**
         * Get the human-readable name for a variable.
         */
        [[nodiscard]] auto name_of(SimpleOrProofOnlyIntegerVariableID id) const -> const std::string &;

        /**
         * Get the human-readable name for a variable.
         */
        [[nodiscard]] auto name_of(ProofFlag id) const -> const std::string &;
    };
}

#endif
