#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/interval_tree.hh>
#include <gcs/innards/proofs/hints.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_line-fwd.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/proof_only_variables-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <algorithm>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <gcs/proof.hh>
#include <list>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include <nlohmann/json.hpp>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#endif

#include <util/overloaded.hh>

using namespace gcs;
using namespace gcs::innards;

using std::any_of;
using std::fstream;
using std::function;
using std::generator;
using std::ios;
using std::ios_base;
using std::list;
using std::make_shared;
using std::make_unique;
using std::map;
using std::max;
using std::min;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::shared_ptr;
using std::string;
using std::stringstream;
using std::to_string;
using std::unordered_map;
using std::variant;
using std::vector;
using std::visit;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

namespace
{
    // These three tables are read on every literal rendered into every proof
    // line, so they are hashed rather than tree-ordered. Nothing iterates
    // them. The hashes just have to spread structured small integers; the
    // magic constant is the usual 64-bit golden-ratio mix.
    constexpr auto hash_combine(std::size_t seed, std::size_t v) -> std::size_t
    {
        return seed ^ (v + 0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2));
    }

    struct HashSimpleOrProofOnlyVariable
    {
        [[nodiscard]] auto operator()(const SimpleOrProofOnlyIntegerVariableID & id) const -> std::size_t
        {
            return visit(overloaded{//
                             [&](const SimpleIntegerVariableID & v) { return hash_combine(1, v.index); },
                             [&](const ProofOnlySimpleIntegerVariableID & v) { return hash_combine(2, v.index); }},
                id);
        }
    };

    // A variable's atoms, one table per condition family, storing only the
    // positive polarity (the negative-op condition is the flipped literal:
    // every allocation registers the pair together). Read on every condition
    // rendered into every proof line, hence value-keyed tables per variable
    // rather than one big map over whole condition objects.
    // The two halves of an atom's defining reification: forward and reverse
    // lines (or, for a direct-encoded 0/1 variable, the literal itself).
    using AtomDefs = pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>>;

    struct VariableAtoms
    {
        std::unordered_map<long long, XLiteral> eq; // Equal; NotEqual is the flip
        std::unordered_map<long long, XLiteral> ge; // GreaterEqual; Less is the flip
        map<pair<Integer, Integer>, XLiteral> in;   // InRange by (lo, hi); NotInRange is the flip
        // The defining lines for the eq and ge atoms that have them (an atom
        // can exist in eq/ge above without defs, e.g. an introduced
        // variable's values). Value-keyed like the literal tables.
        std::unordered_map<long long, AtomDefs> eq_defs;
        std::unordered_map<long long, AtomDefs> ge_defs;
    };

    struct HashView
    {
        [[nodiscard]] auto operator()(const ViewOfIntegerVariableID & view) const -> std::size_t
        {
            auto h = hash_combine(view.negate_first ? 3 : 4, view.actual_variable.index);
            return hash_combine(h, static_cast<std::size_t>(view.then_add.raw_value));
        }
    };

    struct HashProofFlag
    {
        [[nodiscard]] auto operator()(const ProofFlag & flag) const -> std::size_t
        {
            return hash_combine(flag.positive ? 5 : 6, flag.index);
        }
    };
}

struct NamesAndIDsTracker::Imp
{
    ProofModel * model = nullptr;
    ProofLogger * logger = nullptr;

    // Every c[id][role] label emitted so far. A label is how a proof step cites
    // a row, so two constraint rows must never share one; see
    // claim_constraint_row_labels, and note the variable-encoding namespaces are
    // deliberately not tracked here. Write-only while the model is being
    // defined, read-only afterwards, and derived entirely from (id, role) --- so
    // it needs no synchronisation under the intended one-OPB, N-thread model.
    set<string> emitted_constraint_row_labels;

    unordered_map<SimpleOrProofOnlyIntegerVariableID, ProofLine, HashSimpleOrProofOnlyVariable> variable_at_least_one_constraints;
    // Indexed by variable index (variables are allocated with sequential
    // indices, so these stay dense), one per id kind.
    vector<VariableAtoms> simple_variable_atoms;
    vector<VariableAtoms> proof_only_variable_atoms;

    [[nodiscard]] auto atoms_for(const SimpleOrProofOnlyIntegerVariableID & id) -> VariableAtoms &
    {
        auto & table = visit(overloaded{//
                                 [&](const SimpleIntegerVariableID &) -> vector<VariableAtoms> & { return simple_variable_atoms; },
                                 [&](const ProofOnlySimpleIntegerVariableID &) -> vector<VariableAtoms> & { return proof_only_variable_atoms; }},
            id);
        auto idx = visit([&](const auto & i) { return static_cast<vector<VariableAtoms>::size_type>(i.index); }, id);
        if (table.size() <= idx)
            table.resize(idx + 1);
        return table[idx];
    }

    [[nodiscard]] auto find_atoms(const SimpleOrProofOnlyIntegerVariableID & id) const -> const VariableAtoms *
    {
        const auto & table =
            visit(overloaded{//
                      [&](const SimpleIntegerVariableID &) -> const vector<VariableAtoms> & { return simple_variable_atoms; },
                      [&](const ProofOnlySimpleIntegerVariableID &) -> const vector<VariableAtoms> & { return proof_only_variable_atoms; }},
                id);
        auto idx = visit([&](const auto & i) { return static_cast<vector<VariableAtoms>::size_type>(i.index); }, id);
        return idx < table.size() ? &table[idx] : nullptr;
    }

    // The single lookup behind xliteral_for and friends: resolve a condition
    // to its literal, flipping polarity for the negative ops.
    [[nodiscard]] auto find_condition(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) const -> optional<XLiteral>
    {
        const auto * atoms = find_atoms(cond.var);
        if (! atoms)
            return nullopt;
        auto flip_if = [&](const XLiteral & x, bool negate) { return negate ? ! x : x; };
        switch (cond.op) {
            using enum VariableConditionOperator;
        case Equal:
        case NotEqual:
            if (auto it = atoms->eq.find(cond.value.raw_value); it != atoms->eq.end())
                return flip_if(it->second, NotEqual == cond.op);
            return nullopt;
        case GreaterEqual:
        case Less:
            if (auto it = atoms->ge.find(cond.value.raw_value); it != atoms->ge.end())
                return flip_if(it->second, Less == cond.op);
            return nullopt;
        case InRange:
        case NotInRange:
            if (auto it = atoms->in.find(pair{cond.value, cond.upper_value}); it != atoms->in.end())
                return flip_if(it->second, NotInRange == cond.op);
            return nullopt;
        }
        throw NonExhaustiveSwitch{};
    }

    // Record a condition's literal, normalised to the positive op so both
    // polarities are answerable from one entry. First store wins, matching
    // the emplace semantics this replaces.
    auto store_condition(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond, const XLiteral & x) -> void
    {
        auto & atoms = atoms_for(cond.var);
        switch (cond.op) {
            using enum VariableConditionOperator;
        case Equal: atoms.eq.try_emplace(cond.value.raw_value, x); return;
        case NotEqual: atoms.eq.try_emplace(cond.value.raw_value, ! x); return;
        case GreaterEqual: atoms.ge.try_emplace(cond.value.raw_value, x); return;
        case Less: atoms.ge.try_emplace(cond.value.raw_value, ! x); return;
        case InRange: atoms.in.try_emplace(pair{cond.value, cond.upper_value}, x); return;
        case NotInRange: atoms.in.try_emplace(pair{cond.value, cond.upper_value}, ! x); return;
        }
        throw NonExhaustiveSwitch{};
    }
    unordered_map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, vector<pair<Integer, XLiteral>>>, HashSimpleOrProofOnlyVariable>
        integer_variable_bits_to_size_and_proof_vars;
    unordered_map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, Integer>, HashSimpleOrProofOnlyVariable> integer_variable_definition_bounds;
    unordered_map<SimpleOrProofOnlyIntegerVariableID, pair<ProofLine, ProofLine>, HashSimpleOrProofOnlyVariable> integer_variable_bound_rows;
    // Variables (e.g. ArgSort's cake-named free-bit-sum sorted values) whose [lo, hi]
    // domain is NOT a trivial consequence of the OPB -- cake emits no bound line for
    // them and the bounds are only entailed through conditional channels -- so
    // need_gevar's fix_bound must not pin their boundary order literals; those bounds
    // are instead established once, explicitly, by the owning constraint's proof.
    std::set<SimpleOrProofOnlyIntegerVariableID> bounds_not_trivially_derivable;
    // Variables whose order-encoding (ge) atom definitions carry @i[..][ge] labels that
    // a cake_pb_cp OPB does not create (it reifies each atom per value under its own
    // @c[peq..] labels). need_gevar recovers those labels in-proof for these variables:
    // it re-declares each half's reification via an `ia` line under our @i label at
    // proof start, so the order-chain pols resolve against them in both the solver's own
    // OPB (workflow 1) and cake's re-derived OPB (workflow 2). Used for ArgSort's
    // permutation variables, whose eq atoms are OPB constraint terms/guards (matching
    // cake) and so are forced model-time under @i labels.
    std::set<SimpleOrProofOnlyIntegerVariableID> vars_recover_labels;
    // Real variables whose order encoding must stay RESIDENT (every ge definition at
    // Top, tagged level 0) even under OrderEncodingDeletion::Literals, because a
    // permanent (Top) constraint names their ges: deleting a def on backtrack would
    // leave that Top line naming a deleted literal, which VeriPB rejects. Populated at
    // model-build time by note_order_encoding_stays_resident, called from
    // ProofModel::register_state_variable_bits_in_proof for the in-proof-bit auxiliary
    // magnitudes (divide/modulus), whose ges the product-justification caches pin at Top.
    // The other resident class -- a view's underlying variable, named by the always-at-Top
    // view-bridge pol lines -- is detected directly from views_of_variable in need_gevar,
    // not carried here.
    std::set<SimpleOrProofOnlyIntegerVariableID> order_encoding_stays_resident;
    // The values with ge atoms, per variable, in value order: need_gevar's
    // order-encoding chain links join each new atom to its neighbours, which
    // needs ordered iteration. The atoms' literals and defining lines live in
    // the per-variable atom tables.
    unordered_map<SimpleOrProofOnlyIntegerVariableID, std::set<Integer>, HashSimpleOrProofOnlyVariable> gevar_values;
    // Range ("in") literals [lo, hi], keyed by (lo, hi): the forward and reverse
    // lines of the reification against the variable's two order cuts. The literal
    // itself lives in the per-variable atom tables, keyed by the InRange / NotInRange
    // conditions, just like the eq and order atoms. A width-1 interval is its eq
    // atom and is never entered here.
    unordered_map<SimpleOrProofOnlyIntegerVariableID, map<pair<Integer, Integer>, pair<ProofLine, ProofLine>>, HashSimpleOrProofOnlyVariable>
        invars_that_exist;

    // Every range and eq literal on each variable, as intervals, for finding a new
    // literal's immediate neighbours in the containment order.
    map<SimpleOrProofOnlyIntegerVariableID, IntervalTree> containment_trees;

    // The always-covered partition for each variable with interval literals: the
    // sorted cell start points, always containing the definition lower bound and
    // ub+1 as a sentinel, so the cells are the intervals between consecutive
    // boundaries. Every cell has a literal, every eq atom on a partitioned
    // variable is a singleton cell, and every requested interval is a union of
    // adjacent cells. Absent until the first interval request.
    map<SimpleOrProofOnlyIntegerVariableID, std::set<Integer>> interval_partitions;

    unordered_map<ViewOfIntegerVariableID, ProofOnlySimpleIntegerVariableID, HashView> view_proof_only_vars;
    map<ProofOnlySimpleIntegerVariableID, ViewOfIntegerVariableID> view_proof_only_to_view;
    // For each registered view, the (LE-half, GE-half) ProofLine IDs of the
    // bit-vector link constraint emitted in need_view. The LE half is
    // `BinEnc(V) - s*BinEnc(X) <= c`, the GE half is `>= c`. Used by need_gevar
    // to pol-derive atom-level links from each V-atom to the corresponding
    // X-atom.
    map<ProofOnlySimpleIntegerVariableID, pair<ProofLine, ProofLine>> view_link_ids;

    // Reverse index: for each underlying variable, the proof-only IDs of
    // all views currently registered over it. Lets need_gevar /
    // need_direct_encoding_for on the X side back-emit the V-side atoms
    // (and thereby the V<->X link) when an X atom is introduced after a
    // view has been registered. When views are registered AFTER an X atom
    // already exists, need_view itself backfills via this map's setup.
    std::map<SimpleIntegerVariableID, std::vector<ProofOnlySimpleIntegerVariableID>> views_of_variable;

    // For each V-form proof line that has a derived deview-form, the
    // corresponding deview-form line. Lookup via deviewed_line_for.
    map<ProofLine, ProofLine> deviewed_line_by_v_form;

    unordered_map<ProofFlag, XLiteral, HashProofFlag> flags;

    map<SimpleOrProofOnlyIntegerVariableID, string> id_names;
    // The PB-file rendering of every allocated XLiteral, indexed 2 * id +
    // negated (ids are allocated sequentially from 1). Populated in both
    // naming modes, so rendering a literal is an index, not a lookup.
    vector<string> xlit_names;
    map<ProofFlag, string> flag_names;

    list<function<auto(ProofLogger * const)->void>> delayed_proof_steps;

    bool use_friendly_names = true;
    unsigned model_variables = 0;
    long long next_xliteral_nr = 0;

    optional<fstream> variables_map_file;
    string variables_map_file_name;
    bool first_varmap_entry = true;
    bool finalised = false;
    bool verbose_names;
    bool use_compact_boolean_encoding = false;
    AssertionLevel assertion_level = AssertionLevel::Off;

    // Whether (and how) order-encoding chain links are deleted on backtrack.
    OrderEncodingDeletion order_link_deletion_mode = OrderEncodingDeletion::None;
    // Set while a chain-link pol is being built. Building the pol re-enters
    // need_gevar (via add_for_literal -> need_pol_item_defining_literal) for the
    // two thresholds it references; this guard stops the fast path from cascading
    // link re-emission back through those calls. The pol only needs the resident
    // (Top) ge definitions, which the suppressed need_gevar still returns.
    bool building_order_link = false;
    // When order-link deletion is on: for each real variable, the adjacent-threshold
    // chain links currently present in the proof, keyed by the (lower, higher)
    // threshold pair and tagged with the proof level they were emitted at. Model-time
    // links are tagged 0 (Top, never forgotten); proof-time links are tagged with the
    // active proof level, so forget_proof_level deletes and forget_order_links_at_level
    // drops them together. Left empty and untouched when the mode is off.
    map<SimpleIntegerVariableID, map<pair<Integer, Integer>, int>> live_order_links;
    // Level index over live_order_links: for each proof level, the (id, {lo, hi})
    // links recorded at it, appended on emit. forget_order_links_at_level walks only
    // the bucket for the forgotten level (O(links-at-level)) instead of scanning every
    // variable. A link is only re-emitted after being forgotten (removed from both
    // structures), so it is never double-indexed within a level's bucket. Bucket 0
    // holds Top links and is never forgotten.
    map<int, vector<pair<SimpleIntegerVariableID, pair<Integer, Integer>>>> order_links_by_level;

    // --- Literals mode (OrderEncodingDeletion::Literals) ---
    // For each real variable, the currently-live ge thresholds, each tagged with the
    // proof level at which its definition was recorded. Level 0 means a Top literal
    // (a model-time atom or a boundary literal, whose def stays resident and is never
    // forgotten); a positive level means a search-introduced interior literal whose
    // def lives at ProofLevel::Current and is deleted when that level is forgotten.
    // Left empty and untouched unless the mode is Literals.
    map<SimpleIntegerVariableID, map<Integer, int>> live_order_literals;
    // Level index over live_order_literals holding only the deletable (Current)
    // thresholds: for each proof level, the (id, threshold) literals whose defs were
    // recorded at it. forget_order_literals_at_level walks just the forgotten level's
    // bucket (O(deleted)) to stitch and prune, instead of scanning every variable.
    // Level-0 (Top) literals are never indexed here, so they are never forgotten.
    map<int, vector<pair<SimpleIntegerVariableID, Integer>>> order_literals_by_level;

    // --- GCS_ORDER_ENCODING_STATS pin-apportionment diagnostic (Literals mode only) ---
    // Everything below is touched ONLY when collect_order_encoding_stats is true
    // (Literals mode AND the env var set). It is pure bookkeeping -- no proof bytes are
    // emitted -- swept and printed to stderr once at proof end (dump_order_encoding_stats).
    // Cheap map ops at rare events, so it can run whenever the diagnostic is requested
    // without perturbing the proof.
    bool collect_order_encoding_stats = false;
    // For every real-variable proof-time ge threshold ever recorded live: its Top
    // residency cause once it reaches Top (first-cause-wins), or nullopt while it is a
    // deletable literal (currently at a positive level, or deleted). Key presence means
    // "seen"; the entry persists across delete/reintroduce, so the map size is the count
    // of distinct real-var ge atoms seen over the whole proof.
    map<SimpleIntegerVariableID, map<Integer, optional<OrderEncodingResidencyCause>>> stats_ge_top_cause;
    // Event counters.
    long long stats_deletes = 0;                                    // literals dropped by forget_order_literals_at_level.
    long long stats_stitches = 0;                                   // forget-path skip-link emissions (emit_order_stitch).
    long long stats_reintroductions = 0;                            // reintroduce_order_literal calls.
    long long stats_dup_top_stitches = 0;                           // Top-level stitch clauses re-emitted for an already-linked pair.
    map<OrderEncodingResidencyCause, long long> stats_hoist_events; // actual hoist events, by cause.
    // Top-level (level-0) stitch pairs already emitted per variable, for cheap
    // duplicate-Top-stitch detection.
    map<SimpleIntegerVariableID, std::set<pair<Integer, Integer>>> stats_top_stitch_pairs;
};

NamesAndIDsTracker::NamesAndIDsTracker(const ProofOptions & proof_options) : _imp(make_unique<Imp>())
{
    _imp->verbose_names = proof_options.verbose_names;
    _imp->use_compact_boolean_encoding = proof_options.use_compact_boolean_encoding;
    _imp->assertion_level = proof_options.assertion_level;
    _imp->order_link_deletion_mode = proof_options.order_encoding_deletion;

    // The pin-apportionment diagnostic collects only under OrderEncodingDeletion::Literals
    // (the only mode with deletable/hoistable order literals) AND when GCS_ORDER_ENCODING_STATS
    // holds any non-empty value. Cached once here; gates every stats hook so nothing runs on
    // the default (deletion-off) path or when the diagnostic is not requested.
    if (_imp->order_link_deletion_mode == OrderEncodingDeletion::Literals) {
        const auto * const stats_env = std::getenv("GCS_ORDER_ENCODING_STATS");
        _imp->collect_order_encoding_stats = stats_env != nullptr && *stats_env != '\0';
    }

    if (proof_options.proof_file_names.variables_map_file) {
        _imp->variables_map_file_name = *proof_options.proof_file_names.variables_map_file;
        _imp->variables_map_file.emplace();
        try {
            _imp->variables_map_file->exceptions(ios::failbit | ios::badbit);
            _imp->variables_map_file->open(_imp->variables_map_file_name, ios::out);
            *_imp->variables_map_file << "{\n";
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }
}

NamesAndIDsTracker::~NamesAndIDsTracker()
{
    if (_imp->variables_map_file && ! _imp->finalised && std::uncaught_exceptions() == 0) {
        print(stderr, "NamesAndIDsTracker destroyed without calling finalise()\n");
        std::abort();
    }
}

auto NamesAndIDsTracker::finalise() -> void
{
    _imp->finalised = true;
    if (_imp->variables_map_file) {
        try {
            *_imp->variables_map_file << "\n}\n";
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }
}

auto NamesAndIDsTracker::emit_proof_line_now_or_at_start(const function<auto(ProofLogger * const)->void> & func) -> void
{
    if (_imp->logger)
        func(_imp->logger);
    else
        _imp->delayed_proof_steps.push_back(func);
}

auto NamesAndIDsTracker::switch_from_model_to_proof(ProofLogger * const logger) -> void
{
    _imp->model = nullptr;
    _imp->logger = logger;
}

auto NamesAndIDsTracker::emit_delayed_proof_steps() -> void
{
    for (const auto & step : _imp->delayed_proof_steps)
        step(_imp->logger);
    _imp->delayed_proof_steps.clear();
}

auto NamesAndIDsTracker::start_writing_model(ProofModel * const model) -> void
{
    _imp->model = model;
}

auto NamesAndIDsTracker::associate_condition_with_xliteral(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond, const XLiteral & x)
    -> void
{
    _imp->store_condition(cond, x);
}

auto NamesAndIDsTracker::track_variable_takes_at_least_one_value(const SimpleOrProofOnlyIntegerVariableID & id, ProofLine line) -> void
{
    _imp->variable_at_least_one_constraints.emplace(id, line);
}

auto NamesAndIDsTracker::need_constraint_saying_variable_takes_at_least_one_value(IntegerVariableID var) -> ProofLine
{
    return overloaded{
        [&](const ConstantIntegerVariableID &) -> ProofLine { throw UnimplementedException{}; }, //
        [&](const SimpleIntegerVariableID & var) -> ProofLine {
            auto result = _imp->variable_at_least_one_constraints.find(var);
            if (result == _imp->variable_at_least_one_constraints.end()) {
                WPBSum al1s;
                auto [lower, upper] = _imp->integer_variable_definition_bounds.at(var);
                for (Integer v = lower; v <= upper; ++v)
                    al1s += 1_i * (var == v);

                auto line = _imp->logger->emit_rup_proof_line(al1s >= 1_i, ProofLevel::Top);
                result = _imp->variable_at_least_one_constraints.emplace(var, line).first;
            }
            return result->second;
        }, //
        [&](const ViewOfIntegerVariableID & var) -> ProofLine {
            // For a registered view, emit AL1 in V-form so it cancels
            // cleanly against AM1s that already reference V-form atoms
            // (those go through need_pol_item_defining_literal, which
            // returns the V's eqvar when the view is registered). Falling
            // back to the X-form AL1 here used to leave Hall-set proofs in
            // gac_all_different unable to RUP their conclusion: the AL1
            // contributed `+x[eq w]` terms while AM1s contributed
            // `-p_view[eq W]` terms, with no shared atoms to cancel.
            if (auto v_id = find_view(var)) {
                auto result = _imp->variable_at_least_one_constraints.find(*v_id);
                if (result == _imp->variable_at_least_one_constraints.end()) {
                    WPBSum al1s;
                    auto [lower, upper] = _imp->integer_variable_definition_bounds.at(*v_id);
                    for (Integer v = lower; v <= upper; ++v)
                        al1s += 1_i * (*v_id == v);

                    auto line = _imp->logger->emit_rup_proof_line(al1s >= 1_i, ProofLevel::Top);
                    result = _imp->variable_at_least_one_constraints.emplace(*v_id, line).first;
                }
                return result->second;
            }
            return need_constraint_saying_variable_takes_at_least_one_value(var.actual_variable);
        } //
    }
        .visit(var);
}

auto NamesAndIDsTracker::need_pol_item_defining_literal(const IntegerVariableCondition & cond) -> variant<ProofLine, XLiteral>
{
    return overloaded{
        [&](const ConstantIntegerVariableID &) -> variant<ProofLine,                              //
                                                   XLiteral> { throw UnimplementedException{}; }, //
        [&](const SimpleIntegerVariableID & var) -> variant<ProofLine, XLiteral> {
            switch (cond.op) {
                using enum VariableConditionOperator;
            case GreaterEqual: need_gevar(var, cond.value); return _imp->atoms_for(var).ge_defs.at(cond.value.raw_value).first;
            case Less: need_gevar(var, cond.value); return _imp->atoms_for(var).ge_defs.at(cond.value.raw_value).second;
            case Equal: need_direct_encoding_for(var, cond.value); return _imp->atoms_for(var).eq_defs.at(cond.value.raw_value).first;
            case NotEqual: need_direct_encoding_for(var, cond.value); return _imp->atoms_for(var).eq_defs.at(cond.value.raw_value).second;
            case InRange:
                static_cast<void>(need_invar(var, cond.value, cond.upper_value));
                return _imp->invars_that_exist.at(var).at(pair{cond.value, cond.upper_value}).first;
            case NotInRange:
                static_cast<void>(need_invar(var, cond.value, cond.upper_value));
                return _imp->invars_that_exist.at(var).at(pair{cond.value, cond.upper_value}).second;
            }
            throw NonExhaustiveSwitch{};
        }, //
        [&](const ViewOfIntegerVariableID & var) -> variant<ProofLine, XLiteral> {
            // If the view's been registered, V's atoms have proper Defs over
            // BinEnc(V) and the pol-item path looks just like a simple
            // variable's. The Equal/NotEqual throws below only fire on the
            // deview fallback for views first seen during proof logging.
            if (auto v_id = find_view(var)) {
                switch (cond.op) {
                    using enum VariableConditionOperator;
                case GreaterEqual: need_gevar(*v_id, cond.value); return _imp->atoms_for(*v_id).ge_defs.at(cond.value.raw_value).first;
                case Less: need_gevar(*v_id, cond.value); return _imp->atoms_for(*v_id).ge_defs.at(cond.value.raw_value).second;
                case Equal: need_direct_encoding_for(*v_id, cond.value); return _imp->atoms_for(*v_id).eq_defs.at(cond.value.raw_value).first;
                case NotEqual: need_direct_encoding_for(*v_id, cond.value); return _imp->atoms_for(*v_id).eq_defs.at(cond.value.raw_value).second;
                case InRange:
                case NotInRange: throw UnimplementedException{};
                }
                throw NonExhaustiveSwitch{};
            }
            switch (cond.op) {
                using enum VariableConditionOperator;
            case GreaterEqual:
                if (var.negate_first)
                    return need_pol_item_defining_literal(var.actual_variable < -(cond.value - var.then_add) + 1_i);
                else
                    return need_pol_item_defining_literal(var.actual_variable >= cond.value - var.then_add);
            case Less:
                if (var.negate_first)
                    return need_pol_item_defining_literal(var.actual_variable >= -(cond.value - var.then_add) + 1_i);
                else
                    return need_pol_item_defining_literal(var.actual_variable < cond.value - var.then_add);
            case Equal: throw UnimplementedException{};
            case NotEqual: throw UnimplementedException{};
            case InRange:
            case NotInRange: throw UnimplementedException{};
            }
            throw NonExhaustiveSwitch{};
        } //
    }
        .visit(cond.var);
}

auto NamesAndIDsTracker::create_literals_for_introduced_variable_value(SimpleIntegerVariableID id, Integer val, const string & name) -> void
{
    // These literals bypass the eq-atom defs table and the containment structures, which
    // is safe because an introduced variable has no bits encoding, so no range
    // literal can ever be defined over it.
    track_variable_name(id, to_string(id.index) + "intr_" + name); // hack!
    auto x = allocate_xliteral_meaning(id, EqualsOrGreaterEqual::Equals, val);
    _imp->store_condition(id == val, x);
}

auto NamesAndIDsTracker::need_proof_name(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) -> void
{
    switch (cond.op) {
        using enum VariableConditionOperator;
    case Equal:
    case NotEqual: need_direct_encoding_for(cond.var, cond.value); break;
    case Less:
    case GreaterEqual: need_gevar(cond.var, cond.value); break;
    case InRange:
    case NotInRange:
        if (! _imp->find_condition(cond))
            static_cast<void>(need_invar(cond.var, cond.value, cond.upper_value));
        break;
    }
}

auto NamesAndIDsTracker::need_all_proof_names_in(const SumOf<Weighted<PseudoBooleanTerm>> & sum) -> void
{
    for (auto & [_, v] : sum.terms)
        overloaded{
            [&](const ProofLiteral & lit) {
                overloaded{
                    [&](const TrueLiteral &) {},                                                        //
                    [&](const FalseLiteral &) {},                                                       //
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) { need_proof_name(cond); } //
                }
                    .visit(simplify_literal(*this, lit));
            },                         //
            [&](const ProofFlag &) {}, //
            [&](const IntegerVariableID & var) {
                // Opportunistically register view bit vectors during model
                // writing. need_view can only introduce a view while the
                // model is being written (it throws during the proof-logging
                // phase), so this is gated on _imp->model.
                if (_imp->model)
                    if (auto view = std::get_if<ViewOfIntegerVariableID>(&var))
                        static_cast<void>(need_view(*view));
            },                                                //
            [&](const ProofOnlySimpleIntegerVariableID &) {}, //
            [&](const ProofBitVariable &) {}                  //
        }
            .visit(v);
}

auto NamesAndIDsTracker::need_all_proof_names_in(const Literals & lits) -> void
{
    for (auto & lit : lits)
        overloaded{
            [&](const TrueLiteral &) {},                                                        //
            [&](const FalseLiteral &) {},                                                       //
            [&]<typename T_>(const VariableConditionFrom<T_> & cond) { need_proof_name(cond); } //
        }
            .visit(simplify_literal(*this, lit));
}

auto NamesAndIDsTracker::need_all_proof_names_in(const HalfReifyOnConjunctionOf & h) -> void
{
    for (auto & term : h)
        overloaded{
            [&](const ProofLiteral & lit) {
                overloaded{
                    [&](const TrueLiteral &) {},                                                        //
                    [&](const FalseLiteral &) {},                                                       //
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) { need_proof_name(cond); } //
                }
                    .visit(simplify_literal(*this, lit));
            },                               //
            [&](const ProofFlag &) {},       //
            [&](const ProofBitVariable &) {} //
        }
            .visit(term);
}

auto NamesAndIDsTracker::negative_bit_coefficient(const SimpleOrProofOnlyIntegerVariableID & id) -> Integer
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(id);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");
    return it->second.first;
}

auto NamesAndIDsTracker::each_bit(const SimpleOrProofOnlyIntegerVariableID & id) -> generator<pair<Integer, XLiteral>>
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(id);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");
    for (auto & [c, n] : it->second.second)
        co_yield pair{c, n};
}

auto NamesAndIDsTracker::get_bit(const gcs::innards::SimpleOrProofOnlyIntegerVariableID & var, Integer position) -> pair<Integer, XLiteral>
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(var);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");

    return it->second.second.at(position.as_index());
}

auto NamesAndIDsTracker::get_bit(const ProofBitVariable & bit) -> pair<Integer, XLiteral>
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(bit.for_var);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");

    auto bit_data = it->second.second.at(bit.position.as_index());

    if (! bit.positive)
        bit_data.second.negated = ! bit_data.second.negated;

    return bit_data;
}

auto NamesAndIDsTracker::num_bits(const gcs::innards::SimpleOrProofOnlyIntegerVariableID & var) -> Integer
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(var);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");

    return Integer(it->second.second.size());
}

auto NamesAndIDsTracker::track_bits(
    const SimpleOrProofOnlyIntegerVariableID & id, Integer negative_coeff, const vector<pair<Integer, XLiteral>> & bit_vars) -> void
{
    _imp->integer_variable_bits_to_size_and_proof_vars.emplace(id, pair{negative_coeff, bit_vars});
}

auto NamesAndIDsTracker::allocate_flag_index() -> unsigned long long
{
    return _imp->flags.size() / 2;
}

auto NamesAndIDsTracker::track_eqvar(
    SimpleIntegerVariableID id, Integer val, const pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>> & names) -> void
{
    _imp->atoms_for(id).eq_defs.try_emplace(val.raw_value, names);
}

auto NamesAndIDsTracker::need_direct_encoding_for(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> void
{
    if (_imp->find_condition(id == v))
        return;

    auto eqvar = allocate_xliteral_meaning(id, EqualsOrGreaterEqual::Equals, v);
    _imp->store_condition(id == v, eqvar);

    auto bounds = _imp->integer_variable_definition_bounds.find(id);
    ProofLine forwards_line, reverse_line;

    // Model-path eq-atom definitions are labelled @<base>[eq<v>][r]/[f] (see
    // definitional_label_base): @i[name] for a real variable, @po[index] for a
    // proof-only one, so they are referenced (e.g. in a view's deview-form) by
    // name rather than line number. A bracket-nesting real-variable name has no
    // valid label and falls back to the unlabelled definitional form.
    auto eq_base = definitional_label_base(id);
    auto add_eq = [&](const char * role, const WPBSumLE & ineq, const HalfReifyOnConjunctionOf & reif) -> ProofLine {
        return _imp->model->add_labelled_constraint(eq_base + "[eq" + to_string(v.raw_value) + "][" + role + "]", ineq, reif);
    };

    // The compact boolean encoding defines an eq atom at a bound using only the
    // one non-trivial order literal (eq(lower) <=> ~ge(lower+1), since ge(lower)
    // is always true; eq(upper) <=> ge(upper), since ge(upper+1) is always
    // false). With it off (the default), every eq atom -- including those at the
    // bounds -- is the full eq(v) <=> ge(v) & ~ge(v+1), so the trivial ge(lower)
    // and ge(upper+1) literals are materialised (need_gevar emits and fixes
    // them), matching cake_pb_cp's eager encoding.
    if (_imp->use_compact_boolean_encoding && bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.first == v) {
        // it's a lower bound
        if (_imp->logger && _imp->assertion_level <= AssertionLevel::Links) {
            visit(
                [&](const auto & id) {
                    auto [_f_line, _r_line] =
                        _imp->logger->emit_red_proof_lines_reifying(WPBSum{} + 1_i * ! (id >= (v + 1_i)) >= 1_i, id == v, ProofLevel::Top);
                    forwards_line = _f_line;
                    reverse_line = _r_line;
                },
                id);
        }
        else if (! _imp->logger) {
            visit(
                [&](const auto & id) {
                    forwards_line = add_eq("r", WPBSum{} + 1_i * ! (id >= (v + 1_i)) >= 1_i, {{id == v}});
                    reverse_line = add_eq("f", WPBSum{} + 1_i * (id >= (v + 1_i)) >= 1_i, {{id != v}});
                },
                id);
            ++_imp->model_variables;
        }
    }
    else if (_imp->use_compact_boolean_encoding && bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.second == v) {
        // it's an upper bound
        if (_imp->logger && _imp->assertion_level <= AssertionLevel::Links) {
            visit(
                [&](const auto & id) {
                    auto [_f_line, _r_line] =
                        _imp->logger->emit_red_proof_lines_reifying(WPBSum{} + 1_i * (id >= v) >= 1_i, id == v, ProofLevel::Top);
                    forwards_line = _f_line;
                    reverse_line = _r_line;
                },
                id);
        }
        else if (! _imp->logger) {
            visit(
                [&](const auto & id) {
                    forwards_line = add_eq("r", WPBSum{} + 1_i * (id >= v) >= 1_i, {{id == v}});
                    reverse_line = add_eq("f", WPBSum{} + 1_i * ! (id >= v) >= 1_i, {{id != v}});
                },
                id);
            ++_imp->model_variables;
        }
    }
    else {
        // neither a lower nor an upper bound
        if (_imp->logger && _imp->assertion_level <= AssertionLevel::Links)
            visit(
                [&](const auto & id) {
                    auto [_f_line, _r_line] = _imp->logger->emit_red_proof_lines_reifying(
                        WPBSum{} + (1_i * (id >= v)) + (1_i * ! (id > v)) >= 2_i, id == v, ProofLevel::Top);
                    forwards_line = _f_line;
                    reverse_line = _r_line;
                },
                id);
        else if (! _imp->logger) {
            visit(
                [&](const auto & id) {
                    forwards_line = add_eq("r", WPBSum{} + 1_i * (id >= v) + 1_i * ! (id > v) >= 2_i, {{id == v}});
                    reverse_line = add_eq("f", WPBSum{} + 1_i * ! (id >= v) + 1_i * (id > v) >= 1_i, {{id != v}});
                },
                id);
            ++_imp->model_variables;
        }
    }

    _imp->atoms_for(id).eq_defs.try_emplace(v.raw_value, pair{forwards_line, reverse_line});

    // Literals order-encoding-deletion mode: this eq atom's definition was emitted at
    // ProofLevel::Top (permanent) above, and names ge(v) and ge(v+1). The
    // need_all_proof_names_in inside that emission has made both live; but for an
    // interior threshold their def lands at Current, so a later backtrack forget would
    // delete it -- leaving this surviving Top eq def (and any solx / backtrack clause /
    // value-branch guess over the eq atom) naming a deleted ge, which rejects in VeriPB
    // (the failure this mode showed on eq-heavy instances). Hoist both ge defs to Top so
    // they stay resident for the eq atom's whole lifetime.
    hoist_ges_named_by_top_atom(id, v, v + 1_i, OrderEncodingResidencyCause::EqHoist);

    // If `id` is a view's proof-only var, eagerly emit the
    // eq-atom-level link `V=v <=> X=k_x` as two RUP lines. The GE-atom
    // links + the V- and X-side eq Defs are already in F at this point
    // (need_gevar(V,v), need_gevar(V,v+1), and need_direct_encoding_for(X,k_x)
    // are all called by this point), so each direction is UP-closable:
    //
    //   ~V=v OR X=k_x:  V=v UP-derives V>=v and ~V>=v+1 (eq fwd),
    //     then x_cond and ~x_cond+1 via GE links, then X=k_x by Def(X=k_x)
    //     reverse fed with both sides forced -- conflict with assumed ~X=k_x.
    //   ~X=k_x OR V=v:  symmetric.
    //
    // Without these eq-atom links, propagator-derived V<->Y lemmas combined
    // with X-atom guesses from search couldn't UP-chain V=v <-> X=k_x, and
    // backtrack-from-guess Bt verifications stalled with several remaining
    // values for Y.
    if (auto pid_ptr = std::get_if<ProofOnlySimpleIntegerVariableID>(&id)) {
        auto view_it = _imp->view_proof_only_to_view.find(*pid_ptr);
        if (view_it != _imp->view_proof_only_to_view.end()) {
            const auto & view = view_it->second;
            // V := s*X + c, V=v <=> X = (v-c)/s.
            //   s=+1: X = v - c.
            //   s=-1: X = c - v.
            Integer x_threshold = view.negate_first ? view.then_add - v : v - view.then_add;
            need_direct_encoding_for(view.actual_variable, x_threshold);

            ProofVariableCondition v_cond{*pid_ptr, VariableConditionOperator::Equal, v};
            IntegerVariableID x_var{view.actual_variable};
            auto x_cond = (x_var == x_threshold);
            // Always queue this (it delays to proof start when the logger
            // isn't attached yet during model building); decide whether to
            // emit based on using_assertions() *inside* the lambda, when the
            // logger definitely exists. Guarding on _imp->logger out here
            // drops the step entirely during model building, losing the
            // channelling between the proof-only encoding and the actual
            // variable. See the matching pattern in need_gevar's bound links.
            emit_proof_line_now_or_at_start([v_cond, x_cond](ProofLogger * const logger) {
                if (logger->get_assertion_level() > AssertionLevel::Links)
                    return;

                auto assert_or_rup =
                    logger->get_assertion_level() == AssertionLevel::Links ? ProofRule(AssertProofRule{}) : ProofRule(RUPProofRule{});
                logger->emit(assert_or_rup, WPBSum{} + 1_i * ! v_cond + 1_i * x_cond >= 1_i, ProofLevel::Top);
                logger->emit(assert_or_rup, WPBSum{} + 1_i * ! x_cond + 1_i * v_cond >= 1_i, ProofLevel::Top);
            });
        }
    }

    // Nothing beyond this point needs to be emmitted at AssertionLevel::Links
    if (_imp->assertion_level > AssertionLevel::Links)
        return;

    // Reverse direction: see the matching block in need_gevar above.
    if (auto sid_ptr = std::get_if<SimpleIntegerVariableID>(&id)) {
        if (auto it = _imp->views_of_variable.find(*sid_ptr); it != _imp->views_of_variable.end()) {
            auto views_copy = it->second;
            for (const auto & view_pid : views_copy) {
                const auto & view = _imp->view_proof_only_to_view.at(view_pid);
                Integer v_value = view.negate_first ? view.then_add - v : v + view.then_add;
                need_direct_encoding_for(view_pid, v_value);
            }
        }
    }

    // Link this new eq atom (a singleton [v, v]) to its immediate range containers,
    // so a rejected container propagates ~(id == v). Most variables never have any
    // range literals, so the containment tree is only maintained once one exists.
    link_immediate_containment(id, v, v);
    if (auto tree = _imp->containment_trees.find(id); tree != _imp->containment_trees.end())
        tree->second.insert(v, v);

    // On a partitioned variable, every eq atom is a singleton cell: split the
    // containing cell, so that interval coverings reach the atoms that per-value
    // conclusions are logged over.
    if (_imp->interval_partitions.contains(id)) {
        auto [lb, ub] = _imp->integer_variable_definition_bounds.at(id);
        if (lb <= v && v <= ub) {
            ensure_partition_cut(id, v);
            ensure_partition_cut(id, v + 1_i);
        }
    }
}

auto NamesAndIDsTracker::definitional_label_base(const SimpleOrProofOnlyIntegerVariableID & id) const -> string
{
    return visit(overloaded{                                                                              //
                     [&](const SimpleIntegerVariableID &) -> string { return "i[" + name_of(id) + "]"; }, //
                     [&](const ProofOnlySimpleIntegerVariableID & pid) -> string { return "po[" + to_string(pid.index) + "]"; }},
        id);
}

auto NamesAndIDsTracker::need_gevar(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> void
{
    if (_imp->find_condition(id >= v)) {
        // Fast path: the ge atom and its definition already exist, so they are never
        // recreated. With order-link deletion on, though, a previous backtrack may
        // have deleted some of this variable's chain links; reconnect its whole order
        // chain so any order reasoning a RUP needs is available. Only real variables
        // carry deletable chain links. building_order_link suppresses this while a
        // chain-link pol is being built (those need_gevar calls only want the resident
        // definitions).
        if (_imp->order_link_deletion_mode == OrderEncodingDeletion::Links && _imp->logger && ! _imp->building_order_link) {
            if (auto sid_ptr = std::get_if<SimpleIntegerVariableID>(&id))
                ensure_order_chain_connected(*sid_ptr);
        }
        else if (_imp->order_link_deletion_mode == OrderEncodingDeletion::Literals && _imp->logger && _imp->assertion_level == AssertionLevel::Off &&
            ! _imp->building_order_link) {
            // Literals mode: the atom is permanent, but its definition may have been
            // deleted by an earlier backtrack. If this threshold is no longer live,
            // re-introduce it (re-emit its def at Current and re-link it to its current
            // live neighbours). Boundary / model-time literals are tagged level 0 and
            // never leave the live set, so this only fires for interior literals. A
            // ge aliased to a preserved bit (DirectOnly {0,1}) is skipped: it has no
            // proof-time reification to delete or re-introduce, and re-emitting one would
            // put the preserved bit in a red witness -- rejected at a derived level.
            if (auto sid_ptr = std::get_if<SimpleIntegerVariableID>(&id)) {
                auto live_it = _imp->live_order_literals.find(*sid_ptr);
                if ((live_it == _imp->live_order_literals.end() || ! live_it->second.contains(v)) && ! order_literal_aliased_to_bit(id, v))
                    reintroduce_order_literal(*sid_ptr, v);
            }
        }
        return;
    }

    auto gevar = allocate_xliteral_meaning(id, EqualsOrGreaterEqual::GreaterEqual, v);
    _imp->store_condition(id >= v, gevar);

    // Literals order-encoding-deletion mode: a real variable's non-boundary ge
    // definition is emitted at ProofLevel::Current, so a backtrack deletes it and a
    // later reference re-introduces it. Boundary literals (whose bound pin makes them
    // trivially true/false and which serve as permanent chain anchors) and model-time
    // atoms (logger not yet attached) keep their def resident at Top, tagged level 0.
    // Computed here because the def is emitted just below, before the fix_bound block.
    bool literals_real = _imp->order_link_deletion_mode == OrderEncodingDeletion::Literals && _imp->assertion_level == AssertionLevel::Off &&
        std::holds_alternative<SimpleIntegerVariableID>(id);
    bool literals_proof_time = literals_real && _imp->logger != nullptr;
    bool def_at_current = false;
    // Stats: the born-Top cause for this ge, set below alongside the def_at_current
    // decision (nullopt for a born-deletable interior literal). Only ever read under the
    // collect guard; kept in step with the residency logic it mirrors.
    optional<OrderEncodingResidencyCause> stats_born_cause;
    if (literals_proof_time) {
        auto b = _imp->integer_variable_definition_bounds.find(id);
        bool trivial_boundary = ! _imp->bounds_not_trivially_derivable.contains(id);
        bool boundary = trivial_boundary && b != _imp->integer_variable_definition_bounds.end() && (b->second.first >= v || b->second.second < v);
        def_at_current = ! boundary;
        // Two classes of real variable keep their WHOLE order encoding resident (def at
        // Top, like the deletion-off mode), because a permanent (Top) constraint names
        // their ges and a deleted def would strand that Top line on a deleted literal
        // (VeriPB rejects the resulting proofgoal):
        //  - an in-proof-bit auxiliary magnitude (register_state_variable_bits_in_proof),
        //    whose ges the divide/modulus product-justification caches pin at Top;
        //  - a view's underlying variable (views_of_variable), whose ge definition lines
        //    the always-at-Top view-bridge pol lines cite by number.
        // views_of_variable is only ever populated at model-build time (need_view rejects
        // a proof-phase view), so this decision is stable for every proof-time ge.
        if (def_at_current &&
            (_imp->order_encoding_stays_resident.contains(id) || _imp->views_of_variable.contains(std::get<SimpleIntegerVariableID>(id))))
            def_at_current = false;
        // Stats attribution, matching the branches just taken (boundary wins over the
        // aux/view override, which is only reached when boundary was false).
        if (_imp->collect_order_encoding_stats && ! def_at_current) {
            if (boundary)
                stats_born_cause = OrderEncodingResidencyCause::Boundary;
            else if (_imp->order_encoding_stays_resident.contains(id))
                stats_born_cause = OrderEncodingResidencyCause::AuxPin;
            else
                stats_born_cause = OrderEncodingResidencyCause::ViewPin;
        }
    }
    else if (literals_real && _imp->collect_order_encoding_stats) {
        // Model-build-time creation (logger not yet attached): born Top, tagged model_time.
        stats_born_cause = OrderEncodingResidencyCause::ModelTime;
    }
    auto ge_def_level = def_at_current ? ProofLevel::Current : ProofLevel::Top;

    // gevar -> bits
    if (_imp->logger && _imp->assertion_level > AssertionLevel::Definitions) {
        _imp->atoms_for(id).ge_defs.try_emplace(
            v.raw_value, make_pair(ProofLine{}, ProofLine{})); // Don't output geqvar definitions if using assertions
    }
    else if (_imp->logger) {
        auto def_lines = visit(
            [&](const auto & id) { return _imp->logger->emit_red_proof_lines_reifying(WPBSum{} + (1_i * id) >= v, id >= v, ge_def_level); }, id);
        _imp->atoms_for(id).ge_defs.try_emplace(v.raw_value, def_lines);
    }
    else {
        // Label the two halves @<base>[ge<v>][r]/[f]: the base is @i[name] for a
        // real variable (matching cake_pb_cp) or @po[index] for a proof-only one
        // (cake never sees it). The first emitted half (the id>=v reif, carrying
        // ~ge..) is cake's [r]; the second is [f]. v may be negative -- veripb
        // 3.0.2 allows `-` in @labels.
        string ge_label = definitional_label_base(id) + "[ge" + to_string(v.raw_value) + "]";
        _imp->atoms_for(id).ge_defs.try_emplace(v.raw_value,
            visit(
                [&](const auto & vid) -> pair<ProofLine, ProofLine> {
                    return pair{_imp->model->add_labelled_constraint(ge_label + "[r]", WPBSum{} + (1_i * vid) >= v, {{vid >= v}}),
                        _imp->model->add_labelled_constraint(ge_label + "[f]", WPBSum{} + (-1_i * vid) >= -v + 1_i, {{vid < v}})};
                },
                id));
        ++_imp->model_variables;

        // For a variable whose @i[..][ge] labels a cake_pb_cp OPB will not create (see
        // vars_recover_labels), recover the labels in-proof: re-declare each half's
        // reification via `ia` (implies-add) under our @i label at proof start, checked
        // implied against whatever reifies the atom in the OPB -- our own @i line in
        // workflow-1, cake's per-value @c[peq..] in workflow-2. The order-chain pols
        // then resolve against the recovered labels in either. Queued here, before this
        // call emits its chain links below, so the recovery lands ahead of them in the
        // proof; the reification is reconstructed via reify() so nothing is remembered.
        if (_imp->vars_recover_labels.contains(id))
            emit_proof_line_now_or_at_start([this, id, v, ge_label](ProofLogger * const logger) {
                visit(
                    [&](const auto & vid) {
                        logger->emit(ImpliesProofRule{}, reify(WPBSum{} + (1_i * vid) >= v, {{vid >= v}}), ProofLevel::Top, std::nullopt,
                            ProofLineLabel{ge_label + "[r]"});
                        logger->emit(ImpliesProofRule{}, reify(WPBSum{} + (-1_i * vid) >= -v + 1_i, {{vid < v}}), ProofLevel::Top, std::nullopt,
                            ProofLineLabel{ge_label + "[f]"});
                    },
                    id);
            });
    }

    // Literals mode: record this real variable's ge literal as live *now*, before
    // fix_bound and the link blocks run. Those emit proof lines whose
    // need_all_proof_names_in re-enters need_gevar(id, v); recording first means that
    // re-entry sees v as live and does not spuriously re-introduce it (which would also
    // wrongly re-tag a boundary literal as deletable). Linking to neighbours is done
    // after the blocks, once v is already in the live set. Model-time atoms and boundary
    // literals are tagged level 0 (def resident at Top); interior literals at Current.
    if (literals_real) {
        const auto & sid = std::get<SimpleIntegerVariableID>(id);
        record_live_order_literal(sid, v, ! def_at_current);
        // Stats: register the ge as seen and attribute any born-Top residency. For a
        // born-deletable literal stats_born_cause is nullopt (recorded seen, no Top cause).
        if (_imp->collect_order_encoding_stats)
            stats_note_ge_recorded(sid, v, stats_born_cause);
    }

    // is it a bound?
    auto bounds = _imp->integer_variable_definition_bounds.find(id);

    auto fix_bound = [&](bool negated) {
        // Pin a trivial boundary order literal -- ge(lower) (always true) or
        // ge(ub+1) (always false) -- in the PROOF, never as an OPB axiom. The fact
        // is a consequence of the variable's bound constraints, not a definition,
        // so it does not belong in the OPB; cake_pb_cp likewise derives it rather
        // than pinning it, so an OPB axiom would make our OPB diverge from cake's,
        // and -- worse -- a pin re-derived per use does not survive VeriPB's
        // post-solx enumeration restriction. Emitting it once as a persistent
        // top-of-proof line (RUP-derivable from the bound constraints, or asserted
        // at AssertionLevel::Links) keeps the OPB byte-clean and the pin available
        // throughout both enumeration and refutation. emit_proof_line_now_or_at_start
        // queues it to proof start when the logger is not yet attached (model
        // building) and emits it immediately otherwise.
        emit_proof_line_now_or_at_start([id, v, negated](ProofLogger * const logger) {
            if (logger->get_assertion_level() > AssertionLevel::Links)
                return;
            ProofRule assert_or_rup =
                logger->get_assertion_level() == AssertionLevel::Links ? ProofRule(AssertProofRule{}) : ProofRule(RUPProofRule{});
            auto annotation = AssertionAnnotation{.hint_name = hints::InitialBound::hint_name};
            visit(
                [&](auto vid) {
                    logger->emit(assert_or_rup, WPBSum{} + 1_i * (negated ? ! (vid >= v) : (vid >= v)) >= 1_i, ProofLevel::Top, annotation);
                },
                id);
        });
    };

    // A variable whose bounds are not a trivial OPB consequence (see
    // bounds_not_trivially_derivable) gets no boundary pin -- pinning it would emit a
    // top-of-proof RUP line that is not actually reverse-unit-propagatable; its owner
    // derives the bounds explicitly instead.
    bool trivial_boundary = ! _imp->bounds_not_trivially_derivable.contains(id);

    // lower?
    if (trivial_boundary && bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.first >= v) {
        fix_bound(false);
    }

    // upper?
    if (trivial_boundary && bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.second < v) {
        fix_bound(true);
    }

    auto & other_gevars = _imp->gevar_values[id];
    auto this_gevar = other_gevars.insert(v).first;
    auto higher_gevar = next(this_gevar);

    // implied by the next highest gevar, if there is one?
    auto link_hint = AssertionAnnotation{.hint_name = hints::BoundLink::hint_name};
    if (higher_gevar != other_gevars.end()) {
        overloaded{
            [&](const ProofOnlySimpleIntegerVariableID & id) {
                auto chain_con = WPBSum{} + (1_i * (id >= v)) + (1_i * ! (id >= *higher_gevar)) >= 1_i;
                emit_proof_line_now_or_at_start([c = chain_con, link_hint](ProofLogger * const logger) {
                    if (logger->get_assertion_level() > AssertionLevel::Links)
                        return;
                    ProofRule assert_or_rup =
                        logger->get_assertion_level() == AssertionLevel::Links ? ProofRule(AssertProofRule{}) : ProofRule(RUPProofRule{});
                    logger->emit(assert_or_rup, c, ProofLevel::Top, link_hint);
                });
            }, //
            [&](const SimpleIntegerVariableID & id) {
                if (_imp->assertion_level > AssertionLevel::Links) {
                    return;
                }
                else if (_imp->assertion_level == AssertionLevel::Links) {
                    auto chain_con = WPBSum{} + (1_i * (id >= v)) + (1_i * ! (id >= *higher_gevar)) >= 1_i;
                    emit_proof_line_now_or_at_start(
                        [c = chain_con, link_hint](ProofLogger * const logger) { logger->emit(AssertProofRule{}, c, ProofLevel::Top, link_hint); });
                }
                else if (! literals_proof_time) {
                    emit_and_maybe_track_order_link(id, v, *higher_gevar);
                }
                // In Literals mode at proof time, this real variable's ge literal is
                // linked to its live neighbours (not its gevars neighbours, which may
                // have been deleted) after both blocks below.
            } //
        }
            .visit(id);
    }

    // implies the next lowest gevar, if there is one?
    if (this_gevar != other_gevars.begin()) {
        overloaded{
            [&](const ProofOnlySimpleIntegerVariableID & id) {
                auto chain_con = WPBSum{} + (1_i * (id >= *prev(this_gevar))) + (1_i * ! (id >= v)) >= 1_i;
                emit_proof_line_now_or_at_start([c = chain_con, link_hint = link_hint](ProofLogger * const logger) {
                    if (logger->get_assertion_level() > AssertionLevel::Links)
                        return;
                    ProofRule assert_or_rup =
                        logger->get_assertion_level() == AssertionLevel::Links ? ProofRule(AssertProofRule{}) : ProofRule(RUPProofRule{});
                    logger->emit(assert_or_rup, c, ProofLevel::Top, link_hint);
                });
            }, //
            [&](const SimpleIntegerVariableID & id) {
                if (_imp->assertion_level > AssertionLevel::Links) {
                    return;
                }
                else if (_imp->assertion_level == AssertionLevel::Links) {
                    auto chain_con = WPBSum{} + (1_i * (id >= *prev(this_gevar))) + (1_i * ! (id >= v)) >= 1_i;
                    emit_proof_line_now_or_at_start([c = chain_con, link_hint = link_hint](ProofLogger * const logger) {
                        logger->emit(AssertProofRule{}, c, ProofLevel::Top, link_hint);
                    });
                }
                else if (! literals_proof_time) {
                    emit_and_maybe_track_order_link(id, *prev(this_gevar), v);
                }
                // Literals-mode proof-time linking is handled once, below.
            } //
        }
            .visit(id);
    }

    // Literals order-encoding-deletion mode: link this real variable's ge literal to its
    // immediate *live* neighbours (it was recorded live above). Linking to live
    // neighbours (rather than the gevars neighbours used by the blocks above) keeps the
    // chain valid even when neighbouring thresholds have been deleted by an earlier
    // backtrack. Only at proof time; model-time links are emitted by the blocks above.
    if (literals_proof_time)
        link_order_literal_to_live_neighbours(std::get<SimpleIntegerVariableID>(id), v);

    // If `id` is a view's proof-only var, eagerly pol-derive the
    // atom-level link to the corresponding X-atom so propagator inferences
    // that mix V-atoms (from view literals via simplify_literal) and X-atoms
    // (from search guesses or other propagator inferences) can UP across
    // them without needing to case-split through the bit-vector link
    // alone. Two pol lines per V-atom — one for each direction of the iff:
    //
    //   D1: ~v>=k OR x_cond >= 1   = (v>=k -> x_cond)
    //   D2: ~x_cond OR v>=k >= 1   = (x_cond -> v>=k)
    //
    // where x_cond = (X >= v-c) for s=+1 and x_cond = ~(X >= c-v+1) for s=-1.
    //
    // Both directions sum three constraints whose BinEnc terms cancel
    // exactly, leaving an at-least-one over the two atom literals after
    // saturation. The choice of fwd vs rev for the X-atom Def flips with s:
    //   s=+1: D1 uses Def(v) fwd + LE + Def(x) rev; D2 uses rev + GE + fwd.
    //   s=-1: D1 uses Def(v) fwd + LE + Def(x) fwd; D2 uses rev + GE + rev.
    //
    // Both lines queued via emit_proof_line_now_or_at_start so they land at
    // the top of the proof, alongside the standard order-encoding chain
    // links, rather than as extra OPB axioms.
    if (_imp->assertion_level > AssertionLevel::Links)
        return;

    if (auto pid_ptr = std::get_if<ProofOnlySimpleIntegerVariableID>(&id)) {
        auto view_it = _imp->view_proof_only_to_view.find(*pid_ptr);
        if (view_it != _imp->view_proof_only_to_view.end()) {
            const auto & view = view_it->second;
            Integer x_threshold = view.negate_first ? view.then_add - v + 1_i : v - view.then_add;
            need_gevar(view.actual_variable, x_threshold);
            if (_imp->assertion_level == AssertionLevel::Links) {
                // Definitions are omitted at this level, instead assert the view links that the
                // pol lines below would derive.
                auto v_atom = (*pid_ptr >= v);
                auto x_atom = (view.actual_variable >= x_threshold);
                auto x_cond = view.negate_first ? ! x_atom : x_atom;
                auto d1 = WPBSum{} + 1_i * ! v_atom + 1_i * x_cond >= 1_i;
                auto d2 = WPBSum{} + 1_i * ! x_cond + 1_i * v_atom >= 1_i;
                emit_proof_line_now_or_at_start([d1, d2, link_hint](ProofLogger * const logger) {
                    logger->emit(AssertProofRule{}, d1, ProofLevel::Top, link_hint);
                    logger->emit(AssertProofRule{}, d2, ProofLevel::Top, link_hint);
                });
                return;
            }

            auto v_defs = _imp->atoms_for(id).ge_defs.at(v.raw_value);
            auto x_defs = _imp->atoms_for(SimpleOrProofOnlyIntegerVariableID{view.actual_variable}).ge_defs.at(x_threshold.raw_value);
            auto link = _imp->view_link_ids.at(*pid_ptr);
            auto * v_fwd_line = std::get_if<ProofLine>(&v_defs.first);
            auto * v_rev_line = std::get_if<ProofLine>(&v_defs.second);
            auto * x_fwd_line = std::get_if<ProofLine>(&x_defs.first);
            auto * x_rev_line = std::get_if<ProofLine>(&x_defs.second);
            if (v_fwd_line && v_rev_line && x_fwd_line && x_rev_line) {
                bool neg = view.negate_first;
                ProofLine d1_x = neg ? *x_fwd_line : *x_rev_line;
                ProofLine d2_x = neg ? *x_rev_line : *x_fwd_line;
                // Shared PolBuilders (not rendered strings) so the line refs emit
                // as relative indices -- see make_pol_chain_line above for why.
                auto b1 = make_shared<PolBuilder>();
                b1->add(*v_fwd_line).add(link.first).add(d1_x).saturate();
                auto b2 = make_shared<PolBuilder>();
                b2->add(*v_rev_line).add(link.second).add(d2_x).saturate();
                emit_proof_line_now_or_at_start([b1, b2](ProofLogger * const logger) {
                    b1->emit(*logger, ProofLevel::Top);
                    b2->emit(*logger, ProofLevel::Top);
                });
            }
        }
    }

    // Reverse direction: if `id` is a bare underlying variable that has
    // views registered over it, recursively trigger the matching V_ge
    // atom for each view. The V-side need_gevar then runs the link
    // emission above. Without this, an X atom introduced before any V
    // atom of the same value would never get a link in F.
    if (auto sid_ptr = std::get_if<SimpleIntegerVariableID>(&id)) {
        if (auto it = _imp->views_of_variable.find(*sid_ptr); it != _imp->views_of_variable.end()) {
            auto views_copy = it->second;
            for (const auto & view_pid : views_copy) {
                const auto & view = _imp->view_proof_only_to_view.at(view_pid);
                Integer v_value = view.negate_first ? view.then_add - v + 1_i : v + view.then_add;
                need_gevar(view_pid, v_value);
            }
        }
    }
}

auto NamesAndIDsTracker::make_pol_chain_line(IntegerVariableCondition cond1, IntegerVariableCondition cond2) -> shared_ptr<PolBuilder>
{
    // Returns a shared PolBuilder (rather than a rendered string) so the line
    // references resolve to *relative* indices at emit time -- a workflow-2
    // requirement: under cake_pb_cp the OPB has a different constraint count, so
    // an absolute `pol 50 ...` would point at the wrong (or deleted) constraint.
    // emit_proof_line_now_or_at_start may defer the lambda to proof start, hence
    // the shared_ptr capture (the std::function it stores must stay copyable).
    auto b = make_shared<PolBuilder>();
    b->add_for_literal(*this, ! cond1).add_for_literal(*this, ! cond2).saturate();
    return b;
}

auto NamesAndIDsTracker::emit_and_maybe_track_order_link(const SimpleIntegerVariableID & id, Integer lo, Integer hi) -> void
{
    // During proof logging with the mode on, land the link at Current so a backtrack
    // deletes it; otherwise (mode off, or model building where the logger is not yet
    // attached and the emission is deferred to proof start) keep it at Top exactly as
    // before -- hence the _imp->logger guard.
    auto level = (_imp->order_link_deletion_mode == OrderEncodingDeletion::Links && _imp->logger) ? ProofLevel::Current : ProofLevel::Top;

    // The adjacent-threshold chain link is the clause (id >= lo) OR ~(id >= hi),
    // i.e. ge(hi) -> ge(lo); make_pol_chain_line derives it from the two resident
    // (Top) ge definitions, so it stays sound to (re-)emit at any level even after
    // the previous copy was deleted. Suppress fast-path re-emission while the pol is
    // built (it re-enters need_gevar for lo and hi) so it does not recurse back here.
    auto saved = _imp->building_order_link;
    _imp->building_order_link = true;
    auto pol = make_pol_chain_line(id >= lo, ! (id >= hi));
    _imp->building_order_link = saved;

    emit_proof_line_now_or_at_start([pol, level](ProofLogger * const logger) { pol->emit(*logger, level); });

    // Record the link as live, tagged with the level it was emitted at, so the fast
    // path can tell it is present and forget_order_links_at_level can drop it when
    // that level is forgotten. Top links are tagged 0 (never forgotten) so the fast
    // path does not needlessly re-emit a permanent link. Also index it under its level
    // so forget is O(links-at-level). Only track when the mode is on, to keep the
    // mode-off path a pure no-op.
    if (_imp->order_link_deletion_mode == OrderEncodingDeletion::Links) {
        auto tag = (level == ProofLevel::Current) ? _imp->logger->proof_level() : 0;
        _imp->live_order_links[id][pair{lo, hi}] = tag;
        _imp->order_links_by_level[tag].emplace_back(id, pair{lo, hi});
    }
}

auto NamesAndIDsTracker::ensure_order_chain_connected(const SimpleIntegerVariableID & id) -> void
{
    auto gevars_it = _imp->gevar_values.find(SimpleOrProofOnlyIntegerVariableID{id});
    if (gevars_it == _imp->gevar_values.end())
        return;
    const auto & gevars = gevars_it->second;
    if (gevars.size() < 2)
        return;

    // Reconnect the variable's entire order chain: every consecutive threshold pair
    // whose link is not currently live gets re-emitted, so a RUP that needs multi-hop
    // order propagation across this variable has the full chain available (matching
    // what the baseline keeps permanently resident). Emission only fires for
    // genuinely-missing links, so this stays cheap once the chain is connected.
    // gevar_values is not modified here (the atoms already exist), and inserting
    // into live_order_links never invalidates `links`, so both references stay valid
    // across the emissions below.
    auto & links = _imp->live_order_links[id];
    for (auto lower = gevars.begin(), higher = next(lower); higher != gevars.end(); ++lower, ++higher)
        if (! links.contains(pair{*lower, *higher}))
            emit_and_maybe_track_order_link(id, *lower, *higher);
}

auto NamesAndIDsTracker::forget_order_links_at_level(int level) -> void
{
    if (_imp->order_link_deletion_mode == OrderEncodingDeletion::Literals) {
        forget_order_literals_at_level(level);
        return;
    }

    if (_imp->order_link_deletion_mode == OrderEncodingDeletion::None)
        return;

    // Links mode: walk only the links recorded at this level (their `del`s are emitted
    // by ProofLogger::forget_proof_level's own loop). Drop each from the live set so a
    // later need_gevar re-emits it if needed, then clear the level's bucket (keeping
    // its capacity for when the level is re-entered). Bucket 0 (Top) is never passed
    // here.
    auto bucket_it = _imp->order_links_by_level.find(level);
    if (bucket_it == _imp->order_links_by_level.end())
        return;
    for (const auto & [id, lohi] : bucket_it->second)
        if (auto links_it = _imp->live_order_links.find(id); links_it != _imp->live_order_links.end())
            links_it->second.erase(lohi);
    bucket_it->second.clear();
}

auto NamesAndIDsTracker::record_live_order_literal(const SimpleIntegerVariableID & id, Integer v, bool top) -> void
{
    // Tag a Top literal (model-time atom or boundary) as level 0 -- permanent, never
    // forgotten, so it is not indexed for deletion. A search-introduced interior
    // literal is tagged with the active proof level and indexed under it, so a later
    // forget of that level deletes and stitches it.
    int level = top ? 0 : _imp->logger->proof_level();
    _imp->live_order_literals[id][v] = level;
    if (! top)
        _imp->order_literals_by_level[level].emplace_back(id, v);
}

auto NamesAndIDsTracker::link_order_literal_to_live_neighbours(const SimpleIntegerVariableID & id, Integer v) -> void
{
    // Emit the two chain links joining v to its immediate live neighbours. A link between
    // two RESIDENT (level 0) literals lands at Top so it survives every backtrack, keeping
    // a fully-resident chain (an aux magnitude's or a view underlying's, whose every ge is
    // kept at Top) intact -- a Current-level link there would be del'd on the next forget
    // with no re-stitch (forget_order_literals_at_level only stitches around deleted, not
    // resident, thresholds), orphaning the resident definition. Every other link -- an
    // ordinary search-introduced literal (v is the deepest live threshold, its level the
    // current proof level) and an isolated boundary literal linked to a deletable interior
    // neighbour alike -- lands at Current, exactly as before this change (so a mode-on
    // proof of an instance with no resident interior chain, e.g. an eq-free bound-branching
    // one, is byte-for-byte unchanged). v must already be present in live_order_literals
    // (recorded by the caller before this call), so its neighbours are prev(v) and next(v)
    // in the live map. building_order_link suppresses re-introduction while
    // make_pol_chain_line re-enters need_gevar for v and each neighbour (all resident/live).
    auto & live = _imp->live_order_literals[id];
    auto it = live.find(v);
    if (it == live.end())
        return;
    int v_level = it->second;
    auto current = _imp->logger->proof_level();

    // Top only when BOTH endpoints are resident; otherwise Current (the pre-change level).
    // lo < hi is the threshold pair the link is over (for the stats dup-Top check).
    auto emit_link = [&](const shared_ptr<PolBuilder> & pol, int neighbour_level, Integer lo, Integer hi) {
        int landed;
        if (v_level == 0 && neighbour_level == 0 && current != 0) {
            _imp->logger->enter_proof_level(0);
            pol->emit(*_imp->logger, ProofLevel::Current);
            _imp->logger->enter_proof_level(current);
            landed = 0;
        }
        else {
            pol->emit(*_imp->logger, ProofLevel::Current);
            landed = current;
        }
        if (_imp->collect_order_encoding_stats)
            stats_note_stitch_emitted(id, lo, hi, landed, /*forget_path=*/false);
    };

    auto saved = _imp->building_order_link;
    _imp->building_order_link = true;
    if (auto higher = next(it); higher != live.end()) {
        // ge(hi) -> ge(v): clause ge(v) OR ~ge(hi).
        auto pol = make_pol_chain_line(id >= v, ! (id >= higher->first));
        emit_link(pol, higher->second, v, higher->first);
    }
    if (it != live.begin()) {
        auto lower = prev(it);
        // ge(v) -> ge(lo): clause ge(lo) OR ~ge(v).
        auto pol = make_pol_chain_line(id >= lower->first, ! (id >= v));
        emit_link(pol, lower->second, lower->first, v);
    }
    _imp->building_order_link = saved;
}

auto NamesAndIDsTracker::reintroduce_order_literal(const SimpleIntegerVariableID & id, Integer v) -> void
{
    // The atom already exists but its Current-level definition was deleted on an
    // earlier backtrack, and the search has genuinely re-touched it. Re-emit the
    // reification def at Current, overwrite the stale def lines, re-record as live at
    // Current, then re-link to live neighbours. Only interior literals reach here
    // (level-0 literals never leave the live set), and in practice only *unpinned*
    // ones: a ge pinned by a surviving Top constraint -- in particular a ge named by an
    // eq atom's permanent (Top) definition -- is hoisted to Top when that atom is
    // created and is thereafter never deleted, so it never reaches reintroduction. That
    // is why the fresh `red` VeriPB accepts here never collides with a pin against its
    // falsify-witness: pinned literals are hoisted, not reintroduced. Only genuinely
    // re-touched unpinned interior literals reintroduce, and they verify.
    SimpleOrProofOnlyIntegerVariableID key{id};
    // The re-emitted `red` reifies against `id >= v` itself, so rendering it resolves
    // that very condition through xliteral_for_ensuring -- which, under this mode, calls
    // back into need_gevar to re-introduce a non-live literal. v is not live again until
    // record_live_order_literal below, so without this guard the call recurses forever.
    // building_order_link is the existing "we are emitting order-encoding machinery, do
    // not recursively re-introduce" flag, used the same way by emit_order_stitch.
    auto saved_building = _imp->building_order_link;
    _imp->building_order_link = true;
    auto def_lines = _imp->logger->emit_red_proof_lines_reifying(WPBSum{} + (1_i * id) >= v, id >= v, ProofLevel::Current);
    _imp->building_order_link = saved_building;
    auto & entry = _imp->atoms_for(key).ge_defs.at(v.raw_value);
    entry.first = def_lines.first;
    entry.second = def_lines.second;

    if (_imp->collect_order_encoding_stats)
        ++_imp->stats_reintroductions;

    record_live_order_literal(id, v, /*top=*/false);
    link_order_literal_to_live_neighbours(id, v);
}

auto NamesAndIDsTracker::emit_order_stitch(const SimpleIntegerVariableID & id, Integer lo, Integer hi, int at_level, int restore_level) -> void
{
    // Derive the skip link ge(hi) -> ge(lo) (clause ge(lo) OR ~ge(hi)) from the two
    // survivors' resident defs, exactly as an adjacent chain link -- it is sound for a
    // skip (lo, hi more than one threshold apart) identically. Record it at at_level =
    // max(level(lo), level(hi)) so it is deleted together with the deeper of its two
    // endpoints (levels are forgotten deepest-first). building_order_link suppresses
    // re-introduction while make_pol_chain_line re-enters need_gevar for lo and hi.
    auto saved = _imp->building_order_link;
    _imp->building_order_link = true;
    auto pol = make_pol_chain_line(id >= lo, ! (id >= hi));
    _imp->building_order_link = saved;

    _imp->logger->enter_proof_level(at_level);
    pol->emit(*_imp->logger, ProofLevel::Current);
    _imp->logger->enter_proof_level(restore_level);

    if (_imp->collect_order_encoding_stats)
        stats_note_stitch_emitted(id, lo, hi, at_level, /*forget_path=*/true);
}

auto NamesAndIDsTracker::forget_order_literals_at_level(int level) -> void
{
    // Called from forget_order_links_at_level, itself called by
    // ProofLogger::forget_proof_level after it has emitted the `del`s for every line
    // recorded at `level` (which include the deleted literals' def and link lines).
    auto bucket_it = _imp->order_literals_by_level.find(level);
    if (bucket_it == _imp->order_literals_by_level.end())
        return;

    // Group the thresholds deleted at this level by variable.
    map<SimpleIntegerVariableID, vector<Integer>> deleted_by_var;
    for (const auto & [id, v] : bucket_it->second)
        deleted_by_var[id].push_back(v);

    auto restore_level = _imp->logger->proof_level();
    for (auto & [id, dvals] : deleted_by_var) {
        auto live_it = _imp->live_order_literals.find(id);
        if (live_it == _imp->live_order_literals.end())
            continue;
        auto & live = live_it->second;

        // Walk the live thresholds in order. For each maximal contiguous run of
        // level-`level` thresholds, stitch the nearest surviving neighbour below (lo)
        // to the nearest above (hi) -- both necessarily at a level < `level`, since
        // deeper levels are forgotten first -- so the chain stays complete over the
        // survivors. A run at a chain end (no survivor on one side) gets no stitch
        // there. The stitch lands at max(level(lo), level(hi)).
        for (auto it = live.begin(); it != live.end();) {
            if (it->second != level) {
                ++it;
                continue;
            }
            optional<Integer> lo, hi;
            int lo_level = 0, hi_level = 0;
            if (it != live.begin()) {
                auto p = prev(it);
                lo = p->first;
                lo_level = p->second;
            }
            auto run_end = it;
            while (run_end != live.end() && run_end->second == level)
                ++run_end;
            if (run_end != live.end()) {
                hi = run_end->first;
                hi_level = run_end->second;
            }
            if (lo && hi)
                emit_order_stitch(id, *lo, *hi, max(lo_level, hi_level), restore_level);
            it = run_end;
        }

        // The deleted literals' def+link lines were del'd by forget_proof_level's own
        // loop; drop the thresholds from the live set so a later need_gevar
        // re-introduces them.
        if (_imp->collect_order_encoding_stats)
            _imp->stats_deletes += static_cast<long long>(dvals.size());
        for (auto v : dvals)
            live.erase(v);
        if (live.empty())
            _imp->live_order_literals.erase(live_it);
    }

    _imp->order_literals_by_level.erase(bucket_it);
}

auto NamesAndIDsTracker::stitch_hoisted_order_literal(const SimpleIntegerVariableID & id, Integer v, int target_level, bool immediate_neighbours)
    -> void
{
    auto & live = _imp->live_order_literals[id];
    auto it = live.find(v);
    if (it == live.end())
        return;

    // Choose the neighbours to re-link v to. In the immediate-neighbours policy the
    // *nearest* live neighbour on each side is taken, at whatever level, and the link is
    // recorded at max(target_level, neighbour_level). Otherwise (the backtrack/nogood
    // hoist, whose caller is about to forget every deeper level) the nearest neighbour
    // whose level is <= target_level is taken -- the survivor v will end up adjacent to
    // -- and the link is recorded at target_level. See the header for why immediate
    // neighbours are needed when the deeper levels are NOT being forgotten.
    optional<Integer> lo, hi;
    int lo_level = target_level, hi_level = target_level;
    for (auto j = it; j != live.begin();) {
        --j;
        if (immediate_neighbours || j->second <= target_level) {
            lo = j->first;
            lo_level = j->second;
            break;
        }
    }
    for (auto j = next(it); j != live.end(); ++j)
        if (immediate_neighbours || j->second <= target_level) {
            hi = j->first;
            hi_level = j->second;
            break;
        }

    // Emit each link at max(target_level, neighbour_level): enter that level, emit at
    // Current, restore. building_order_link suppresses re-introduction while
    // make_pol_chain_line re-enters need_gevar for v and each neighbour (all resident
    // and live).
    auto restore_level = _imp->logger->proof_level();
    auto saved = _imp->building_order_link;
    _imp->building_order_link = true;
    if (lo) {
        // ge(lo) -> nothing; the link is ge(lo) OR ~ge(v), i.e. ge(v) -> ge(lo).
        auto pol = make_pol_chain_line(id >= *lo, ! (id >= v));
        auto landed = max(target_level, lo_level);
        _imp->logger->enter_proof_level(landed);
        pol->emit(*_imp->logger, ProofLevel::Current);
        if (_imp->collect_order_encoding_stats)
            stats_note_stitch_emitted(id, *lo, v, landed, /*forget_path=*/false);
    }
    if (hi) {
        // ge(v) OR ~ge(hi), i.e. ge(hi) -> ge(v).
        auto pol = make_pol_chain_line(id >= v, ! (id >= *hi));
        auto landed = max(target_level, hi_level);
        _imp->logger->enter_proof_level(landed);
        pol->emit(*_imp->logger, ProofLevel::Current);
        if (_imp->collect_order_encoding_stats)
            stats_note_stitch_emitted(id, v, *hi, landed, /*forget_path=*/false);
    }
    _imp->logger->enter_proof_level(restore_level);
    _imp->building_order_link = saved;
}

auto NamesAndIDsTracker::hoist_order_literal_to_level(const SimpleIntegerVariableID & id, Integer v, int target_level, bool immediate_neighbours,
    optional<OrderEncodingResidencyCause> stats_cause) -> void
{
    if (_imp->order_link_deletion_mode != OrderEncodingDeletion::Literals)
        throw ProofError{"hoist_order_literal_to_level requires OrderEncodingDeletion::Literals"};
    if (! _imp->logger)
        throw ProofError{"hoist_order_literal_to_level requires the logger to be attached"};

    auto live_it = _imp->live_order_literals.find(id);
    if (live_it == _imp->live_order_literals.end())
        throw ProofError{"hoist of an order literal for an untracked variable"};
    auto lvl_it = live_it->second.find(v);
    if (lvl_it == live_it->second.end())
        throw ProofError{"hoist of a non-live order literal"};

    int cur_level = lvl_it->second;
    if (cur_level == target_level)
        return;

    // Stats: an actual hoist is about to happen. Count it by cause, and -- for a hoist
    // that lands the def at Top -- attribute the literal's Top residency to this cause
    // (first-cause-wins; GuessHoist targets a positive level and is never a Top cause).
    if (_imp->collect_order_encoding_stats && stats_cause) {
        ++_imp->stats_hoist_events[*stats_cause];
        if (target_level == 0 && *stats_cause != OrderEncodingResidencyCause::GuessHoist) {
            auto & slot = _imp->stats_ge_top_cause[id][v];
            if (! slot)
                slot = stats_cause;
        }
    }

    // Part 1: relocate the two reification proof lines of ge(v)'s definition from
    // their current (deep) level bucket to target_level's bucket. Pure bookkeeping
    // -- emits nothing -- so there is no re-asserted witness to collide with a pin.
    SimpleOrProofOnlyIntegerVariableID key{id};
    auto & entry = _imp->atoms_for(key).ge_defs.at(v.raw_value);
    vector<ProofLine> def_lines;
    if (auto p = std::get_if<ProofLine>(&entry.first))
        def_lines.push_back(*p);
    if (auto p = std::get_if<ProofLine>(&entry.second))
        def_lines.push_back(*p);
    _imp->logger->move_proof_lines_to_level(def_lines, cur_level, target_level);

    // Retag v in the tracker's live/level bookkeeping: drop it from its old level's
    // deletion index and, unless it is now permanent at Top, index it under the
    // target level so a later forget of that level deletes and stitches it.
    if (cur_level != 0) {
        auto & old_bucket = _imp->order_literals_by_level[cur_level];
        std::erase_if(old_bucket, [&](const pair<SimpleIntegerVariableID, Integer> & e) { return e.first.index == id.index && e.second == v; });
    }
    lvl_it->second = target_level;
    if (target_level != 0)
        _imp->order_literals_by_level[target_level].emplace_back(id, v);

    // Part 2: re-stitch v into the target level's chain (see above).
    stitch_hoisted_order_literal(id, v, target_level, immediate_neighbours);
}

auto NamesAndIDsTracker::hoist_order_literal_to_top(const SimpleIntegerVariableID & id, Integer v, optional<OrderEncodingResidencyCause> stats_cause)
    -> void
{
    hoist_order_literal_to_level(id, v, 0, /*immediate_neighbours=*/false, stats_cause);
}

auto NamesAndIDsTracker::hoist_order_literal_to_top_if_live(
    const SimpleIntegerVariableID & id, Integer v, optional<OrderEncodingResidencyCause> stats_cause) -> void
{
    // A permanent (Top) eq definition eq(v) <=> ge(v) & ~ge(v+1) names ge(v) and
    // ge(v+1); this makes those two ge defs resident at Top so the eq def -- and any
    // later solx / backtrack clause over the eq atom -- never names a ge whose
    // Current-level def a backtrack forget deleted. Only fires for a threshold that is
    // actually a live, deletable order literal for id: a boundary/model-time literal is
    // already at Top (level 0), and a threshold the eq def does not name (the ge absent
    // from the compact-encoding form) is simply not live here, so both are skipped.
    auto live_it = _imp->live_order_literals.find(id);
    if (live_it == _imp->live_order_literals.end())
        return;
    auto lvl_it = live_it->second.find(v);
    if (lvl_it == live_it->second.end() || lvl_it->second == 0)
        return;
    // immediate_neighbours: this hoist happens mid-search (an eq/interval def naming
    // this ge), NOT before a forget of the deeper levels, so interior survivors between
    // v and its nearest Top neighbour must stay chained -- link to the immediate live
    // neighbours, not only the Top ones.
    hoist_order_literal_to_level(id, v, 0, /*immediate_neighbours=*/true, stats_cause);
}

auto NamesAndIDsTracker::order_literal_aliased_to_bit(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> bool
{
    // Aliasing (proof_model.cc set_up_direct_only_variable_encoding) only ever happens
    // for a single-bit DirectOnly {0,1} variable, so a >1-bit variable is excluded up
    // front (cheap). For a one-bit variable, the ge is aliased iff id >= v's xliteral
    // *is* that bit's xliteral (a Bits-encoded {0,1} variable instead mints a distinct
    // ge1 atom, whose xliteral differs, so it returns false and stays reintroducible).
    if (! has_bit_representation(id) || num_bits(id) != 1_i)
        return false;
    auto cond = _imp->find_condition(id >= v);
    return cond && *cond == get_bit(id, 0_i).second;
}

auto NamesAndIDsTracker::hoist_ges_named_by_top_atom(
    SimpleOrProofOnlyIntegerVariableID id, Integer lower_ge, Integer upper_ge, optional<OrderEncodingResidencyCause> stats_cause) -> void
{
    // Same guard the ge-def deletion in need_gevar uses: only proof-time, real-variable,
    // assertions-off Literals mode tracks deletable ge defs at all.
    if (_imp->order_link_deletion_mode != OrderEncodingDeletion::Literals || ! _imp->logger || _imp->assertion_level != AssertionLevel::Off)
        return;
    if (auto sid_ptr = std::get_if<SimpleIntegerVariableID>(&id)) {
        hoist_order_literal_to_top_if_live(*sid_ptr, lower_ge, stats_cause);
        hoist_order_literal_to_top_if_live(*sid_ptr, upper_ge, stats_cause);
    }
}

auto NamesAndIDsTracker::hoist_live_order_literals_toward_level(
    const std::vector<Literal> & lits, int target_level, optional<OrderEncodingResidencyCause> stats_cause) -> void
{
    // Only the Literals mode has anything to hoist; other modes keep the whole
    // encoding resident at Top, and with no logger there is nothing emitted yet.
    if (_imp->order_link_deletion_mode != OrderEncodingDeletion::Literals || ! _imp->logger)
        return;

    for (const auto & lit : lits) {
        // Only a plain integer-variable condition can name an order literal.
        const auto * cond = std::get_if<IntegerVariableCondition>(&lit);
        if (! cond)
            continue;
        // ge(v) is named by `X >= v` (GreaterEqual, threshold v) and by `X < v`
        // (Less, threshold v -- the negated ge atom). `X <= v` / `X > v` are lowered
        // to Less(v+1) / GreaterEqual(v+1), so their threshold is likewise the value.
        // Any other operator (eq, range, ...) is not an order literal here.
        if (cond->op != VariableConditionOperator::GreaterEqual && cond->op != VariableConditionOperator::Less)
            continue;
        // Views and constants are not what the Literals mode tracks (only real
        // SimpleIntegerVariableIDs carry deletable order-literal definitions).
        const auto * sid = std::get_if<SimpleIntegerVariableID>(&cond->var);
        if (! sid)
            continue;

        // Hoist only a currently-live literal whose definition is deeper than the
        // target: a boundary/model-time literal (level 0) or one already at or above
        // the target needs nothing, and hoisting never sinks a definition deeper.
        auto live_it = _imp->live_order_literals.find(*sid);
        if (live_it == _imp->live_order_literals.end())
            continue;
        auto lvl_it = live_it->second.find(cond->value);
        if (lvl_it == live_it->second.end())
            continue;
        if (lvl_it->second > target_level)
            hoist_order_literal_to_level(*sid, cond->value, target_level, /*immediate_neighbours=*/false, stats_cause);
    }
}

auto NamesAndIDsTracker::stats_note_ge_recorded(const SimpleIntegerVariableID & id, Integer v, optional<OrderEncodingResidencyCause> born_cause)
    -> void
{
    // Register v as seen (inserts a nullopt entry on first sight; a re-record of an
    // already-seen literal leaves the existing entry alone). If born Top, attribute the
    // residency -- first-cause-wins, so a cause is only ever set when none is present.
    auto & slot = _imp->stats_ge_top_cause[id][v];
    if (born_cause && ! slot)
        slot = born_cause;
}

auto NamesAndIDsTracker::stats_note_stitch_emitted(const SimpleIntegerVariableID & id, Integer lo, Integer hi, int at_level, bool forget_path) -> void
{
    if (forget_path)
        ++_imp->stats_stitches;
    // A chain-link/stitch clause landing at Top over a pair already Top-linked re-adds a
    // constraint that is still resident: the known duplicate-Top-stitch inefficiency.
    if (at_level == 0 && ! _imp->stats_top_stitch_pairs[id].emplace(lo, hi).second)
        ++_imp->stats_dup_top_stitches;
}

auto NamesAndIDsTracker::dump_order_encoding_stats() const -> void
{
    if (! _imp->collect_order_encoding_stats)
        return;

    using Cause = OrderEncodingResidencyCause;

    // Sweep the per-literal cause map: distinct real-var ge atoms seen over the proof,
    // and the Top-resident count broken down by first-cause.
    long long seen = 0, top_resident = 0;
    map<Cause, long long> by_cause;
    for (const auto & [id, vs] : _imp->stats_ge_top_cause)
        for (const auto & [v, cause] : vs) {
            ++seen;
            if (cause) {
                ++top_resident;
                ++by_cause[*cause];
            }
        }

    // Live snapshot at proof end (a Top literal is never deleted, so live-at-Top equals
    // top_resident; a positive-level literal is a still-open deletable one).
    long long live_top = 0, live_positive = 0;
    for (const auto & [id, vs] : _imp->live_order_literals)
        for (const auto & [v, lvl] : vs)
            ((lvl == 0) ? live_top : live_positive) += 1;
    long long net_deleted = seen - live_top - live_positive;

    // Per-variable classification: view/aux structurally, then ordinary variables by
    // whether any of their ges are hoist-pinned (eq/invar/nogood/soli) vs all deletable.
    long long n_view = 0, n_aux = 0, n_mixed = 0, n_deletable = 0;
    for (const auto & [id, vs] : _imp->stats_ge_top_cause) {
        if (_imp->views_of_variable.contains(id)) {
            ++n_view;
            continue;
        }
        if (_imp->order_encoding_stays_resident.contains(SimpleOrProofOnlyIntegerVariableID{id})) {
            ++n_aux;
            continue;
        }
        bool any_hoist_pin = false;
        for (const auto & [v, cause] : vs)
            if (cause && (*cause == Cause::EqHoist || *cause == Cause::InvarHoist || *cause == Cause::NogoodHoist || *cause == Cause::SoliHoist)) {
                any_hoist_pin = true;
                break;
            }
        ((any_hoist_pin) ? n_mixed : n_deletable) += 1;
    }

    auto get = [](const map<Cause, long long> & m, Cause k) -> long long {
        auto it = m.find(k);
        return it == m.end() ? 0 : it->second;
    };
    auto pct = [&](long long x) -> double { return top_resident > 0 ? 100.0 * static_cast<double>(x) / static_cast<double>(top_resident) : 0.0; };

    long long view_pin = get(by_cause, Cause::ViewPin), aux_pin = get(by_cause, Cause::AuxPin);
    long long eq_h = get(by_cause, Cause::EqHoist), invar_h = get(by_cause, Cause::InvarHoist);
    long long nogood_h = get(by_cause, Cause::NogoodHoist), soli_h = get(by_cause, Cause::SoliHoist);
    long long boundary = get(by_cause, Cause::Boundary), model_time = get(by_cause, Cause::ModelTime);
    long long would_free = view_pin + aux_pin;
    long long would_not_free = eq_h + invar_h + nogood_h + soli_h;
    long long structural = boundary + model_time;

    stringstream o;
    auto emit = [&](const string & s) { o << "%% oed-stats: " << s << "\n"; };
    emit("order-encoding-deletion pin apportionment (mode=Literals)");
    emit(format("real-var ge atoms seen (proof-time): {}", seen));
    emit(format("  currently live at Top: {}", live_top));
    emit(format("  currently live at positive levels: {}", live_positive));
    emit(format("  net deleted: {}", net_deleted));
    emit(format("Top-resident breakdown by cause (of {} Top-resident):", top_resident));
    emit(format("  step-3-WOULD-free (view_pin + aux_pin): {} ({:.1f}%)", would_free, pct(would_free)));
    emit(format("      view_pin:     {} ({:.1f}%)", view_pin, pct(view_pin)));
    emit(format("      aux_pin:      {} ({:.1f}%)", aux_pin, pct(aux_pin)));
    emit(format("  step-3-would-NOT-free (eq + invar + nogood + soli hoist): {} ({:.1f}%)", would_not_free, pct(would_not_free)));
    emit(format("      eq_hoist:     {} ({:.1f}%)", eq_h, pct(eq_h)));
    emit(format("      invar_hoist:  {} ({:.1f}%)", invar_h, pct(invar_h)));
    emit(format("      nogood_hoist: {} ({:.1f}%)", nogood_h, pct(nogood_h)));
    emit(format("      soli_hoist:   {} ({:.1f}%)", soli_h, pct(soli_h)));
    emit(format("  structural (boundary + model_time): {} ({:.1f}%)", structural, pct(structural)));
    emit(format("      boundary:     {} ({:.1f}%)", boundary, pct(boundary)));
    emit(format("      model_time:   {} ({:.1f}%)", model_time, pct(model_time)));
    emit("events:");
    emit(format("  deletes: {}", _imp->stats_deletes));
    emit(format("  stitches (forget-path): {}", _imp->stats_stitches));
    emit(format("  reintroductions: {}", _imp->stats_reintroductions));
    emit(format("  duplicate-Top-stitches: {}", _imp->stats_dup_top_stitches));
    emit(format("  hoists: eq={} invar={} nogood={} soli={} guess={}", get(_imp->stats_hoist_events, Cause::EqHoist),
        get(_imp->stats_hoist_events, Cause::InvarHoist), get(_imp->stats_hoist_events, Cause::NogoodHoist),
        get(_imp->stats_hoist_events, Cause::SoliHoist), get(_imp->stats_hoist_events, Cause::GuessHoist)));
    emit("variables by class:");
    emit(format("  fully-resident-by-view: {}", n_view));
    emit(format("  fully-resident-by-aux:  {}", n_aux));
    emit(format("  mixed (some eq/invar/nogood/soli-hoisted resident): {}", n_mixed));
    emit(format("  fully-deletable (no hoist pins): {}", n_deletable));

    print(stderr, "{}", o.str());
}

auto NamesAndIDsTracker::link_immediate_containment(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> void
{
    if (! _imp->logger || _imp->logger->get_assertion_level() > AssertionLevel::Links) // Should be unreachable at AssertionLevel::Links anyway
        return;

    auto tree_it = _imp->containment_trees.find(id);
    if (tree_it == _imp->containment_trees.end())
        return;
    const auto & tree = tree_it->second;

    // A child -> parent containment edge (~child OR parent) as a rup line. A width-1
    // literal is its eq atom; nothing fits strictly inside a width-1 literal, so a
    // parent is always a range.
    auto emit_edge = [&](Integer clo, Integer chi, Integer plo, Integer phi) {
        visit(
            [&](const auto & id) {
                WPBSum edge;
                if (clo == chi)
                    edge += 1_i * (id != clo);
                else
                    edge += 1_i * not_in_range(id, clo, chi);
                edge += 1_i * in_range(id, plo, phi);
                _imp->logger->emit_rup_proof_line(move(edge) >= 1_i, ProofLevel::Top);
            },
            id);
    };

    // self -> minimal containers: walking candidates by decreasing lo (ties:
    // increasing hi), a candidate is minimal exactly when its hi is strictly below
    // every hi seen so far, since everything seen so far has a lo at least as big.
    vector<pair<Integer, Integer>> found;
    tree.for_each_containing(lo, hi, [&](Integer c, Integer d) {
        if (c != lo || d != hi)
            found.emplace_back(c, d);
    });
    sort(found, [](const pair<Integer, Integer> & x, const pair<Integer, Integer> & y) {
        return x.first == y.first ? x.second < y.second : x.first > y.first;
    });
    optional<Integer> least_hi;
    for (const auto & [c, d] : found)
        if (! least_hi || d < *least_hi) {
            emit_edge(lo, hi, c, d);
            least_hi = d;
        }

    // maximal contained literals -> self, by the mirrored argument.
    if (lo != hi) {
        found.clear();
        tree.for_each_contained_in(lo, hi, [&](Integer c, Integer d) {
            if (c != lo || d != hi)
                found.emplace_back(c, d);
        });
        sort(found, [](const pair<Integer, Integer> & x, const pair<Integer, Integer> & y) {
            return x.first == y.first ? x.second > y.second : x.first < y.first;
        });
        optional<Integer> greatest_hi;
        for (const auto & [c, d] : found)
            if (! greatest_hi || d > *greatest_hi) {
                emit_edge(c, d, lo, hi);
                greatest_hi = d;
            }
    }
}

auto NamesAndIDsTracker::define_plain_invar(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> void
{
    // Both order-encoding cuts; need_gevar threads them into the order chain, and
    // emits the bound-axiom units for any cut outside the definition bounds.
    need_gevar(id, lo);
    need_gevar(id, hi + 1_i);

    auto x = allocate_xliteral_meaning(id, lo, hi);
    _imp->store_condition(in_range(id, lo, hi), x);

    auto will_define = _imp->logger->get_assertion_level() <= AssertionLevel::Links;
    // Struggling to get clang-format to behave here...
    auto lines = will_define //
        ? visit(
              [&](const auto & id) {
                  return _imp->logger->emit_red_proof_lines_reifying(
                      WPBSum{} + (1_i * (id >= lo)) + (1_i * ! (id > hi)) >= 2_i, in_range(id, lo, hi), ProofLevel::Top);
              },
              id)
        : make_pair(ProofLine{}, ProofLine{});

    _imp->invars_that_exist[id].emplace(pair{lo, hi}, lines);

    // Literals order-encoding-deletion mode: this interval atom's definition was emitted
    // at ProofLevel::Top (permanent) above, and names ge(lo) and ge(hi+1) (id > hi is
    // id >= hi+1). Keep those ge defs resident at Top so a backtrack forget never
    // deletes a ge underneath this surviving Top atom -- otherwise a later covering /
    // solx / need_direct_encoding_for over this partition would name (or try to
    // pinned-re-introduce) a deleted ge, which VeriPB rejects.
    hoist_ges_named_by_top_atom(id, lo, hi + 1_i, OrderEncodingResidencyCause::InvarHoist);

    // No containment tree apparatus needed at higher assertion levels.
    if (_imp->logger->get_assertion_level() > AssertionLevel::Links)
        return;

    // Containment edges let a rejected literal propagate down to the literals a
    // conflict is written over; the order chain alone does not give this. The
    // variable's first range literal creates its containment tree, seeded with
    // the eq atoms that already exist.
    if (! _imp->containment_trees.contains(id)) {
        auto & tree = _imp->containment_trees[id];
        if (const auto * atoms = _imp->find_atoms(id))
            for (const auto & [v, _] : atoms->eq_defs)
                tree.insert(Integer{v}, Integer{v});
    }
    link_immediate_containment(id, lo, hi);
    _imp->containment_trees[id].insert(lo, hi);
}

auto NamesAndIDsTracker::append_cell_literal_to(WPBSum & sum, SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> void
{
    visit(
        [&](const auto & id) {
            if (lo == hi)
                sum += 1_i * (id == lo);
            else
                sum += 1_i * in_range(id, lo, hi);
        },
        id);
}

auto NamesAndIDsTracker::ensure_partition_cut(SimpleOrProofOnlyIntegerVariableID id, Integer p) -> void
{
    if (_imp->logger->get_assertion_level() > AssertionLevel::Links)
        return;

    auto & boundaries = _imp->interval_partitions.at(id);
    if (boundaries.contains(p))
        return;

    // p falls strictly inside the cell [a, b].
    auto above = boundaries.upper_bound(p);
    auto a = *prev(above), b = *above - 1_i;

    // Insert the boundary before defining the halves: a width-1 half goes through
    // need_direct_encoding_for, whose partition maintenance re-enters here and must
    // see both of its cuts already present (making the re-entry a no-op).
    boundaries.insert(p);

    auto define_cell = [&](Integer cell_lo, Integer cell_hi) {
        if (cell_lo == cell_hi)
            need_direct_encoding_for(id, cell_lo);
        else
            define_plain_invar(id, cell_lo, cell_hi);
    };
    define_cell(a, p - 1_i);
    define_cell(p, b);

    // The split covering: the split cell is no longer a leaf, so unit propagation
    // falsifies it through its two halves. Coverings compose across refinements, so
    // the split cell's appearances in earlier coverings are never revisited.
    WPBSum covering;
    visit([&](const auto & id) { covering += 1_i * not_in_range(id, a, b); }, id);
    append_cell_literal_to(covering, id, a, p - 1_i);
    append_cell_literal_to(covering, id, p, b);
    _imp->logger->emit_rup_proof_line(move(covering) >= 1_i, ProofLevel::Top);
}

auto NamesAndIDsTracker::init_interval_partition(SimpleOrProofOnlyIntegerVariableID id, Integer request_lo, Integer request_hi) -> void
{
    if (_imp->logger->get_assertion_level() > AssertionLevel::Links)
        return;

    auto [lb, ub] = _imp->integer_variable_definition_bounds.at(id);
    auto & boundaries = _imp->interval_partitions[id];
    boundaries.insert(lb);
    boundaries.insert(ub + 1_i);

    // Every pre-existing eq atom becomes a singleton cell, so that coverings can
    // reach conclusions already logged over those atoms.
    if (const auto * atoms = _imp->find_atoms(id))
        for (const auto & [raw_v, _] : atoms->eq_defs)
            if (Integer v{raw_v}; lb <= v && v <= ub) {
                boundaries.insert(v);
                boundaries.insert(v + 1_i);
            }

    boundaries.insert(request_lo);
    boundaries.insert(request_hi + 1_i);

    // Define a literal for every cell, then emit the at-least-one clause over the
    // top-level partition, which gives wipeout detection at the literal level. It is
    // RUP from the bound axioms via the cells' reverse reifications and the order
    // chain.
    WPBSum root_covering;
    for (auto it = boundaries.begin(); next(it) != boundaries.end(); ++it) {
        auto cell_lo = *it, cell_hi = *next(it) - 1_i;
        if (cell_lo == cell_hi)
            need_direct_encoding_for(id, cell_lo);
        else
            define_plain_invar(id, cell_lo, cell_hi);
        append_cell_literal_to(root_covering, id, cell_lo, cell_hi);
    }
    _imp->logger->emit_rup_proof_line(move(root_covering) >= 1_i, ProofLevel::Top);
}

auto NamesAndIDsTracker::need_invar(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> ProofLiteral
{
    if (lo > hi)
        return FalseLiteral{};

    if (lo == hi) {
        need_direct_encoding_for(id, lo);
        return visit([&](const auto & id) -> ProofLiteral { return id == lo; }, id);
    }

    auto as_literal = [&]() { return visit([&](const auto & id) -> ProofLiteral { return in_range(id, lo, hi); }, id); };

    auto & for_this_var = _imp->invars_that_exist[id];
    if (for_this_var.contains(pair{lo, hi}))
        return as_literal();

    if (! _imp->logger)
        throw UnimplementedException{"range literals during model writing are not yet supported"};
    if (! has_bit_representation(id))
        throw ProofError{"range literal requested for a variable without a bits encoding"};

    // The literal is defined over its own two cuts even when they lie outside the
    // definition bounds; the bound-axiom units falsify the out-of-bounds part by
    // unit propagation. The partition only spans the definition range, so the
    // covering is over the cells of the in-bounds intersection.
    auto [lb, ub] = _imp->integer_variable_definition_bounds.at(id);
    auto span_lo = max(lo, lb), span_hi = min(hi, ub);

    if (span_lo > span_hi || _imp->assertion_level > AssertionLevel::Links) {
        // Entirely outside: the reification plus the bound axioms already falsify
        // it, so there is nothing to cover;
        // ...OR we are at a higher assertion level that doesn't need covering apparatus in the first place.
        define_plain_invar(id, lo, hi);
        return as_literal();
    }

    if (! _imp->interval_partitions.contains(id)) {
        init_interval_partition(id, span_lo, span_hi);
    }
    else {
        ensure_partition_cut(id, span_lo);
        ensure_partition_cut(id, span_hi + 1_i);
    }

    // If the request is exactly one cell, it was defined just now.
    const auto & boundaries = _imp->interval_partitions.at(id);
    if (lo == span_lo && hi == span_hi && *next(boundaries.find(span_lo)) == span_hi + 1_i)
        return as_literal();

    // Otherwise define it, with a covering over the in-bounds cells it spans, so
    // that falsifying those pieces falsifies it by unit propagation.
    define_plain_invar(id, lo, hi);
    WPBSum covering;
    visit([&](const auto & id) { covering += 1_i * not_in_range(id, lo, hi); }, id);
    for (auto it = boundaries.find(span_lo); *it != span_hi + 1_i; ++it)
        append_cell_literal_to(covering, id, *it, *next(it) - 1_i);
    _imp->logger->emit_rup_proof_line(move(covering) >= 1_i, ProofLevel::Top);
    return as_literal();
}

auto NamesAndIDsTracker::has_bit_representation(const SimpleOrProofOnlyIntegerVariableID & id) const -> bool
{
    return _imp->integer_variable_bits_to_size_and_proof_vars.contains(id);
}

auto NamesAndIDsTracker::view_bounds(const ViewOfIntegerVariableID & view) const -> pair<Integer, Integer>
{
    auto bounds_it = _imp->integer_variable_definition_bounds.find(view.actual_variable);
    if (bounds_it == _imp->integer_variable_definition_bounds.end())
        throw ProofError{"view_bounds: underlying variable's bounds are not registered"};
    auto [x_lo, x_hi] = bounds_it->second;
    return view.negate_first ? pair{-x_hi + view.then_add, -x_lo + view.then_add} : pair{x_lo + view.then_add, x_hi + view.then_add};
}

auto NamesAndIDsTracker::need_view(const ViewOfIntegerVariableID & view) -> ProofOnlySimpleIntegerVariableID
{
    if (auto it = _imp->view_proof_only_vars.find(view); it != _imp->view_proof_only_vars.end())
        return it->second;

    if (! _imp->model)
        throw UnimplementedException{"need_view: view introduction during proof-logging phase is not yet supported"};

    auto [v_lo, v_hi] = view_bounds(view);

    string name = "view_of_" + name_of(view.actual_variable);
    if (view.negate_first)
        name = "neg_" + name;
    if (view.then_add != 0_i)
        name += "_plus_" + to_string(view.then_add.raw_value);

    auto v_id = _imp->model->create_proof_only_integer_variable(v_lo, v_hi, name, IntegerVariableProofRepresentation::Bits);

    Integer s_coeff = view.negate_first ? -1_i : 1_i;

    // Views must be defined properly in the model. Cake has no view variables, so
    // there is no cake label to match: invent one named after the view, referenced
    // by label rather than line number.
    auto [link_le, link_ge] = _imp->model->add_labelled_constraint(
        "c[" + name + "][viewle]", "c[" + name + "][viewge]", WPBSum{} + 1_i * v_id + (-s_coeff) * view.actual_variable == view.then_add);

    _imp->view_proof_only_vars.emplace(view, v_id);
    _imp->view_proof_only_to_view.emplace(v_id, view);
    _imp->view_link_ids.emplace(v_id, pair{link_le, link_ge});
    _imp->views_of_variable[view.actual_variable].push_back(v_id);

    if (_imp->assertion_level > AssertionLevel::Links) // No further linking needed at higher assertion levels.
        return v_id;

    // Backfill: if X atoms already exist when this view is registered,
    // trigger the matching V atoms now so the V<->X link is emitted for
    // them. (Atoms introduced later go via the X-side hook in need_gevar /
    // need_direct_encoding_for.) Copy the X-side maps before iterating
    // because the V-side need_* calls add entries to other maps and may
    // recurse back through need_gevar(X, ...), which is a no-op for
    // already-existing atoms but would invalidate iterators if it weren't.
    SimpleOrProofOnlyIntegerVariableID x_key{view.actual_variable};
    if (auto it = _imp->gevar_values.find(x_key); it != _imp->gevar_values.end()) {
        auto x_atoms = it->second;
        for (const auto & k : x_atoms) {
            Integer v_value = view.negate_first ? view.then_add - k + 1_i : k + view.then_add;
            need_gevar(v_id, v_value);
        }
    }
    if (const auto * atoms = _imp->find_atoms(x_key); atoms && ! atoms->eq_defs.empty()) {
        // Ascending, so the backfilled V atoms are emitted in the same
        // order the ordered map this replaces produced.
        vector<long long> x_atom_values;
        x_atom_values.reserve(atoms->eq_defs.size());
        for (const auto & [k, _] : atoms->eq_defs)
            x_atom_values.push_back(k);
        sort(x_atom_values);
        for (const auto & k : x_atom_values) {
            Integer v_value = view.negate_first ? view.then_add - Integer{k} : Integer{k} + view.then_add;
            need_direct_encoding_for(v_id, v_value);
        }
    }

    return v_id;
}

auto NamesAndIDsTracker::find_view(const ViewOfIntegerVariableID & view) const -> optional<ProofOnlySimpleIntegerVariableID>
{
    if (auto it = _imp->view_proof_only_vars.find(view); it != _imp->view_proof_only_vars.end())
        return it->second;
    return std::nullopt;
}

auto NamesAndIDsTracker::register_deviewed_line(const ProofLine & v_form_line, const ProofLine & deviewed_line) -> void
{
    _imp->deviewed_line_by_v_form.emplace(v_form_line, deviewed_line);
}

auto NamesAndIDsTracker::deviewed_line_for(const ProofLine & line) const -> ProofLine
{
    if (auto it = _imp->deviewed_line_by_v_form.find(line); it != _imp->deviewed_line_by_v_form.end())
        return it->second;
    return line;
}

auto NamesAndIDsTracker::view_link_lines_for(const ProofOnlySimpleIntegerVariableID & view_proof_id) const -> pair<ProofLine, ProofLine>
{
    auto it = _imp->view_link_ids.find(view_proof_id);
    if (it == _imp->view_link_ids.end())
        throw ProofError{"view_link_lines_for: no link recorded for this proof-only var"};
    return it->second;
}

auto NamesAndIDsTracker::derive_deviewed_form_for(const ProofLine & v_form_line, const SumOf<Weighted<PseudoBooleanTerm>> & lhs, bool le_half) -> void
{
    // Walk the lhs terms and collect, for each view appearance, the
    // (opb_form_coefficient, view_proof_id) pair. opb_form_coefficient is
    // the WPBSum coefficient with sign flipped if le_half is true (since
    // emit_inequality_to negates the LE half on emission to land in
    // PB >= normal form).
    struct ViewContribution
    {
        ProofOnlySimpleIntegerVariableID view_proof_id;
        Integer opb_form_coefficient;
    };
    vector<ViewContribution> view_contributions;

    for (const auto & [w, v] : lhs.terms) {
        if (0_i == w)
            continue;
        if (auto var = std::get_if<IntegerVariableID>(&v)) {
            // Path 1: propagator-passed `IntegerVariableID` holding a view.
            if (auto view = std::get_if<ViewOfIntegerVariableID>(var)) {
                if (auto v_proof_id = find_view(*view)) {
                    Integer opb_coeff = le_half ? -w : w;
                    view_contributions.push_back({*v_proof_id, opb_coeff});
                }
            }
        }
        else if (auto proof_only = std::get_if<ProofOnlySimpleIntegerVariableID>(&v)) {
            // Path 2: framework-emitted constraint over a view's proof-only
            // var (e.g. Def(v>=k) in `need_gevar`). Treat the proof-only var
            // term the same way as a view-bearing term so propagators that
            // reference Def lines via `need_pol_item_defining_literal` get a
            // deview-form that puts the Def in X-form.
            if (_imp->view_proof_only_to_view.contains(*proof_only)) {
                Integer opb_coeff = le_half ? -w : w;
                view_contributions.push_back({*proof_only, opb_coeff});
            }
        }
    }

    if (view_contributions.empty())
        return;

    if (_imp->assertion_level > AssertionLevel::Links)
        return;
    // Build the pol expression. For each view contribution:
    //   opb_form_coefficient > 0 (positive V in OPB):  add `|coeff| * link_le`.
    //   opb_form_coefficient < 0 (negative V in OPB):  add `|coeff| * link_ge`.
    // Reasoning: link_le contributes `-BinEnc(V) + ...` so it cancels
    // positive V; link_ge contributes `+BinEnc(V) + ...` so it cancels
    // negative V.
    //
    // This is a plain PolBuilder, NOT a deview-mode one: it pushes the raw
    // V-form `v_form_line` and link lines. A deview-mode builder would call
    // back into `deviewed_line_for(v_form_line)` while we are mid-way through
    // deriving that very line, so plain mode is both correct and avoids that
    // self-reference.
    //
    // We deliberately do NOT saturate. Downstream consumers (PolBuilder in
    // deview mode) use this line as the starting constraint in their own
    // pol + divide chains. Saturating here would clip bit-level coefficients
    // on wide-range variables (those encoded with a sign bit + magnitude bits),
    // which then leaks an uncancelled residual into the consumer's pol when
    // it adds a reif on the same variable. The unsaturated form has the full
    // bit-level coefficient mass needed for clean cancellation.
    // Shared PolBuilder (not a rendered string) so the line refs emit as
    // relative indices -- see make_pol_chain_line above for why.
    auto pol = make_shared<PolBuilder>();
    pol->add(v_form_line);
    for (const auto & vc : view_contributions) {
        auto [link_le, link_ge] = view_link_lines_for(vc.view_proof_id);
        Integer mult = vc.opb_form_coefficient > 0_i ? vc.opb_form_coefficient : -vc.opb_form_coefficient;
        const ProofLine & link_to_use = vc.opb_form_coefficient > 0_i ? link_le : link_ge;
        pol->add(link_to_use, mult);
    }

    emit_proof_line_now_or_at_start([this, v_form_line, pol](ProofLogger * const logger) {
        auto deview_line = pol->emit(*logger, ProofLevel::Top);
        register_deviewed_line(v_form_line, deview_line);
    });
}

auto NamesAndIDsTracker::track_bounds(const SimpleOrProofOnlyIntegerVariableID & id, Integer lower, Integer upper) -> void
{
    _imp->integer_variable_definition_bounds.emplace(id, pair{lower, upper});
}

auto NamesAndIDsTracker::tracked_bounds(const SimpleOrProofOnlyIntegerVariableID & id) const -> pair<Integer, Integer>
{
    return _imp->integer_variable_definition_bounds.at(id);
}

auto NamesAndIDsTracker::track_bound_rows(const SimpleOrProofOnlyIntegerVariableID & id, ProofLine lower_row, ProofLine upper_row) -> void
{
    _imp->integer_variable_bound_rows.emplace(id, pair{lower_row, upper_row});
}

auto NamesAndIDsTracker::bound_rows(const SimpleOrProofOnlyIntegerVariableID & id) const -> optional<pair<ProofLine, ProofLine>>
{
    auto it = _imp->integer_variable_bound_rows.find(id);
    if (it == _imp->integer_variable_bound_rows.end())
        return nullopt;
    return it->second;
}

auto NamesAndIDsTracker::note_bounds_not_trivially_derivable(const SimpleOrProofOnlyIntegerVariableID & id) -> void
{
    _imp->bounds_not_trivially_derivable.insert(id);
}

auto NamesAndIDsTracker::note_order_encoding_stays_resident(const SimpleOrProofOnlyIntegerVariableID & id) -> void
{
    _imp->order_encoding_stays_resident.insert(id);
}

auto NamesAndIDsTracker::note_recover_atom_labels_in_proof(const SimpleOrProofOnlyIntegerVariableID & id) -> void
{
    _imp->vars_recover_labels.insert(id);
}

auto NamesAndIDsTracker::claim_constraint_row_labels(const vector<string> & labels) -> void
{
    // A label exists so that a proof step can cite this row, so no two rows in
    // the c[id][role] namespace may carry the same one: with both spelled
    // @c[id][role], a reference to either is ambiguous, and opbdiff
    // --match-labels pairs the two encoders' rows by label. A duplicate is
    // always a bug in the emitting define_proof_model -- a role that does not
    // name everything the surrounding loops vary over (#604: ValuePrecede keyed
    // its ub/ex roles by position but not by chain value, inside a loop over
    // values) -- so it is a hard error rather than a first-wins or last-wins
    // pick.
    //
    // Only the ConstraintID-taking overloads claim, which is what confines this
    // to c[id][role]. The variable-encoding namespaces -- @i[name][...] for a
    // real variable, @po[index] for a proof-only one -- are deliberately left
    // out: a variable's encoding rows can be deleted and re-emitted to keep the
    // proof database small, so a repeat there is by design rather than a naming
    // bug. Their uniqueness is the namer's business, not this check's.
    //
    // The whole pack is claimed before any of it is emitted, so that the
    // equality overload's two halves are all-or-nothing: a rejected pair must
    // not leave its LE row behind in the OPB. Claiming them together is also
    // what catches a caller passing the same role for both halves.
    for (const auto & label : labels)
        if (! _imp->emitted_constraint_row_labels.insert(label).second)
            throw ProofError{"two OPB rows emitted under the same label '@" + label +
                "': a role must name everything that varies, so that each row can be cited unambiguously"};
}

auto NamesAndIDsTracker::constraint_row_label(const ConstraintID & id, const string & role) const -> optional<ProofLineLabel>
{
    // Built the same way ProofModel::emit_constraint_label builds it, because it
    // has to be the same string: that is what makes this a pure function of
    // (id, role) rather than a lookup into per-solve state.
    auto label = "c[" + as_string(id) + "]" + (role.empty() ? "" : "[" + role + "]");
    if (! _imp->emitted_constraint_row_labels.contains(label))
        return nullopt;
    return ProofLineLabel{label};
}

auto NamesAndIDsTracker::create_proof_flag(const string & name) -> ProofFlag
{
    ProofFlag result{allocate_flag_index(), true};
    track_variable_name(result, name);
    auto flagvar = allocate_xliteral_meaning(result);
    _imp->flags.emplace(result, flagvar);
    _imp->flags.emplace(! result, ! flagvar);
    return result;
}

auto NamesAndIDsTracker::create_proof_flag(const ConstraintID & id, const vector<long long> & indices, const optional<string> & annotation)
    -> ProofFlag
{
    // Mirror cake_pb_cp's Indices flag rendering (cp_to_ilpScript.sml format_flag):
    // x[id][i1_i2..][annotation?] -- the index list joined by '_', the optional
    // annotation in its own brackets.
    string name = "x[" + as_string(id) + "][";
    for (size_t k = 0; k < indices.size(); ++k) {
        if (k != 0)
            name += "_";
        name += to_string(indices[k]);
    }
    name += "]";
    if (annotation)
        name += "[" + *annotation + "]";
    return make_proof_flag_named(name);
}

auto NamesAndIDsTracker::create_proof_flag(const ConstraintID & id, const string & annotation) -> ProofFlag
{
    // Mirror cake_pb_cp's Flag rendering (cp_to_ilpScript.sml format_flag):
    // b[id][annotation] -- a scalar flag carrying only an annotation, no index
    // list. Used where the auxiliary is per-constraint rather than per-position,
    // e.g. not_equals' single `ne` selector b[id][ne]. See #354.
    return make_proof_flag_named("b[" + as_string(id) + "][" + annotation + "]");
}

auto NamesAndIDsTracker::create_proof_flag_values(const ConstraintID & id, const vector<long long> & values, const optional<string> & annotation)
    -> ProofFlag
{
    // Mirror cake_pb_cp's Values flag rendering (cp_to_ilpScript.sml format_flag):
    // v[id][v1_v2..][annotation?] -- the value list joined by '_', the optional
    // annotation in its own brackets. The values are domain values, in contrast
    // to the array positions of the x[...] overload; nvalue's per-value
    // occurrence flag is create_proof_flag_values(id, {v}) -> v[id][v]. See #354.
    string name = "v[" + as_string(id) + "][";
    for (size_t k = 0; k < values.size(); ++k) {
        if (k != 0)
            name += "_";
        // Negative values are rendered `-N`, matching cake's format_int_list and
        // the solver's eq/ge literals (i[X][eq-N]). VeriPB allows '-' in both
        // variable names and @labels (VeriPB-dev #191), so this is legal in the
        // labelled flag definitions too and byte-matches cake over negative
        // domains.
        name += to_string(values[k]);
    }
    name += "]";
    if (annotation)
        name += "[" + *annotation + "]";
    return make_proof_flag_named(name);
}

auto NamesAndIDsTracker::create_proof_flag_for_constant(Integer k, const string & atom) -> ProofFlag
{
    // Mirror cake_pb_cp's constant-atom rendering (cp_encScript.sml format_var,
    // Ge/Eq over a constant): n[<k>][<atom>], the constant rendered with a
    // leading '-' when negative, exactly like the eq/ge literal values.
    return make_proof_flag_named("n[" + to_string(k.raw_value) + "][" + atom + "]");
}

auto NamesAndIDsTracker::make_proof_flag_named(const string & full_name) -> ProofFlag
{
    // The supplied name is used verbatim as the PB-file variable name (rather
    // than wrapped in `f[index][...]`), so the same string is both the tracked
    // name and the verbose rendering. See the header for why.
    ProofFlag result{allocate_flag_index(), true};
    track_variable_name(result, full_name);
    auto flagvar = allocate_flag_xliteral(result, full_name);
    _imp->flags.emplace(result, flagvar);
    _imp->flags.emplace(! result, ! flagvar);
    return result;
}

auto NamesAndIDsTracker::store_xlit_names(const XLiteral & lit, string name) -> void
{
    // `name` renders the positive polarity; the negation is always `~name`.
    auto idx = static_cast<vector<string>::size_type>(lit.id) * 2;
    if (_imp->xlit_names.size() < idx + 2)
        _imp->xlit_names.resize(idx + 2);
    _imp->xlit_names[idx + 1] = "~" + name;
    _imp->xlit_names[idx] = move(name);
}

auto NamesAndIDsTracker::pb_file_string_for(const XLiteral & lit) const -> const string &
{
    auto idx = static_cast<vector<string>::size_type>(lit.id) * 2 + (lit.negated ? 1 : 0);
    if (idx >= _imp->xlit_names.size() || _imp->xlit_names[idx].empty())
        throw ProofError("missing name for xliteral " + to_string(lit.id) + " " + to_string(lit.negated));
    return _imp->xlit_names[idx];
}

auto NamesAndIDsTracker::pb_file_string_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) const -> const string &
{
    return pb_file_string_for(xliteral_for(cond));
}

auto NamesAndIDsTracker::pb_file_string_for_ensuring(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) -> const string &
{
    return pb_file_string_for(xliteral_for_ensuring(cond));
}

auto NamesAndIDsTracker::xliteral_for_ensuring(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) -> XLiteral
{
    auto f = _imp->find_condition(cond);
    if (! f) {
        need_proof_name(cond);
        f = _imp->find_condition(cond);
        if (! f)
            throw ProofError{"still can't find literals for cond after introducing it"};
    }
    else if (_imp->order_link_deletion_mode != OrderEncodingDeletion::None && _imp->logger && ! _imp->building_order_link) {
        // Under order-encoding deletion an existing atom is NOT enough: atom identity is
        // permanent, but the atom's *definition* may have been deleted by a backtrack, and
        // a line naming a literal whose definition is gone does not verify. So go through
        // need_proof_name anyway -- need_gevar's fast path re-introduces a deleted
        // definition (and reconnects the chain) before this line names the literal. This
        // is what the old need_all_proof_names_in pre-pass did unconditionally; the fused
        // renderer skips it for known atoms, which is right for every other mode.
        // Deletion off (the default) keeps the single-lookup path untouched.
        // The XLiteral itself never changes -- re-introduction re-emits definition lines
        // and rewrites their line numbers, it never re-mints the atom -- so the value
        // found above stays correct.
        need_proof_name(cond);
    }
    return *f;
}

auto NamesAndIDsTracker::bit_assignment_string_for(const SimpleOrProofOnlyIntegerVariableID & var, const Integer & value) const -> string
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(var);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");

    const auto & [negative_coeff, bits] = it->second;

    bool sign_bit_set = (negative_coeff != 0_i) && (value < 0_i);
    Integer remainder = sign_bit_set ? value - negative_coeff : value;

    string result;
    for (const auto & [coeff, lit] : bits) {
        bool bit_is_one = (coeff < 0_i) ? sign_bit_set : ((remainder / coeff) % 2_i == 1_i);
        if (! result.empty())
            result += " ";
        result += pb_file_string_for(bit_is_one ? lit : ! lit);
    }

    return result;
}

auto NamesAndIDsTracker::xliteral_for(const ProofFlag & flag) const -> const XLiteral
{
    auto f = _imp->flags.find(flag);
    if (f == _imp->flags.end())
        throw ProofError{"can't find literals for flag"};
    return f->second;
}

auto NamesAndIDsTracker::find_xliteral_for(const ProofFlag & flag) const -> optional<XLiteral>
{
    auto f = _imp->flags.find(flag);
    if (f == _imp->flags.end())
        return nullopt;
    return f->second;
}

auto NamesAndIDsTracker::xliteral_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) const -> const XLiteral
{
    auto f = _imp->find_condition(cond);
    if (! f)
        throw ProofError{"can't find literals for cond"};
    return *f;
}

auto NamesAndIDsTracker::find_xliteral_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) const -> optional<XLiteral>
{
    // Same lookup as xliteral_for, which is the point: this is its non-throwing
    // twin, so it must see exactly the same atoms (recover_am1 uses it to spot a
    // complementary {~b0, b0} pair over a bit-aliased {0,1} variable, issue #557).
    return _imp->find_condition(cond);
}

auto NamesAndIDsTracker::pb_file_string_for(const ProofFlag & flag) const -> const string &
{
    return pb_file_string_for(xliteral_for(flag));
}

namespace
{
    auto write_vardata(fstream & stream, bool & first, const string & name, const nlohmann::json & json) -> void
    {
        if (! first)
            stream << ",\n";
        else
            first = false;

        nlohmann::json name_json = name;
        stream << name_json << ": " << json;
    }
}

auto NamesAndIDsTracker::allocate_xliteral_meaning(SimpleOrProofOnlyIntegerVariableID id, const EqualsOrGreaterEqual & op, Integer value) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        // Negative values render as `-N` (matching cake); '-' is legal in both
        // VeriPB variable names and @labels (VeriPB-dev #191).
        string value_name = value.to_string();

        overloaded{
            [&](const SimpleIntegerVariableID & id) -> void {
                string name = format("i[{}][{}{}]", name_of(id), (op == EqualsOrGreaterEqual::Equals ? "eq" : "ge"), value_name);
                store_xlit_names(result, name);
            }, //
            [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                string name = format("p[{}_{}][{}{}]", id.index, name_of(id), (op == EqualsOrGreaterEqual::Equals ? "eq" : "ge"), value_name);
                store_xlit_names(result, name);
            } //
        }
            .visit(id);
    }
    else
        store_xlit_names(result, "x" + to_string(result.id));

    if (_imp->variables_map_file) {
        try {
            nlohmann::json data;
            data["type"] = "condition";
            overloaded{
                [&](const SimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "intvar";
                    data["cpvarid"] = id.index;
                }, //
                [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "proofintvar";
                    data["cpvarid"] = id.index;
                } //
            }
                .visit(id);

            data["name"] = name_of(id);
            data["operator"] = (op == EqualsOrGreaterEqual::Equals ? "=" : ">=");
            data["value"] = value.raw_value;

            write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }

    return result;
}

auto NamesAndIDsTracker::allocate_xliteral_meaning(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        // Negative values render as `-N` (matching cake); '-' is legal in both
        // VeriPB variable names and @labels (VeriPB-dev #191).
        auto value_name = [](Integer v) { return v.to_string(); };

        overloaded{
            [&](const SimpleIntegerVariableID & id) -> void {
                string name = format("i[{}][in{}_{}]", name_of(id), value_name(lo), value_name(hi));
                store_xlit_names(result, name);
            }, //
            [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                string name = format("p[{}_{}][in{}_{}]", id.index, name_of(id), value_name(lo), value_name(hi));
                store_xlit_names(result, name);
            } //
        }
            .visit(id);
    }
    else
        store_xlit_names(result, "x" + to_string(result.id));

    if (_imp->variables_map_file) {
        try {
            nlohmann::json data;
            data["type"] = "condition";
            overloaded{
                [&](const SimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "intvar";
                    data["cpvarid"] = id.index;
                }, //
                [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "proofintvar";
                    data["cpvarid"] = id.index;
                } //
            }
                .visit(id);

            data["name"] = name_of(id);
            data["operator"] = "in";
            data["value"] = lo.raw_value;
            data["upper_value"] = hi.raw_value;

            write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }

    return result;
}

auto NamesAndIDsTracker::allocate_flag_xliteral(ProofFlag flag, const string & verbose_name) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        store_xlit_names(result, verbose_name);
    }
    else
        store_xlit_names(result, "x" + to_string(result.id));

    if (_imp->variables_map_file) {
        try {
            nlohmann::json data;
            data["type"] = "proofflag";
            data["name"] = name_of(flag);

            write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }

    return result;
}

auto NamesAndIDsTracker::allocate_xliteral_meaning(ProofFlag flag) -> XLiteral
{
    return allocate_flag_xliteral(flag, format("f[{}][{}]", flag.index, name_of(flag)));
}

auto NamesAndIDsTracker::allocate_xliteral_meaning_negative_bit_of(
    SimpleOrProofOnlyIntegerVariableID id, Integer power, const optional<string> & name_override) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        string name = name_override
            ? *name_override
            : visit(overloaded{                                                                                 //
                        [&](const SimpleIntegerVariableID & id) { return format("i[{}][sign]", name_of(id)); }, //
                        [&](const ProofOnlySimpleIntegerVariableID & id) { return format("p[{}_{}][sign]", id.index, name_of(id)); }},
                  id);
        store_xlit_names(result, name);
    }
    else
        store_xlit_names(result, "x" + to_string(result.id));

    if (_imp->variables_map_file) {
        try {
            nlohmann::json data;
            data["type"] = "intvarnegbit";
            overloaded{
                [&](const SimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "intvar";
                    data["cpvarid"] = id.index;
                }, //
                [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "proofintvar";
                    data["cpvarid"] = id.index;
                } //
            }
                .visit(id);
            data["name"] = name_of(id);
            data["power"] = power.raw_value;

            write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }

    return result;
}

auto NamesAndIDsTracker::allocate_xliteral_meaning_bit_of(
    SimpleOrProofOnlyIntegerVariableID id, Integer power, const optional<string> & name_override) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        // name_override lets a proof-only variable's bits be named in a caller-chosen
        // scheme (cake_pb_cp's value flags) rather than the default p[index_name][b];
        // the literal is still the variable's bit, only named.
        string name = name_override
            ? *name_override
            : visit(overloaded{                                                                                       //
                        [&](const SimpleIntegerVariableID & id) { return format("i[{}][b{}]", name_of(id), power); }, //
                        [&](const ProofOnlySimpleIntegerVariableID & id) { return format("p[{}_{}][b{}]", id.index, name_of(id), power); }},
                  id);
        store_xlit_names(result, name);
    }
    else
        store_xlit_names(result, "x" + to_string(result.id));

    if (_imp->variables_map_file) {
        try {
            nlohmann::json data;
            data["type"] = "intvarbit";
            overloaded{
                [&](const SimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "intvar";
                    data["cpvarid"] = id.index;
                }, //
                [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "proofintvar";
                    data["cpvarid"] = id.index;
                } //
            }
                .visit(id);

            data["name"] = name_of(id);
            data["power"] = power.raw_value;

            write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }

    return result;
}

auto NamesAndIDsTracker::track_variable_name(SimpleOrProofOnlyIntegerVariableID id, const string & name) -> void
{
    _imp->id_names.emplace(id, name);
}

auto NamesAndIDsTracker::track_variable_name(ProofFlag id, const string & name) -> void
{
    _imp->flag_names.emplace(id, name);
}

auto NamesAndIDsTracker::name_of(SimpleOrProofOnlyIntegerVariableID id) const -> const string &
{
    return _imp->id_names.at(id);
}

auto NamesAndIDsTracker::name_of(ProofFlag id) const -> const string &
{
    return _imp->flag_names.at(id);
}

auto NamesAndIDsTracker::s_expr_name_of(IntegerVariableID id) const -> string
{
    return overloaded{
        [&](const ConstantIntegerVariableID & c) -> string { return c.const_value.to_string(); }, //
        [&](const SimpleIntegerVariableID & v) -> string { return name_of(v); },                  //
        [&](const ViewOfIntegerVariableID & vv) -> string {
            stringstream name;
            name << "(";
            name << (vv.negate_first ? "-" : "");
            name << name_of(vv.actual_variable) << " + " << vv.then_add << ")";
            return name.str();
        } //
    }
        .visit(id);
}

auto NamesAndIDsTracker::s_expr_name_of(Literal lit) const -> string
{
    return overloaded{
        [](const TrueLiteral &) -> string { return "1"; },                                                                //
        [](const FalseLiteral &) -> string { return "0"; },                                                               //
        [&](const VariableConditionFrom<SimpleIntegerVariableID> & cond) -> string { return s_expr_name_of(cond.var); },  //
        [](const VariableConditionFrom<ProofOnlySimpleIntegerVariableID> &) -> string { throw UnimplementedException{}; } //
    }
        .visit(simplify_literal(*this, lit));
}

auto NamesAndIDsTracker::s_expr_name_of(ReificationCondition cond) const -> string
{
    return overloaded{
        [](const reif::MustHold &) -> string { return ""; },    //
        [](const reif::MustNotHold &) -> string { return ""; }, //
        [&](const auto & reif) -> string {                      // This is safe, right?
            return "(" + s_expr_name_of(reif.cond.var) + " " + s_expr_name_of(reif.cond.op) + " " + reif.cond.value.to_string() + ")";
        } //
    }
        .visit(cond);

    return "COND";
}

auto NamesAndIDsTracker::s_expr_name_of(VariableConditionOperator op) const -> string
{
    switch (op) {
        using enum VariableConditionOperator;
        // cake_pb_cp's reification-condition operators are symbols, not words.
    case Equal: return "=";
    case NotEqual: return "!=";
    case GreaterEqual: return ">=";
    case Less: return "<";
    case InRange:
    case NotInRange:
        // cake_pb_cp has no range-condition spelling yet, and range conditions
        // cannot appear in reified constraints (model-phase need_invar throws)
        throw UnimplementedException{};
    }

    throw NonExhaustiveSwitch{};
}

auto NamesAndIDsTracker::s_expr_render_of(IntegerVariableID id) const -> string
{
    return overloaded{
        [&](const ConstantIntegerVariableID & c) -> string { return "(minimize " + c.const_value.to_string() + ")"; }, //
        [&](const SimpleIntegerVariableID & v) -> string { return "(minimize " + name_of(v) + ")"; },                  //
        [&](const ViewOfIntegerVariableID & vv) -> string {
            return "(" + string{vv.negate_first ? "maximize" : "minimize"} + " " + name_of(vv.actual_variable) + ")";
        } //
    }
        .visit(id);
}

auto NamesAndIDsTracker::s_expr_term_of(IntegerVariableID id) const -> SExpr
{
    // A variable / literal name is always a single, non-empty s-expression term
    // (a bare atom like `_1`, or a list like a view `(-_1 + 17)`), so parsing it
    // can't fail or be empty.
    return parse_s_expr(s_expr_name_of(id));
}

auto NamesAndIDsTracker::s_expr_term_of(Literal lit) const -> SExpr
{
    // As for the variable overload: s_expr_name_of(Literal) is always a single,
    // non-empty term (a bare atom for a condition/True/False, or a view list).
    return parse_s_expr(s_expr_name_of(lit));
}

auto NamesAndIDsTracker::s_expr_term_of(ReificationCondition cond) const -> optional<SExpr>
{
    // s_expr_name_of(ReificationCondition) returns "" for the unconditional
    // cases (MustHold / MustNotHold); surface that as nullopt so callers don't
    // have to know about the empty-string sentinel.
    auto name = s_expr_name_of(cond);
    if (name.empty())
        return nullopt;
    return parse_s_expr(name);
}

auto NamesAndIDsTracker::reification_shape(const WPBSumLE & ineq, const HalfReifyOnConjunctionOf & half_reif) -> ReificationShape
{
    // so what happens if there's a false literal in the left hand term? conceptually,
    // this means the constraint will always hold, but it's probably useful to have
    // something that syntactically contains all the right variables. so, we can just
    // make the degree of falsity be very low so the constraint always holds.
    bool contains_false_literal = any_of(half_reif.begin(), half_reif.end(), [&](const auto & flag) {
        return overloaded{
            [&](const ProofFlag &) { return false; }, //
            [&](const ProofLiteral & pl) {
                return overloaded{
                    [&](Literal lit) { return is_literally_false(lit); },  //
                    [&](const ProofVariableCondition &) { return false; }, //
                }
                    .visit(pl);
            },                                              //
            [&](const ProofBitVariable &) { return false; } //
        }
            .visit(flag);
    });

    // work out how big the reification constant needs to be, by adding together
    // positive terms in the inequality and negating
    Integer max_contribution_from_positive_terms = 0_i;

    for (auto & [w, v] : ineq.lhs.terms) {
        overloaded{
            [&, w = w](const ProofLiteral &) { max_contribution_from_positive_terms += max(0_i, w); }, //
            [&, w = w](const ProofFlag &) { max_contribution_from_positive_terms += max(0_i, w); },    //
            [&, w = w](const IntegerVariableID & var) {
                overloaded{
                    [&](const SimpleIntegerVariableID & var) {
                        for (const auto & [bit_value, bit_lit] : each_bit(var))
                            max_contribution_from_positive_terms += max(0_i, w * bit_value);
                    }, //
                    [&](const ViewOfIntegerVariableID & view) {
                        // A registered view is *emitted* over its own proof-only
                        // bit-vector (BinEnc(V) directly encodes the view value),
                        // so the reification constant must be sized from those
                        // bits too. Sizing it from the underlying variable's bits
                        // + then_add (the X representation) instead gives a span
                        // matching the view's value range but smaller than its
                        // bit-vector's, leaving the reified line valid only modulo
                        // V's domain bound -- which RUP can't fold in.
                        if (auto v_proof_id = find_view(view)) {
                            for (const auto & [bit_value, bit_lit] : each_bit(*v_proof_id))
                                max_contribution_from_positive_terms += max(0_i, w * bit_value);
                        }
                        // The term is w * view = w * ((negate_first ? -actual : actual) + then_add).
                        // The variable part w * (negate_first ? -actual : actual) has per-bit max
                        // contribution max(0, ±w * bit_value), with the sign flip depending on
                        // negate_first. The constant part w * then_add applies regardless and is
                        // not affected by negate_first.
                        else if (! view.negate_first) {
                            for (const auto & [bit_value, bit_lit] : each_bit(view.actual_variable))
                                max_contribution_from_positive_terms += max(0_i, w * bit_value);
                            max_contribution_from_positive_terms += max(0_i, w * view.then_add);
                        }
                        else {
                            for (const auto & [bit_value, bit_lit] : each_bit(view.actual_variable))
                                max_contribution_from_positive_terms += max(0_i, -w * bit_value);
                            max_contribution_from_positive_terms += max(0_i, w * view.then_add);
                        }
                    },                                                                                                                      //
                    [&](const ConstantIntegerVariableID & cvar) { max_contribution_from_positive_terms += max(0_i, w * cvar.const_value); } //
                }
                    .visit(var);
            }, //
            [&, w = w](const ProofOnlySimpleIntegerVariableID & var) {
                for (const auto & [bit_value, bit_lit] : each_bit(var))
                    max_contribution_from_positive_terms += max(0_i, w * bit_value);
            },                                                                                             //
            [&, w = w](const ProofBitVariable &) { max_contribution_from_positive_terms += max(0_i, w); }, //
        }
            .visit(v);
    }

    // Usually it would be fine to say 0_i rather than -1_i here, because if a constraint
    // is trivially true, it doesn't really matter whether the implication is there or
    // not. However, for syntactic wrangling reasons, we probably want the implication
    // to always be there.
    auto clamped_reif_const = min(-max_contribution_from_positive_terms + ineq.rhs, -1_i);

    // if we have a false literal on the left hand side, adjusting the degree of falsity
    // up by the sum of positive terms is enough that it will be trivially true.
    auto effective_rhs = contains_false_literal ? ineq.rhs + max_contribution_from_positive_terms : ineq.rhs;

    return ReificationShape{.reif_coefficient = clamped_reif_const, .effective_rhs = effective_rhs};
}

auto NamesAndIDsTracker::reify(const WPBSumLE & ineq, const HalfReifyOnConjunctionOf & half_reif) -> WPBSumLE
{
    auto shape = reification_shape(ineq, half_reif);

    WPBSum new_lhs;
    new_lhs.terms.reserve(ineq.lhs.terms.size() + half_reif.size());
    new_lhs.terms.insert(new_lhs.terms.end(), ineq.lhs.terms.begin(), ineq.lhs.terms.end());
    for (auto & r : half_reif)
        overloaded{
            [&](const ProofFlag & f) { new_lhs += shape.reif_coefficient * ! f; },           //
            [&](const ProofLiteral & lit) { new_lhs += shape.reif_coefficient * ! lit; },    //
            [&](const ProofBitVariable & bit) { new_lhs += shape.reif_coefficient * ! bit; } //
        }
            .visit(r);

    return move(new_lhs) <= shape.effective_rhs;
}
