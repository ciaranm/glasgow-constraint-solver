#include <cstdio>
#include <gcs/expression.hh>
#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/hints.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/state.hh>
#include <gcs/interval_set.hh>
#include <gcs/proof.hh>

#include <algorithm>
#include <cstddef>
#include <cstdlib>
#include <deque>
#include <fstream>
#include <optional>
#include <sstream>

#include <variant>
#include <version>
#ifdef __cpp_lib_stacktrace
#include <stacktrace>
#endif

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
using std::format;
#else
#include <fmt/core.h>
using fmt::format;
#endif

#include <util/overloaded.hh>

using std::cmp_less_equal;
using std::deque;
using std::flush;
using std::fstream;
using std::ios;
using std::ios_base;
using std::make_unique;
using std::map;
using std::max;
using std::nullopt;
using std::optional;
using std::ostream;
using std::pair;
using std::string;
using std::stringstream;
using std::tuple;
using std::variant;
using std::vector;
using std::visit;

using namespace gcs;
using namespace gcs::innards;

namespace
{
    const auto INDENT_WIDTH = 5;

    [[nodiscard]] auto deview(const VariableConditionFrom<ViewOfIntegerVariableID> & cond) -> VariableConditionFrom<SimpleIntegerVariableID>
    {
        switch (cond.op) {
        case VariableConditionOperator::NotEqual:
            return cond.var.actual_variable != (cond.var.negate_first ? -cond.value + cond.var.then_add : cond.value - cond.var.then_add);
        case VariableConditionOperator::Equal:
            return cond.var.actual_variable == (cond.var.negate_first ? -cond.value + cond.var.then_add : cond.value - cond.var.then_add);
        case VariableConditionOperator::Less:
            if (cond.var.negate_first)
                return cond.var.actual_variable >= cond.value - cond.var.then_add + 1_i;
            else
                return cond.var.actual_variable < (cond.value - cond.var.then_add);
        case VariableConditionOperator::GreaterEqual:
            if (cond.var.negate_first)
                return cond.var.actual_variable < cond.value - cond.var.then_add + 1_i;
            else
                return cond.var.actual_variable >= (cond.value - cond.var.then_add);
        case VariableConditionOperator::InRange:
        case VariableConditionOperator::NotInRange:
            // A negated view reverses the order, so the endpoints swap; the result
            // is still a contiguous closed interval.
            if (cond.var.negate_first)
                return VariableConditionFrom<SimpleIntegerVariableID>{
                    cond.var.actual_variable, cond.op, cond.var.then_add - cond.upper_value, cond.var.then_add - cond.value};
            else
                return VariableConditionFrom<SimpleIntegerVariableID>{
                    cond.var.actual_variable, cond.op, cond.value - cond.var.then_add, cond.upper_value - cond.var.then_add};
        }
        throw NonExhaustiveSwitch{};
    }

    // Scoped hold on one of the logger's line-assembly buffers: takes the
    // buffer at the current nesting depth, cleared, and releases it on the
    // way out. See the line_buffers member for why this is a stack.
    class LineBufferLease
    {
    private:
        std::size_t & _depth;
        std::string & _buffer;

        [[nodiscard]] static auto buffer_at_depth(deque<string> & buffers, std::size_t depth) -> string &
        {
            if (buffers.size() <= depth)
                buffers.resize(depth + 1);
            return buffers[depth];
        }

    public:
        explicit LineBufferLease(deque<string> & buffers, std::size_t & depth) : _depth(depth), _buffer(buffer_at_depth(buffers, depth))
        {
            _buffer.clear();
            ++_depth;
        }

        ~LineBufferLease()
        {
            --_depth;
        }

        LineBufferLease(const LineBufferLease &) = delete;
        auto operator=(const LineBufferLease &) -> LineBufferLease & = delete;

        [[nodiscard]] auto buffer() -> string &
        {
            return _buffer;
        }
    };

    // The only rendering of an AssertionAnnotation: `:@label ...:name:fields`,
    // the tail of an assertion line. This replaced an ostream operator on the
    // type itself, which is gone rather than kept as a second spelling to hold
    // in step -- the two assert sites below were its only callers.
    auto append_annotation_to(string & out, const AssertionAnnotation & annotation) -> void
    {
        out += ':';
        for (const auto & id_or_label : annotation.derivable_from) {
            out += '@';
            out += id_or_label.label;
            out += ' ';
        }
        out += ':';
        out += annotation.hint_name;
        out += ':';
        if (annotation.hint_fields)
            out += format("{}", *annotation.hint_fields);
    }

    [[nodiscard]] auto witness_literal(NamesAndIDsTracker & names_and_ids_tracker, const ProofLiteralOrFlag & lit) -> string
    {
        return overloaded{
            [&](const ProofLiteral & lit) {
                return overloaded{
                    [](const TrueLiteral &) -> string { return "1"; }, //
                    [](const FalseLiteral &) -> string { return "0"; },
                    [&]<typename T_>(const VariableConditionFrom<T_> & var) -> string { return names_and_ids_tracker.pb_file_string_for(var); } //
                }
                    .visit(simplify_literal(names_and_ids_tracker, lit));
            },                                                                                                                                //
            [&](const ProofFlag & flag) { return names_and_ids_tracker.pb_file_string_for(flag); },                                           //
            [&](const ProofBitVariable & bit) { return names_and_ids_tracker.pb_file_string_for(names_and_ids_tracker.get_bit(bit).second); } //
        }
            .visit(lit);
    }
}

struct ProofLogger::Imp
{
    NamesAndIDsTracker & tracker;

    ProofLineNumber proof_line{0};
    int active_proof_level = 0;
    deque<IntervalSet<long long>> proof_lines_by_level;

    string proof_file;
    fstream proof;
    // A proof is many short lines; the default stream buffer makes for a
    // write syscall every few KB, which shows up at this volume. Installed
    // via pubsetbuf before open in start_proof.
    vector<char> proof_stream_buffer;
    int current_indent = 0;
    AssertionLevel assertion_level;
    OrderEncodingDeletion order_encoding_deletion = OrderEncodingDeletion::None;
    bool eq_window = false;

    // --- the eq-atom window's per-node state (dev_docs/brancher-design.md) ---
    // The clause the most recent backtrack() emitted: the deepest guess it was reasoned
    // over, its line, and the level it landed at. The window's tidy has to delete the
    // refuted sibling's clause -- it names eq(v), so the atom is not free until it goes --
    // and that clause is emitted by the child frame, which returns only a search result.
    // Nothing between the child's backtrack and the parent's advance emits another one (the
    // forget in between emits `del`s and stitches), so "the last backtrack clause"
    // identifies it exactly. The window still checks the recorded guess AND level against
    // the sibling it is tidying and skips the deletion if either differs, so a future
    // caller landing in between costs a win rather than a double deletion.
    struct BacktrackClause
    {
        Literal guess;
        ProofLine line;
        int level;
    };
    optional<BacktrackClause> last_backtrack_clause;
    // The standing frontier advance for each windowed variable, bucketed by the proof level
    // it was emitted at and then by variable, so the next step of that window can delete the
    // one it supersedes. Bucketed by level because a level number is reused by every node at
    // that depth: the bucket is dropped when the level is forgotten (which is what deleted
    // its lines), so a later node at the same depth never inherits the previous one's
    // already-deleted line. Empty unless the window is on.
    map<int, map<long long, ProofLine>> standing_eq_advance;

    // Scratch buffers for assembling proof lines before they are written out,
    // reused across emissions to avoid a stringstream per logged inference.
    // A stack, indexed by line_buffer_depth: rendering a line can introduce a
    // proof name whose definitions are emitted (to the stream, ahead of the
    // buffered line) through a nested emit, which needs its own buffer. A
    // deque so nested growth never invalidates an outer buffer reference.
    deque<string> line_buffers;
    std::size_t line_buffer_depth = 0;

    // Scratch for the ubiquitous `1 * lit >= 1` inference shape, in its
    // rendered LE form (one -1 term, rhs -1), so infer() does not allocate a
    // one-term sum per logged inference. Safe to reuse because nothing
    // reachable from an emission re-enters infer().
    WPBSumLE unit_buffer{{}, -1_i};

    [[nodiscard]] auto unit_holds(const Literal & lit) -> const WPBSumLE &
    {
        unit_buffer.lhs.terms.clear();
        unit_buffer.lhs.terms.emplace_back(-1_i, ProofLiteral{lit});
        return unit_buffer;
    }

    Imp(NamesAndIDsTracker & t) : tracker(t)
    {
    }
};

ProofLogger::ProofLogger(const ProofOptions & proof_options, NamesAndIDsTracker & t) : _imp(make_unique<Imp>(t))
{
    _imp->proof_file = proof_options.proof_file_names.proof_file;
    _imp->proof_lines_by_level.resize(2);
    _imp->assertion_level = proof_options.assertion_level;
    _imp->order_encoding_deletion = proof_options.order_encoding_deletion;
    _imp->eq_window = proof_options.order_encoding_deletion_eq_window;
}

ProofLogger::~ProofLogger() = default;

auto ProofLogger::log_stacktrace() -> void
{
#ifdef __cpp_lib_stacktrace
    static bool do_logging = []() { return getenv("GCS_VERBOSE_LOGGING"); }();

    using std::stacktrace;
    if (do_logging) [[unlikely]] {
        for (const auto & entry : stacktrace::current()) {
            // source_file() uses the host path separator, so match either form:
            // "/gcs/" on POSIX, "\gcs\" from MSVC's PDB paths.
            const auto & file = entry.source_file();
            if (file.contains("/gcs/") || file.contains("\\gcs\\"))
                _imp->proof << "% " << to_string(entry) << '\n';
        }
    }
#endif
}

auto ProofLogger::advance_proof_line_number() -> ProofLineNumber
{
    return ProofLineNumber{++_imp->proof_line.number};
}

auto ProofLogger::solution(const vector<pair<IntegerVariableID, Integer>> & all_variables_and_values,
    const optional<pair<IntegerVariableID, Integer>> & optional_minimise_variable_and_value) -> void
{
    write_indent();
    _imp->proof << "% solution\n";

    for (const auto & [var, val] : all_variables_and_values)
        overloaded{
            [&](const ConstantIntegerVariableID &) {},                                                                //
            [&](const SimpleIntegerVariableID & var) { names_and_ids_tracker().need_proof_name(var == val); },        //
            [&](const ViewOfIntegerVariableID & var) { names_and_ids_tracker().need_proof_name(deview(var == val)); } //
        }
            .visit(var);

    // The solx / soli line below is a permanent (Top) reference to every `var == val` it
    // names, so the eq-atom window's hoist-out rule fires for any of them that is a live
    // windowed definition: retain it at Top instead of letting the window's next tidy evict
    // it, together with the two ge thresholds it names. This is the commonest permanent
    // reference by far -- every solution takes one on each branched variable's current
    // value. Guarded by the window rather than left to the no-op inside, because this is a
    // per-solution walk of every variable and an enumeration takes it millions of times.
    if (eq_window_active())
        for (const auto & [var, val] : all_variables_and_values)
            overloaded{
                [&](const ConstantIntegerVariableID &) {}, //
                [&](const SimpleIntegerVariableID & var) { names_and_ids_tracker().note_permanent_eq_reference(var, val); },
                [&](const ViewOfIntegerVariableID & var) {
                    // A view is named through its underlying, which is the variable that can
                    // be windowed. A view that negates still deviews to an `==` condition.
                    auto under = deview(var == val);
                    names_and_ids_tracker().note_permanent_eq_reference(under.var, under.value);
                } //
            }
                .visit(var);

    _imp->proof << (optional_minimise_variable_and_value ? "soli" : "solx");

    WPBSum blocking_sum{};

    for (const auto & [var, val] : all_variables_and_values) {
        if (! optional_minimise_variable_and_value && _imp->assertion_level > AssertionLevel::Definitions)
            blocking_sum += 1_i * (var != val);

        overloaded{
            [&](const ConstantIntegerVariableID &) {}, //
            [&](const SimpleIntegerVariableID & var) {
                if (_imp->assertion_level > AssertionLevel::Definitions)
                    _imp->proof << " " << names_and_ids_tracker().bit_assignment_string_for(var, val);
                else
                    _imp->proof << " " << names_and_ids_tracker().pb_file_string_for(var == val);
            }, //
            [&](const ViewOfIntegerVariableID & var) {
                if (_imp->assertion_level > AssertionLevel::Definitions) {
                    // An unregistered view (e.g. an objective too wide to
                    // host its own bit vector) is witnessed through the
                    // underlying's bits at the deviewed value instead.
                    if (auto v_id = names_and_ids_tracker().find_view(var))
                        _imp->proof << " " << names_and_ids_tracker().bit_assignment_string_for(*v_id, val);
                    else
                        _imp->proof << " "
                                    << names_and_ids_tracker().bit_assignment_string_for(
                                           var.actual_variable, var.negate_first ? var.then_add - val : val - var.then_add);
                }
                else
                    _imp->proof << " " << names_and_ids_tracker().pb_file_string_for(deview(var == val));
            } //
        }
            .visit(var);
    }

    _imp->proof << ";\n";
    record_proof_line(advance_proof_line_number(), ProofLevel::Top);

    // Under OrderEncodingDeletion::Literals the objective-improvement constraint emitted
    // below (soli, either branch) names the objective variable's `id < incumbent` order
    // literal at ProofLevel::Top on every improving solution. Its definition sits at the
    // deep Current level the search reached this solution at, so the very next backtrack's
    // forget deletes it -- leaving this permanent Top line naming a deleted literal, which
    // VeriPB rejects. Hoist that order literal to Top first, exactly as the backtrack and
    // nogood paths hoist their guess/decision literals, so its definition survives every
    // later forget. A no-op in every other mode (and when the literal is already Top).
    if (optional_minimise_variable_and_value)
        visit(
            [&](const auto & id) {
                names_and_ids_tracker().hoist_live_order_literals_toward_level(
                    std::vector<Literal>{Literal{id < optional_minimise_variable_and_value->second}}, 0, OrderEncodingResidencyCause::SoliHoist);
            },
            optional_minimise_variable_and_value->first);

    if (optional_minimise_variable_and_value && _imp->assertion_level > AssertionLevel::Definitions)
        // soli and no links => have to assert the objective improving constraint
        visit(
            [&](const auto & id) {
                emit(AssertProofRule{}, WPBSum{} + 1_i * (id < optional_minimise_variable_and_value->second) >= 1_i, ProofLevel::Top,
                    AssertionAnnotation{.hint_name = hints::SoliImprove::hint_name});
            },
            optional_minimise_variable_and_value->first);
    else if (optional_minimise_variable_and_value)
        // normal soli, emit e line for trimmer
        visit(
            [&](const auto & id) {
                _imp->proof << "e ";
                emit_inequality_to(names_and_ids_tracker(), WPBSum{} + 1_i * id <= optional_minimise_variable_and_value->second - 1_i, _imp->proof);
                _imp->proof << ":" << relative_proof_line(_imp->proof_line, _imp->proof_line.number) << ";\n";

                emit_rup_proof_line(WPBSum{} + 1_i * (id < optional_minimise_variable_and_value->second) >= 1_i, ProofLevel::Top);
            },
            optional_minimise_variable_and_value->first);
    else if (_imp->assertion_level > AssertionLevel::Definitions) {
        // solx and no links => have to assert the blocking constraint
        emit(AssertProofRule{}, blocking_sum >= 1_i, ProofLevel::Top, AssertionAnnotation{.hint_name = hints::SolxBlock::hint_name});
    }
    // nothing needs done for solx below AssertionLevel::Links
}

auto ProofLogger::backtrack(const vector<Literal> & guesses) -> void
{
    // Under OrderEncodingDeletion::Literals the backtrack clause below names every
    // guess, and the forget_proof_level(depth+1) the caller runs straight after would
    // delete this frame's guess order-literal definition (emitted one level deeper).
    // Re-introducing it later fails VeriPB because the backtrack clause pins the atom
    // and the reification's falsify-witness collides with the pin. So hoist every
    // guess that is a real-variable order literal up to the current (backtrack) level
    // first: its definition then survives the forget and the clause never names a
    // to-be-deleted literal. A no-op in every other mode. (proof_level() is the
    // backtrack level here: solve.cc enters it before calling backtrack.)
    names_and_ids_tracker().hoist_live_order_literals_toward_level(guesses, proof_level(), OrderEncodingResidencyCause::GuessHoist);

    _imp->proof << "% backtracking\n";
    // The backtrack clause is `at least one guess is false': exactly a
    // reason-only reified line over the guesses, so route it through the
    // reified renderer, which negates each guess at the XLiteral level
    // rather than as a condition object.
    ReasonLiterals guesses_as_reason;
    guesses_as_reason.reserve(guesses.size());
    for (const auto & guess : guesses)
        guesses_as_reason.emplace_back(ProofLiteral{guess});
    auto assert_or_rup = (_imp->assertion_level >= AssertionLevel::Inferences) ? ProofRule(AssertProofRule{}) : ProofRule(RUPProofRule{});
    auto line = emit_under_reason(
        assert_or_rup, WPBSum{} >= 1_i, ProofLevel::Current, guesses_as_reason, AssertionAnnotation{.hint_name = hints::Backtrack::hint_name});

    // Remember the clause for the eq window's tidy: the parent frame is about to advance
    // its frontier past this refuted sibling, and this clause -- which names the sibling's
    // eq atom -- has to go with the atom. See Imp::last_backtrack_clause.
    if (eq_window_active() && ! guesses.empty())
        _imp->last_backtrack_clause = Imp::BacktrackClause{guesses.back(), line, proof_level()};
}

auto ProofLogger::bound_advances_active() const -> bool
{
    // Bound advances act on the proof only under the Literals order-encoding-deletion
    // mode with assertions off --- the same pairing every Literals-machinery guard uses.
    // Under None a Bound advance is treated exactly like Exclude (no advance emitted),
    // which is what keeps flag-off proofs byte-identical after the split family is tagged.
    return _imp->order_encoding_deletion == OrderEncodingDeletion::Literals && _imp->assertion_level == AssertionLevel::Off;
}

auto ProofLogger::emit_split_bound_advance(const vector<Literal> & guesses, const Literal & refuted_guess) -> void
{
    if (! bound_advances_active())
        return;

    // The frontier order literal is the refuted guess's own negation. For a split
    // sibling this is a single `ge` threshold: refuting `var <= v` (`var < v+1`) gives
    // `var >= v+1`; refuting `var > v` (`var >= v+1`) gives `var < v+1`. No hole-jumping
    // is needed in stage B --- the split refutes the half directly, so the advance clause
    // coincides with the refuted child's still-live backtrack clause and RUP is immediate.
    auto frontier = ! refuted_guess;

    // Hoist the frontier to this level (the sibling's backtrack level == the active
    // level) so the advance never names a to-be-deleted literal and the child's forget
    // keeps exactly the frontier resident behind the monotone bound. Usually a no-op:
    // the child's backtrack GuessHoist already placed the frontier here (it is named by
    // the refuted guess); re-run so the frontier is anchored even were that to change.
    names_and_ids_tracker().hoist_live_order_literals_toward_level(vector<Literal>{frontier}, proof_level(), OrderEncodingResidencyCause::GuessHoist);

    _imp->proof << "% bound advance\n";
    WPBSum advance;
    for (const auto & guess : guesses)
        advance += 1_i * ! guess;
    advance += 1_i * frontier;
    emit_rup_proof_line(move(advance) >= 1_i, ProofLevel::Current);
}

auto ProofLogger::eq_window_active() const -> bool
{
    return _imp->eq_window && bound_advances_active();
}

namespace
{
    // The `var == v` a windowed branch guess is, or nullopt for anything else (an order
    // guess, a range guess, a view, a proof-scaffolding literal). The window only ever
    // acts on an eq atom of a real variable.
    [[nodiscard]] auto windowed_eq_guess(const Literal & guess) -> optional<pair<SimpleIntegerVariableID, Integer>>
    {
        const auto * cond = std::get_if<IntegerVariableCondition>(&guess);
        if (! cond || cond->op != VariableConditionOperator::Equal)
            return nullopt;
        const auto * sid = std::get_if<SimpleIntegerVariableID>(&cond->var);
        if (! sid)
            return nullopt;
        return pair{*sid, cond->value};
    }
}

auto ProofLogger::mint_windowed_eq_guess(const Literal & guess) -> void
{
    if (! eq_window_active())
        return;
    auto eq = windowed_eq_guess(guess);
    if (! eq)
        return;

    // The scope is the only route to a deletable eq definition: it is open across this one
    // mint and nothing else, so every other caller in the solver keeps getting a permanent
    // definition without knowing lifetimes exist.
    NamesAndIDsTracker::WindowedEqScope scope{names_and_ids_tracker()};
    names_and_ids_tracker().need_direct_encoding_for(eq->first, eq->second);
}

auto ProofLogger::emit_eq_window_advance(const vector<Literal> & guesses, const Literal & refuted_guess, bool lower) -> void
{
    if (! eq_window_active())
        return;
    auto eq = windowed_eq_guess(refuted_guess);
    if (! eq)
        return;
    auto [var, v] = *eq;

    // Nothing was windowed here, so there is nothing behind the frontier to take out. The
    // advance exists only to be the standing bound the tidy reasons from, so emitting one
    // now would be cost with no matching saving -- and this is the *common* case on
    // eq-heavy models, where a constraint names the values the search branches on and
    // defines their atoms permanently long before the branch layer asks. Measured on
    // talent: 0 windowed atoms, so without this check the run paid +1.1 % proof and ~5 %
    // verify time for advances that could never be tidied behind.
    if (! names_and_ids_tracker().eq_literal_is_windowed(var, v))
        return;

    // The frontier the refutation of `var == v` establishes, given the standing bound this
    // node has already reached. Ascending: `var >= v` and `var != v` give `var >= v+1`.
    // Descending: `var <= v` and `var != v` give `var <= v-1`, i.e. `var < v`. Either way
    // it is one threshold, and the eq atom's reverse reification is the step that gets
    // there -- which is why the tidy below must not delete that definition first.
    Literal frontier = lower ? Literal{var >= v + 1_i} : Literal{var < v};

    // Anchor the frontier at this level, exactly as the split advance does: the definition
    // was minted here by mint_windowed_eq_guess, so this is normally a no-op, but a
    // frontier that already existed deeper (named by an earlier propagation) must not be
    // left for a deeper forget to delete under the standing advance.
    names_and_ids_tracker().hoist_live_order_literals_toward_level(vector<Literal>{frontier}, proof_level(), OrderEncodingResidencyCause::GuessHoist);

    _imp->proof << "% eq window advance\n";
    WPBSum advance;
    for (const auto & guess : guesses)
        advance += 1_i * ! guess;
    advance += 1_i * frontier;
    auto advance_line = emit_rup_proof_line(move(advance) >= 1_i, ProofLevel::Current);

    // ---- the per-iteration tidy ----
    // Everything below is deletion, and every step of it is ordered after the advance
    // above: the advance RUPs *through* eq(v)'s reverse reification, and deleting that
    // first is exactly what driver control D2c shows VeriPB rejecting.
    auto level = proof_level();

    // The previous step's advance is superseded by the one just emitted (the frontier only
    // moves one way), so it goes; the new one takes its place as this node's standing
    // bound. Nothing else can be relying on it: it was RUP from this node's own clauses,
    // and the node-close lemma re-derives what it needs from the standing one.
    auto & standing = _imp->standing_eq_advance[level];
    if (auto previous = standing.find(var.index); previous != standing.end()) {
        delete_proof_lines_at_level(vector<ProofLine>{previous->second}, level);
        previous->second = advance_line;
    }
    else
        standing.emplace(var.index, advance_line);

    // The refuted sibling's own backtrack clause names eq(v), so the atom is not
    // unreferenced -- and so not evictable -- until it goes too. This is the deletion the
    // naive "definition lines only" list omits, and it is confirmed necessary in the
    // validated driver proof.
    bool sibling_deleted = false;
    if (_imp->last_backtrack_clause && _imp->last_backtrack_clause->level == level && _imp->last_backtrack_clause->guess == refuted_guess) {
        delete_proof_lines_at_level(vector<ProofLine>{_imp->last_backtrack_clause->line}, level);
        _imp->last_backtrack_clause = nullopt;
        sibling_deleted = true;
    }

    // Now the atom itself. Skipped when the sibling clause survived, because a live clause
    // naming an evicted atom is exactly the stranded reference the mode must not create.
    // The eviction cannot refuse here -- an atom the hoist-out rule retained was already
    // turned away by the windowed check at the top, and nothing since then can have taken a
    // permanent reference -- but it is a refusing primitive rather than an asserting one,
    // so this reads as a condition rather than as an assumption.
    if (sibling_deleted && names_and_ids_tracker().evict_eq_literal(var, v)) {
        // The threshold the frontier has stepped over: ascending, ge(v) is now behind the
        // bound; descending, ge(v+1) is. Its definition and every chain clause naming it go,
        // and the chain is re-stitched over the hole. Refused (safely) when it is pinned by
        // a permanent atom; skipped when it is not resident at all, which the compact
        // boolean encoding's one-sided eq definitions can leave it.
        auto stepped_over = lower ? v : v + 1_i;
        if (names_and_ids_tracker().order_literal_is_live(var, stepped_over))
            names_and_ids_tracker().evict_order_literal(var, stepped_over, nullopt);
    }
}

auto ProofLogger::emit_learned_nogood(const vector<Literal> & decisions) -> ProofLine
{
    // The nogood clause lands at Top and survives the restart forget, but it names
    // the decision (branch-threshold) order literals, whose definitions live at
    // Current and would be deleted by that forget. Under OrderEncodingDeletion::Literals
    // hoist those decision literals to Top first, so they stay resident and the Top
    // nogood never references a deleted literal. Done before emitting the clause so the
    // hoisted def ids precede the clause id in the Top bucket. A no-op in other modes.
    names_and_ids_tracker().hoist_live_order_literals_toward_level(decisions, 0, OrderEncodingResidencyCause::NogoodHoist);

    // The same for any eq decision the nogood names: a windowed definition would be
    // deleted out from under this Top clause, so the hoist-out rule retains it instead.
    for (const auto & lit : decisions)
        if (const auto * cond = std::get_if<IntegerVariableCondition>(&lit))
            if (cond->op == VariableConditionOperator::Equal || cond->op == VariableConditionOperator::NotEqual)
                if (const auto * sid = std::get_if<SimpleIntegerVariableID>(&cond->var))
                    names_and_ids_tracker().note_permanent_eq_reference(*sid, cond->value);

    _imp->proof << "% learned nogood\n";
    WPBSum clause;
    for (const auto & lit : decisions)
        clause += 1_i * ! lit;
    return emit_rup_proof_line(move(clause) >= 1_i, ProofLevel::Top);
}

auto ProofLogger::end_proof() -> void
{
    _imp->proof << "end pseudo-Boolean proof;\n";

    // this is mostly for tests: we haven't necessarily destroyed the
    // Problem before running the verifier.
    _imp->proof << flush;

    // Single conclude funnel (every conclude_* variant ends here exactly once): dump the
    // order-encoding-deletion pin-apportionment diagnostic to stderr, if requested. A
    // no-op unless GCS_ORDER_ENCODING_STATS is set under OrderEncodingDeletion::Literals;
    // it writes only to stderr, never to the proof, so the .pbp is unaffected.
    names_and_ids_tracker().dump_order_encoding_stats();
}

auto ProofLogger::conclude_unsatisfiable(bool is_optimisation) -> void
{
    _imp->proof << "% asserting contradiction\n";
    auto assert_or_rup = _imp->assertion_level >= AssertionLevel::Inferences ? ProofRule(AssertProofRule{}) : ProofRule(RUPProofRule{});
    emit(assert_or_rup, WPBSum{} >= 1_i, ProofLevel::Top);
    _imp->proof << "output NONE;\n";
    if (is_optimisation)
        _imp->proof << "conclusion BOUNDS INF INF;\n";
    else
        _imp->proof << "conclusion UNSAT : " << relative_proof_line(_imp->proof_line, _imp->proof_line.number) << ";\n";
    end_proof();
}

auto ProofLogger::conclude_satisfiable() -> void
{
    _imp->proof << "output NONE;\n";
    _imp->proof << "conclusion SAT;\n";
    end_proof();
}

auto ProofLogger::conclude_complete_enumeration(Integer number_of_solutions) -> void
{
    _imp->proof << "rup >= 1 ;\n";
    record_proof_line(advance_proof_line_number(), ProofLevel::Top);
    _imp->proof << "output NONE;\n";
    _imp->proof << "conclusion ENUMERATION_COMPLETE " << number_of_solutions << " : -1 ;\n";
    end_proof();
}

auto ProofLogger::conclude_optimality(IntegerVariableID var, Integer value) -> void
{
    conclude_bounds(var, value, value);
}

auto ProofLogger::conclude_bounds(IntegerVariableID minimise_variable, Integer lower, Integer upper) -> void
{
    emit_rup_proof_line(WPBSum{} + 1_i * minimise_variable >= lower, ProofLevel::Top);
    _imp->proof << "output NONE;\n";
    _imp->proof << "conclusion BOUNDS " << lower << " " << upper << ";\n";
    end_proof();
}

auto ProofLogger::conclude_none() -> void
{
    _imp->proof << "output NONE;\n";
    _imp->proof << "conclusion NONE;\n";
    end_proof();
}

auto ProofLogger::infer(
    const Literal & lit, const Justification & why, const ReasonLiterals & reason, const optional<AssertionAnnotation> & annotation) -> void
{
    // A range conclusion on a view (folding views into the interval machinery is
    // deferred) or on a plain variable without a bits encoding (no order cuts to
    // reify against) cannot become a single range ("in") literal; fall back to one
    // per-value line each, which is still correct, just not coalesced. Every other
    // range conclusion rides the standard machinery: the condition's proof name is
    // the range literal, or the eq atom for width 1.
    if (const auto * cond = std::get_if<IntegerVariableCondition>(&lit))
        if (cond->op == VariableConditionOperator::NotInRange) {
            auto needs_per_value_fallback = overloaded{
                [&](const SimpleIntegerVariableID & v) { return ! names_and_ids_tracker().has_bit_representation(v); }, //
                [&](const ViewOfIntegerVariableID &) { return true; },                                                  //
                [&](const ConstantIntegerVariableID &) { return false; }                                                //
            }
                                                .visit(cond->var);
            if (needs_per_value_fallback) {
                for (Integer val = cond->value; val <= cond->upper_value; ++val)
                    infer(cond->var != val, why, reason);
                return;
            }
        }

    if (_imp->assertion_level > AssertionLevel::Inferences)
        return;

    if (_imp->assertion_level != AssertionLevel::Off) {
        // At AssertionLevel::Definitions we can assert some inferences and not others (since the needed constraints for the justifications will
        // still be present). At higher levels, we need to assert all inferences.
        // Explicit-steps justifications are JustifyExplicitly, handled by
        // infer_explicitly(); this variant only carries the plain ones, so the
        // annotation is just the one passed in.
        if (! is_literally_true(lit) && ! std::holds_alternative<NoJustificationNeeded>(why)) {
            emit_under_reason(AssertProofRule{}, _imp->unit_holds(lit), ProofLevel::Current, reason, annotation);
        }
        return;
    }

    overloaded{
        [&]([[maybe_unused]] const JustifyUsingRUP<NoHint> & j) {
            if (! is_literally_true(lit)) {
                emit_rup_proof_line_under_reason(reason, _imp->unit_holds(lit), ProofLevel::Current);
            }
        }, //
        [&]([[maybe_unused]] const AssertRatherThanJustifying & j) {
            if (! is_literally_true(lit)) {
                emit_under_reason(AssertProofRule{}, _imp->unit_holds(lit), ProofLevel::Current, reason);
            }
        },                                    //
        [&](const NoJustificationNeeded &) {} //
    }
        .visit(why);
}

auto ProofLogger::reify(const WPBSumLE & ineq, const HalfReifyOnConjunctionOf & half_reif) -> WPBSumLE
{
    return names_and_ids_tracker().reify(ineq, half_reif);
}

auto ProofLogger::emit_proof_line(const string & s, ProofLevel level, const optional<ProofLineLabel> & label) -> ProofLine
{
    log_stacktrace();
    write_indent();
    if (label)
        _imp->proof << *label << ' ';
    _imp->proof << s << '\n';
    auto result = record_proof_line(advance_proof_line_number(), level);
    return result;
}

auto ProofLogger::emit_proof_comment(const string & s) -> void
{
    _imp->proof << "% " << s << '\n';
}

auto ProofLogger::emit(const ProofRule & rule, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLevel level,
    const std::optional<AssertionAnnotation> & assertion_hint, const std::optional<ProofLineLabel> & label) -> ProofLine
{
    log_stacktrace();

    LineBufferLease lease{_imp->line_buffers, _imp->line_buffer_depth};
    auto & rule_line = lease.buffer();

    overloaded{
        [&](const RUPProofRule &) { rule_line += "rup "; },    //
        [&](const ImpliesProofRule &) { rule_line += "ia "; }, //
        [&](const AssertProofRule &) { rule_line += "a "; }    //
    }
        .visit(rule);

    // EnsureNames::Yes: a condition without a proof name yet gets introduced
    // as it is rendered, and its definition lines go out to the proof stream
    // ahead of this line, which is still sitting in the buffer.
    emit_inequality_to(names_and_ids_tracker(), ineq, rule_line, EnsureNames::Yes);

    overloaded{
        [&](const RUPProofRule & rule) {
            if (rule.lines) {
                rule_line += ": ";
                for (auto & line : *rule.lines) {
                    rule_line += relative_proof_line(line, _imp->proof_line.number);
                    rule_line += ' ';
                }
                rule_line += " ;";
            }
            else {
                rule_line += ";";
            }
        }, //
        [&](const ImpliesProofRule & rule) {
            if (rule.line) {
                rule_line += ": ";
                rule_line += relative_proof_line(*rule.line, _imp->proof_line.number);
                rule_line += "  ;";
            }
            else {
                rule_line += ";";
            }
        }, //
        [&](const AssertProofRule &) {
            if (assertion_hint) {
                append_annotation_to(rule_line, *assertion_hint);
            }
            rule_line += ";";
        } //
    }
        .visit(rule);

    auto line = emit_proof_line(rule_line, level, label);
    // Note: no automatic deview-derivation here. Runtime RUP/red emissions
    // happen many times per propagator inference and per-call deview
    // derivation explodes proof size on tests with many view-using
    // constraints. Callers that need the deview-form of a runtime-mitted
    // constraint use the explicit `*_then_deview` variant (see
    // `emit_rup_proof_line_under_reason_then_deview`).
    return line;
}

auto ProofLogger::emit_under_reason(const ProofRule & rule, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLevel level,
    const ReasonLiterals & reason, const std::optional<AssertionAnnotation> & assertion_hint) -> ProofLine
{
    log_stacktrace();

    LineBufferLease lease{_imp->line_buffers, _imp->line_buffer_depth};
    auto & rule_line = lease.buffer();

    overloaded{
        [&](const RUPProofRule &) { rule_line += "rup "; },    //
        [&](const ImpliesProofRule &) { rule_line += "ia "; }, //
        [&](const AssertProofRule &) { rule_line += "a "; }    //
    }
        .visit(rule);

    // EnsureNames::Yes: see emit() above.
    if (! reason.empty()) {
        emit_reified_inequality_to(names_and_ids_tracker(), ineq, reason, rule_line, EnsureNames::Yes);
    }
    else {
        emit_inequality_to(names_and_ids_tracker(), ineq, rule_line, EnsureNames::Yes);
    }

    overloaded{
        [&](const RUPProofRule & rule) {
            if (rule.lines) {
                rule_line += ": ";
                for (const auto & line : *rule.lines) {
                    rule_line += relative_proof_line(line, _imp->proof_line.number);
                    rule_line += ' ';
                }
                rule_line += " ;";
            }
            else {
                rule_line += ";";
            }
        }, //
        [&](const ImpliesProofRule & rule) {
            if (rule.line) {
                rule_line += ": ";
                rule_line += relative_proof_line(*rule.line, _imp->proof_line.number);
                rule_line += "  ;";
            }
            else {
                rule_line += ";";
            }
        }, //
        [&](const AssertProofRule &) {
            if (assertion_hint) {
                append_annotation_to(rule_line, *assertion_hint);
            }

            rule_line += ";";
        } //
    }
        .visit(rule);

    auto line = emit_proof_line(rule_line, level);
    // Note: see comment in `emit()` about why no auto-deview-derivation.
    return line;
}

auto ProofLogger::emit_rup_proof_line(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLevel level) -> ProofLine
{
    return emit(RUPProofRule{}, ineq, level);
}

auto ProofLogger::emit_rup_proof_line_under_reason(
    const ReasonLiterals & reason, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLevel level) -> ProofLine
{
    return emit_under_reason(RUPProofRule{}, ineq, level, reason);
}

auto ProofLogger::emit_rup_proof_line_under_reason_then_deview(
    const ReasonLiterals & reason, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLevel level) -> ProofLine
{
    auto v_form_line = emit_rup_proof_line_under_reason(reason, ineq, level);
    // emit_inequality_to negates the LE inequality to land in PB >= form.
    names_and_ids_tracker().derive_deviewed_form_for(v_form_line, ineq.lhs, /*le_half=*/true);
    return names_and_ids_tracker().deviewed_line_for(v_form_line);
}

auto ProofLogger::proof_level() -> int
{
    return _imp->active_proof_level;
}

auto ProofLogger::temporary_proof_level() -> int
{
    return _imp->active_proof_level + 1;
}

auto ProofLogger::enter_proof_level(int depth) -> void
{
    if (cmp_less_equal(_imp->proof_lines_by_level.size(), depth + 1))
        _imp->proof_lines_by_level.resize(depth + 2);
    _imp->active_proof_level = depth;
}

auto ProofLogger::forget_proof_level(int depth) -> void
{
    auto & lines = _imp->proof_lines_by_level.at(depth);
    // Emit deletions as *relative* (negative) ids so a constraint-count
    // difference between the solver's OPB and cake_pb_cp's re-derived OPB
    // doesn't misaddress them. VeriPB's id space is monotonic (deleted entries
    // are tombstoned), so every offset is taken against the same `current`.
    //
    // We keep `del range` rather than expanding to per-id `del id`, because a
    // recorded level can contain ids already deleted by a nested level: VeriPB's
    // `del range` skips already-deleted ids (get_undeleted), but a single
    // `del id` errors on them. The one wrinkle: `del range from to` is half-open,
    // so deleting *through* the most recent line (`u == current`) needs an
    // exclusive upper of `current + 1`, which has no negative encoding (it would
    // be `0`). In that case we range up to but excluding the top line and delete
    // the top with `del id -1` (which is the just-emitted line, never already
    // deleted). A `del range -k 0` form upstream would remove this special case.
    auto current = _imp->proof_line.number;
    auto rel = [&](long long absolute) { return absolute - current - 1; };
    for (const auto & [l, u] : lines.each_interval()) {
        write_indent();
        if (l == u)
            _imp->proof << "del id " << rel(l) << ";\n";
        else if (u < current)
            _imp->proof << "del range " << rel(l) << " " << rel(u + 1) << ";\n";
        else {
            // u == current: peel the top line out of the (otherwise zero-upper) range.
            _imp->proof << "del range " << rel(l) << " " << rel(u) << ";\n";
            write_indent();
            _imp->proof << "del id " << rel(u) << ";\n";
        }
    }
    lines.clear();

    // Keep the tracker's live order-link structure in sync with the deletions just
    // emitted: any order-encoding chain links recorded at this level have now been
    // del'd, so drop them from the live set so a later need_gevar re-emits them if
    // required. A cheap no-op when the order-link deletion mode is off.
    names_and_ids_tracker().forget_order_links_at_level(depth);

    // The eq window's per-node records for this level went with those deletions. Dropping
    // them is not tidiness: the next node at this depth reuses the level number, and a
    // stale line would be `del`'d a second time, which VeriPB errors on (unlike the
    // `del range` above, a `del id` does not skip an already-deleted line).
    if (! _imp->standing_eq_advance.empty())
        _imp->standing_eq_advance.erase(depth);
    if (_imp->last_backtrack_clause && _imp->last_backtrack_clause->level >= depth)
        _imp->last_backtrack_clause = nullopt;
}

auto ProofLogger::move_proof_lines_to_level(const vector<ProofLine> & lines, int from_level, int target_level) -> void
{
    if (from_level == target_level)
        return;

    auto deepest = max(from_level, target_level);
    if (cmp_less_equal(_imp->proof_lines_by_level.size(), deepest + 1))
        _imp->proof_lines_by_level.resize(deepest + 2);

    // Move each concrete line id from the source bucket to the target bucket
    // (labels have no numeric id and are skipped). A hoisted definition can carry
    // a smaller id than lines already resident in the target bucket -- several
    // guess literals hoisted to one level need not arrive in id order, and a
    // hoist-to-Top lands a mid-range def id into a bucket whose tail is a large
    // learned-nogood clause -- so the general-position IntervalSet::insert is used
    // rather than insert_at_end, keeping the bucket sorted, disjoint and merged
    // whatever order the moves happen in.
    auto & from = _imp->proof_lines_by_level.at(from_level);
    auto & to = _imp->proof_lines_by_level.at(target_level);
    for (const auto & l : lines)
        if (auto n = std::get_if<ProofLineNumber>(&l)) {
            from.erase(n->number);
            to.insert(n->number);
        }
}

auto ProofLogger::delete_proof_lines_at_level(const vector<ProofLine> & lines, int level) -> void
{
    auto & bucket = _imp->proof_lines_by_level.at(level);
    // Same relative (negative) encoding forget_proof_level uses, and for the same reason:
    // a constraint-count difference between our OPB and cake_pb_cp's re-derived one would
    // misaddress an absolute id. `current` is taken once -- a `del` is not a numbered
    // line, so emitting these does not move it.
    auto current = _imp->proof_line.number;
    for (const auto & l : lines)
        if (const auto * n = std::get_if<ProofLineNumber>(&l)) {
            bucket.erase(n->number);
            write_indent();
            _imp->proof << "del id " << (n->number - current - 1) << ";\n";
        }
}

auto ProofLogger::hoist_literal_to_level(const SimpleIntegerVariableID & id, Integer v, int target_level) -> void
{
    names_and_ids_tracker().hoist_order_literal_to_level(id, v, target_level);
}

auto ProofLogger::hoist_literal_to_top(const SimpleIntegerVariableID & id, Integer v) -> void
{
    names_and_ids_tracker().hoist_order_literal_to_top(id, v);
}

auto ProofLogger::start_proof(const ProofModel & model) -> void
{
    try {
        _imp->proof.exceptions(ios::failbit | ios::badbit);
        _imp->proof_stream_buffer.resize(1024 * 1024);
        _imp->proof.rdbuf()->pubsetbuf(_imp->proof_stream_buffer.data(), _imp->proof_stream_buffer.size());
        _imp->proof.open(_imp->proof_file, ios::out);
        _imp->proof << "pseudo-Boolean proof version 3.0\n";
        // No `f` rule: VeriPB 3.0 loads the formula implicitly, and omitting the
        // explicit count means cake_pb_cp's re-derived OPB is allowed to have a
        // different number of constraints than the solver's own (e.g. cake emits
        // two bound lines for a binary variable where the solver emits one). All
        // constraint references are relative (see relative_proof_line), so the
        // differing count doesn't misaddress them.
    }
    catch (const ios_base::failure &) {
        throw ProofError{"Error writing proof file to '" + _imp->proof_file + "'"};
    }
    // The solver's own constraint count still seeds the proof-line counter so its
    // derived-line numbering is internally consistent; relativisation cancels any
    // difference from cake's count at reference time.
    _imp->proof_line.number += model.number_of_constraints().number;
}

auto ProofLogger::record_proof_line(ProofLineNumber line, ProofLevel level) -> ProofLineNumber
{
    switch (level) {
    case ProofLevel::Top: _imp->proof_lines_by_level.at(0).insert_at_end(line.number); break;
    case ProofLevel::Current: _imp->proof_lines_by_level.at(_imp->active_proof_level).insert_at_end(line.number); break;
    case ProofLevel::Temporary: _imp->proof_lines_by_level.at(_imp->active_proof_level + 1).insert_at_end(line.number); break;
    }

    return line;
}

auto ProofLogger::names_and_ids_tracker() -> NamesAndIDsTracker &
{
    return _imp->tracker;
}

auto ProofLogger::names_and_ids_tracker() const -> const NamesAndIDsTracker &
{
    return _imp->tracker;
}

auto ProofLogger::emit_subproofs(const map<ProofGoal, Subproof> & subproofs)
{
    _imp->proof << " : subproof\n";
    advance_proof_line_number();
    _imp->current_indent += INDENT_WIDTH;
    for (const auto & [proofgoal, proof] : subproofs) {
        // A ProofLine proofgoal (naming a specific constraint, as circuit does)
        // is a reference and must be relativised like any other -- but VeriPB
        // resolves the `proofgoal <id>` argument against the constraint count
        // *before* the proofgoal line consumes its own id (the `: subproof` line
        // above is already counted, this proofgoal line is not yet). So relativise
        // against the counter captured before this advance, not after. (Verified
        // empirically: a goal at absolute id N with the counter at N+1 here must
        // be emitted as -2, i.e. N - (N+1) - 1.) A "#n" index goal is a plain
        // string and passes through.
        auto goal_base = _imp->proof_line.number;
        advance_proof_line_number();
        write_indent();
        _imp->proof << "proofgoal ";
        visit(overloaded{
                  [&](const ProofLine & l) { _imp->proof << relative_proof_line(l, goal_base); }, //
                  [&](const string & s) { _imp->proof << s; }                                     //
              },
            proofgoal);
        _imp->proof << "\n";
        _imp->current_indent += INDENT_WIDTH;
        proof(*this);
        _imp->current_indent -= INDENT_WIDTH;
        write_indent();
        _imp->proof << "qed;\n";
    }
    _imp->current_indent -= INDENT_WIDTH;
    write_indent();
    _imp->proof << "qed;\n";
}

auto ProofLogger::get_current_proof_line() -> ProofLineNumber
{
    return _imp->proof_line;
}

auto ProofLogger::emit_red_proof_line(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq,
    const std::vector<std::pair<ProofLiteralOrFlag, ProofLiteralOrFlag>> & witness, ProofLevel level,
    const std::optional<std::map<ProofGoal, Subproof>> & subproofs) -> ProofLine
{
    names_and_ids_tracker().need_all_proof_names_in(ineq.lhs);

    log_stacktrace();
    write_indent();
    _imp->proof << "red ";
    emit_inequality_to(names_and_ids_tracker(), ineq, _imp->proof);

    _imp->proof << " :";
    for (auto & [f, t] : witness)
        _imp->proof << " " << witness_literal(names_and_ids_tracker(), f) << " -> " << witness_literal(names_and_ids_tracker(), t);

    if (subproofs)
        emit_subproofs(subproofs.value());
    else
        _imp->proof << ";\n";

    return record_proof_line(advance_proof_line_number(), level);
}

auto ProofLogger::introduce_bits_of(
    const SumOf<Weighted<PseudoBooleanTerm>> & linear_form, SimpleOrProofOnlyIntegerVariableID target, ProofLevel level) -> pair<ProofLine, ProofLine>
{
    // Wietze Koops's construction: walk target's bits from the top, defining each
    // bit e_k as the reified `running-remainder >= 2^k` via a single red whose
    // witness is just e_k -> 1 (upper half) / e_k -> 0 (lower half). The final
    // (k = 0) pair is BinEnc(target) >= form (end_ge) / BinEnc(target) <= form
    // (end_le).
    //
    // A signed target (negative bit coefficient -2^S) is the same construction
    // shifted by 2^S: BinEnc + 2^S = 2^S * ~sign + Sigma 2^j e_j is an unsigned
    // bit sum whose top bit is the negated sign literal, so define ITS bits as
    // equal to form + 2^S. Every inequality just gains the constant 2^S on the
    // form side, and after veripb's literal normalisation the emitted lines ARE
    // the unsigned lines of the shifted form (issue #553). The returned pair
    // still reads BinEnc(target) >= form / <= form.
    //
    // Why every redundancy goal discharges: veripb autoproves a proofgoal by a
    // single-constraint implication check against the database before trying
    // RUP. Each middle step's goal is the previous step's line (or, for a le
    // red's extra goal on that step's ge line, implied by ~C with the current
    // bit weakened away), so only the two TOP-step goals --- form <= (top-half
    // max) for the first ge and form >= (0, or -2^S when signed) for the first
    // le --- have no earlier line to lean on. Unit propagation alone does NOT
    // reliably close those two (it stalls whenever an operand's bit encoding
    // overhangs the target's, e.g. a start in [-17, -16] whose encoding spans
    // [-32, 31] against an end proxy spanning [-8, 7]), so we first derive the
    // form's own bound lines by pol over the operands' OPB bound rows; the
    // implication check then discharges the top goals from those, making the
    // construction shape-independent.
    auto m = names_and_ids_tracker().num_bits(target).raw_value;

    // A [0, 0] target now has zero bits (the empty sum, identically zero), for
    // which the construction below would return default-constructed lines. No
    // caller can currently supply one (cumulative's end proxy could only span
    // [0, 0] if both operands were constant, and then no proxy is made), and
    // the degenerate pair it would need (`form <= 0` / `form >= 0`, exactly
    // the two pol-derived bound lines below) should be written and tested when
    // a real caller appears, not speculatively.
    if (0 == m)
        throw ProofError{"introduce_bits_of does not support a zero-width target"};

    // The form's own bound lines: Sigma c_i * (operand's lower row) for the
    // lower (using the upper row where c_i < 0), and symmetrically for the
    // upper. Terms without tracked bound rows (views, flags, literals ---
    // none of which any current caller passes) leave the top goals to plain
    // RUP as before; constants fold into the goals' right-hand sides and
    // need no row.
    PolBuilder form_lower_bound, form_upper_bound;
    bool have_bound_rows = false, bound_rows_derivable = true;
    for (const auto & term : linear_form.terms) {
        auto add_rows_for = [&](const SimpleOrProofOnlyIntegerVariableID & id) {
            auto rows = names_and_ids_tracker().bound_rows(id);
            if ((! rows) || 0_i == term.coefficient) {
                bound_rows_derivable = bound_rows_derivable && rows.has_value();
                return;
            }
            auto & [lower_row, upper_row] = *rows;
            if (term.coefficient > 0_i) {
                form_lower_bound.add(lower_row, term.coefficient);
                form_upper_bound.add(upper_row, term.coefficient);
            }
            else {
                form_lower_bound.add(upper_row, -term.coefficient);
                form_upper_bound.add(lower_row, -term.coefficient);
            }
            have_bound_rows = true;
        };
        overloaded{
            [&](const ProofLiteral &) { bound_rows_derivable = false; },            //
            [&](const ProofFlag &) { bound_rows_derivable = false; },               //
            [&](const ProofBitVariable &) { bound_rows_derivable = false; },        //
            [&](const ProofOnlySimpleIntegerVariableID & id) { add_rows_for(id); }, //
            [&](const IntegerVariableID & var) {
                overloaded{
                    [&](const SimpleIntegerVariableID & id) { add_rows_for(id); },         //
                    [&](const ConstantIntegerVariableID &) {},                             //
                    [&](const ViewOfIntegerVariableID &) { bound_rows_derivable = false; } //
                }
                    .visit(var);
            } //
        }
            .visit(term.variable);
    }
    if (bound_rows_derivable && have_bound_rows) {
        form_lower_bound.emit(*this, level);
        form_upper_bound.emit(*this, level);
    }

    // 2^S for a signed target (whose sign bit occupies position 0 of the bits
    // vector, with the value bit of weight 2^j at position j + 1), else 0.
    auto shift = -names_and_ids_tracker().negative_bit_coefficient(target);
    if (0_i != shift && shift != power2(Integer{m - 1}))
        throw ProofError{"introduce_bits_of: signed target's negative bit coefficient does not match its bit count"};

    // The bit of weight 2^k in the (shifted) sum.
    auto bit_of_weight = [&](Integer k) -> ProofBitVariable {
        if (0_i == shift)
            return ProofBitVariable{target, k, true};
        else if (k.raw_value == m - 1)
            return ProofBitVariable{target, 0_i, false}; // ~sign as the top bit
        else
            return ProofBitVariable{target, k + 1_i, true};
    };

    pair<ProofLine, ProofLine> bounds;
    SumOf<Weighted<PseudoBooleanTerm>> bitsum; // Sigma_{j > k} 2^j e_j, grows as k descends
    for (long long kk = m - 1; kk >= 0; --kk) {
        Integer k{kk};
        auto bit = bit_of_weight(k);
        bitsum += power2(k) * bit; // now Sigma_{j >= k}

        // expr = (running bit sum) - (linear form)
        auto expr = bitsum;
        for (const auto & term : linear_form.terms)
            expr += Weighted<PseudoBooleanTerm>{-term.coefficient, term.variable};

        // The witness must map the underlying proof variable, so when the top
        // bit is ~sign, setting it means mapping sign to the complement.
        ProofBitVariable witness_var{target, bit.position, true};
        ProofLiteralOrFlag bit_on = bit.positive ? ProofLiteralOrFlag{TrueLiteral{}} : ProofLiteralOrFlag{FalseLiteral{}};
        ProofLiteralOrFlag bit_off = bit.positive ? ProofLiteralOrFlag{FalseLiteral{}} : ProofLiteralOrFlag{TrueLiteral{}};

        // upper: Sigma_{j >= k} 2^j e_j + (2^k - 1) >= form + shift  <=>  expr >= 1 - 2^k + shift
        auto ge = emit_red_proof_line(expr >= 1_i - power2(k) + shift, {{witness_var, bit_on}}, level);
        // lower: Sigma_{j >= k} 2^j e_j <= form + shift  <=>  expr <= shift
        auto le = emit_red_proof_line(expr <= shift, {{witness_var, bit_off}}, level);
        if (kk == 0)
            bounds = {ge, le};
    }
    return bounds;
}

auto ProofLogger::emit_red_proof_lines_forward_reifying(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLiteralOrFlag reif,
    ProofLevel level, const optional<map<ProofGoal, Subproof>> & subproofs) -> ProofLine
{
    log_stacktrace();

    names_and_ids_tracker().need_all_proof_names_in(ineq.lhs);
    write_indent();
    _imp->proof << "red ";
    emit_inequality_to(names_and_ids_tracker(), reify(ineq, {{reif}}), _imp->proof);
    _imp->proof << " : " << witness_literal(names_and_ids_tracker(), reif) << " -> 0";
    if (subproofs)
        emit_subproofs(subproofs.value());
    else
        _imp->proof << ";\n";

    return record_proof_line(advance_proof_line_number(), level);
}

auto ProofLogger::emit_red_proof_lines_reverse_reifying(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLiteralOrFlag reif,
    ProofLevel level, const optional<map<ProofGoal, Subproof>> & subproofs) -> ProofLine
{
    log_stacktrace();

    names_and_ids_tracker().need_all_proof_names_in(ineq.lhs);
    auto negated_ineq = ineq.lhs >= ineq.rhs + 1_i;
    write_indent();
    _imp->proof << "red ";
    emit_inequality_to(names_and_ids_tracker(), reify(negated_ineq, {{! reif}}), _imp->proof);
    _imp->proof << " : " << witness_literal(names_and_ids_tracker(), reif) << " -> 1";
    if (subproofs)
        emit_subproofs(subproofs.value());
    else
        _imp->proof << ";\n";
    return record_proof_line(advance_proof_line_number(), level);
}

auto ProofLogger::emit_red_proof_lines_reifying(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLiteralOrFlag reif, ProofLevel level)
    -> pair<ProofLine, ProofLine>
{
    log_stacktrace();

    auto forward_result = emit_red_proof_lines_forward_reifying(ineq, reif, level);
    auto reverse_result = emit_red_proof_lines_reverse_reifying(ineq, reif, level);
    return pair{forward_result, reverse_result};
}

auto ProofLogger::create_proof_flag_reifying(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, const string & name, ProofLevel level)
    -> tuple<ProofFlag, ProofLine, ProofLine>
{
    auto flag = create_proof_flag(name);
    auto lines = emit_red_proof_lines_reifying(ineq, flag, level);
    return tuple{flag, lines.first, lines.second};
}

auto ProofLogger::create_proof_flag(const string & name) -> ProofFlag
{
    return names_and_ids_tracker().create_proof_flag(name);
}

auto ProofLogger::delete_range(ProofLine from, ProofLine up_to) -> void
{
    _imp->proof << "del range " << relative_proof_line(from, _imp->proof_line.number) << " " << relative_proof_line(up_to, _imp->proof_line.number)
                << ";\n";
}

auto ProofLogger::write_indent() -> void
{
    for (auto _ = _imp->current_indent; _--;) {
        _imp->proof << ' ';
    }
}

auto ProofLogger::get_assertion_level() -> AssertionLevel
{
    return _imp->assertion_level;
}
