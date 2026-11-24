#include <cstdio>
#include <gcs/exception.hh>
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

#include <cstddef>
#include <cstdlib>
#include <deque>
#include <fstream>
#include <optional>
#include <sstream>
#include <type_traits>

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
using std::optional;
using std::ostream;
using std::pair;
using std::string;
using std::stringstream;
using std::to_string;
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

    // The `soli` line, and the objective-improving atom line beside it, for the
    // most recent solution of an optimisation problem. Kept so that the next,
    // strictly better solution can delete both: see ProofLogger::solution.
    optional<pair<ProofLine, ProofLine>> previous_soli_lines;

    string proof_file;
    // A proof is many short lines; the default stream buffer makes for a
    // write syscall every few KB, which shows up at this volume. Installed
    // via pubsetbuf before open in start_proof.
    //
    // Declared before `proof`, and that order is load-bearing: members are
    // destroyed in reverse, and ~fstream closes the file, which flushes
    // whatever is still buffered. If the buffer went first, that final write
    // would read freed memory. It only bites when the last flush is the
    // destructor's --- end_proof() flushes explicitly, so a proof that runs to
    // completion never notices --- but a solve that throws part-way through
    // does, and silently lost the whole unflushed tail of the .pbp.
    vector<char> proof_stream_buffer;
    fstream proof;
    int current_indent = 0;
    // How many `subproof` blocks deep we are. Constraints derived inside one do
    // not survive its `qed;`, so a line recorded at Top from in there must not
    // be moved to core: `core id` inside a subproof addresses something the
    // outer database has never seen.
    int subproof_depth = 0;
    AssertionLevel assertion_level;

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

    // What assume_current_bounds recorded about one variable: its bounds at
    // the time, and which of `x >= lower`, `x < upper + 1` and `x = lower`
    // (when fixed) a reason may leave out. A side that had moved off its
    // declared bound is one the search derived, and gets a unit line of its
    // own the first time a reason leaves it out. A side still at its declared
    // bound may be left out once order_literal_holds_at_top says so, and its
    // unit, if any, is the boundary pin. That answer can change from no to
    // yes, because the pin is written when the bound's atom is first created,
    // which is often the first time a reason names it. So a declared side
    // whose atom does not exist yet stays a candidate (lower_maybe) and is
    // asked again when a reason names it; once its atom exists without a pin
    // the answer is final. Deciding as much as possible up front keeps the
    // check per reason literal to a compare, which matters: it runs for every
    // literal of every reason.
    struct AssumedBounds
    {
        Integer lower = 0_i, upper = -1_i;
        bool lower_ok = false, upper_ok = false, equal_ok = false;
        bool lower_maybe = false, upper_maybe = false;
        bool lower_moved = false, upper_moved = false;
        optional<ProofLine> lower_unit, upper_unit, equal_unit;
    };

    // One assume_current_bounds call, indexed by SimpleIntegerVariableID. It
    // lasts until its proof level is forgotten, since the units it writes and
    // the lines they are derived from live at that level.
    struct AssumptionFrame
    {
        int level;
        vector<AssumedBounds> by_variable;
        vector<ReasonLiteralFilter::Candidates> candidates;
    };

    vector<AssumptionFrame> assumption_frames;

    // How many KeepAssumedReasonLiterals are alive.
    int keep_assumed_reason_literals = 0;

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

auto ProofLogger::solution(
    const vector<pair<IntegerVariableID, Integer>> & all_variables_and_values, const optional<pair<Objective, Integer>> & objective_and_value) -> void
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

    _imp->proof << (objective_and_value ? "soli" : "solx");

    WPBSum blocking_sum{};

    for (const auto & [var, val] : all_variables_and_values) {
        if (! objective_and_value && _imp->assertion_level > AssertionLevel::Definitions)
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
                    // An unregistered view is witnessed through the
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

    // Both rules put the constraint they derive into VeriPB's *core* set, where
    // it stays until something explicitly takes it away, and where it is a drag
    // on every later unit propagation. Which is to say: both want deleting, and
    // they want deleting in different ways.
    //
    // A `solx` blocking clause is only needed while the search is still
    // somewhere that could rediscover the same solution, so it is recorded at
    // the *current* proof level. The backtrack out of the leaf that found the
    // solution then deletes it along with everything else at that level, and
    // that frame's backtrack clause --- which we have moved to core for exactly
    // this purpose --- is what passes VeriPB's deletion check for it.
    //
    // A `soli` objective-improving constraint has to outlive its subtree: it is
    // the incumbent bound, and every later branch anywhere in the tree prunes
    // against it. So it stays at Top and is deleted below instead, at the point
    // where a strictly better one has replaced it.
    // A `soli` constraint stays at Top and is deleted below, when a better one
    // replaces it. So does a `solx` blocking clause in a proof that cannot
    // delete it: above AssertionLevel::Definitions the encoding is not written
    // down, so nothing could carry the clause's preserved-variable assignment
    // across to the atoms a backtrack clause is written in, and the deletion
    // check would have to fail.
    auto solution_level = (objective_and_value || _imp->assertion_level > AssertionLevel::Definitions) ? ProofLevel::Top : ProofLevel::Current;
    auto solution_line = record_proof_line(advance_proof_line_number(), solution_level);

    // The objective-improving constraint's line, and the atom line beside it,
    // both of which the next solution supersedes.
    optional<pair<ProofLine, ProofLine>> soli_lines;

    if (objective_and_value) {
        // What the `soli` has just made VeriPB add: the posted objective,
        // strictly better than this solution's value. The atom says it in
        // literals, and the next solution supersedes both.
        const auto & [objective, value] = *objective_and_value;
        auto improving = objective.direction == ObjectiveDirection::Minimise ? objective.variable < value : objective.variable >= value + 1_i;

        if (_imp->assertion_level > AssertionLevel::Definitions) {
            // soli and no links => have to assert the objective improving constraint
            auto atom_line = emit(AssertProofRule{}, WPBSum{} + 1_i * improving >= 1_i, ProofLevel::Top,
                AssertionAnnotation{.hint_name = hints::SoliImprove::hint_name});
            soli_lines.emplace(solution_line, atom_line);
        }
        else {
            // Normal soli: an `e` line for the trimmer, restating the
            // constraint VeriPB has just derived from the objective line, so
            // spelled the way that line was, over the objective's linear form
            // (issue #1206).
            auto [variable, coefficient, constant] = objective_linear_form(objective.variable);
            _imp->proof << "e ";
            if (objective.direction == ObjectiveDirection::Minimise)
                emit_inequality_to(names_and_ids_tracker(), WPBSum{} + coefficient * variable <= value - 1_i - constant, _imp->proof);
            else
                emit_inequality_to(names_and_ids_tracker(), WPBSum{} + coefficient * variable >= value + 1_i - constant, _imp->proof);
            _imp->proof << ":" << relative_proof_line(_imp->proof_line, _imp->proof_line.number) << ";\n";

            auto atom_line = emit_rup_proof_line(WPBSum{} + 1_i * improving >= 1_i, ProofLevel::Top);
            soli_lines.emplace(solution_line, atom_line);
        }
    }
    else if (_imp->assertion_level > AssertionLevel::Definitions) {
        // solx and no links => have to assert the blocking constraint. At the
        // same level as the solx itself: it is the same fact said in literals
        // rather than in bits, so it goes when the solx goes, and stays when the
        // solx stays.
        emit(AssertProofRule{}, blocking_sum >= 1_i, solution_level, AssertionAnnotation{.hint_name = hints::SolxBlock::hint_name});
    }
    // nothing needs done for solx below AssertionLevel::Links

    if (soli_lines) {
        // The constraint we have just added is `objective <= value - 1` for a
        // strictly smaller value than the one it replaces, so it implies the
        // older constraint outright and VeriPB's deletion check for the older
        // one is a plain RUP against what remains of the core. Likewise for the
        // `objective < value` atom beside it, which is merely derived and so
        // costs nothing to delete. Without this the proof carries one live
        // objective bound per solution found rather than one in total.
        if (_imp->previous_soli_lines)
            delete_proof_lines({_imp->previous_soli_lines->first, _imp->previous_soli_lines->second});
        _imp->previous_soli_lines = soli_lines;
    }
}

auto ProofLogger::backtrack(const vector<Literal> & guesses, ClauseSet destination) -> void
{
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

    // The caller asks for core when the level it is about to forget can hold a
    // blocking clause. Whether such a clause is deletable at all turns on the
    // assertion level, which is the logger's to know: see solution() above.
    if (ClauseSet::Core == destination && _imp->assertion_level <= AssertionLevel::Definitions)
        move_to_core(line);
}

auto ProofLogger::move_to_core(const ProofLine & line) -> void
{
    // `core id` is unconditional --- anything the proof has derived could have
    // been derived into the core in the first place --- and does not itself
    // produce a constraint, so the line counter does not move.
    write_indent();
    _imp->proof << "core id " << relative_proof_line(line, _imp->proof_line.number) << ";\n";
}

auto ProofLogger::emit_learned_nogood(const vector<Literal> & decisions, ClauseSet destination) -> ProofLine
{
    _imp->proof << "% learned nogood\n";
    WPBSum clause;
    for (const auto & lit : decisions)
        clause += 1_i * ! lit;
    auto line = emit_rup_proof_line(move(clause) >= 1_i, ProofLevel::Top);

    // A nogood is something the search derived rather than part of any
    // variable's encoding, so nothing puts it in core on its behalf.
    if (ClauseSet::Core == destination && _imp->assertion_level <= AssertionLevel::Definitions)
        move_to_core(line);

    return line;
}

auto ProofLogger::end_proof() -> void
{
    _imp->proof << "end pseudo-Boolean proof;\n";

    // this is mostly for tests: we haven't necessarily destroyed the
    // Problem before running the verifier.
    _imp->proof << flush;
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

auto ProofLogger::conclude_optimality(const Objective & objective, Integer value) -> void
{
    conclude_bounds(objective, value, value);
}

auto ProofLogger::conclude_bounds(const Objective & objective, Integer root_bound, Integer incumbent) -> void
{
    // Over the objective's linear form, as the objective line was written.
    // VeriPB treats a `max:` as the minimisation of its negation, and states
    // its bounds that way, so for a maximisation the conclusion's bounds are
    // the negated posted ones.
    auto [variable, coefficient, constant] = objective_linear_form(objective.variable);
    if (objective.direction == ObjectiveDirection::Minimise) {
        emit_rup_proof_line(WPBSum{} + coefficient * variable >= root_bound - constant, ProofLevel::Top);
        _imp->proof << "output NONE;\n";
        _imp->proof << "conclusion BOUNDS " << root_bound << " " << incumbent << ";\n";
    }
    else {
        emit_rup_proof_line(WPBSum{} + coefficient * variable <= root_bound - constant, ProofLevel::Top);
        _imp->proof << "output NONE;\n";
        _imp->proof << "conclusion BOUNDS " << -root_bound << " " << -incumbent << ";\n";
    }
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
    // A range conclusion about a variable with no bits encoding has no order cuts to
    // reify against, so it cannot become a single range ("in") literal; fall back to
    // one per-value line each, which is still correct, just not coalesced. Every
    // other range conclusion, views included, rides the standard machinery: the
    // condition's proof name is the range literal, or the eq atom for width 1.
    if (const auto * cond = std::get_if<IntegerVariableCondition>(&lit))
        if (cond->op == VariableConditionOperator::NotInRange)
            if (! names_and_ids_tracker().can_represent_range_literal_for(cond->var)) {
                for (Integer val = cond->value; val <= cond->upper_value; ++val)
                    infer(cond->var != val, why, reason);
                return;
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

// Leaves out of a reason the literals assume_current_bounds made units of.
// With hinted set, the line is a hinted RUP, which propagates only over its
// hints, so a literal is left out only if there is a unit line to add to them.
class ProofLogger::AssumedReasonLiteralFilter : public ReasonLiteralFilter
{
private:
    ProofLogger & _logger;
    Imp::AssumptionFrame & _frame;
    bool _hinted;

    // may_write: the bound was moved by the search, so its unit is ours to
    // write. Otherwise it is a declared bound, whose unit is the boundary pin
    // if there is one; unit propagation needs no line for it, but a hinted RUP
    // needs a line to cite.
    auto use(optional<ProofLine> & unit, bool may_write, const VariableConditionFrom<SimpleIntegerVariableID> & cond) -> bool
    {
        if (! unit) {
            if (! may_write)
                return ! _hinted;
            // A line derived inside a subproof does not outlive its `qed`.
            if (_logger._imp->subproof_depth > 0)
                return false;
            unit = _logger.emit_assumed_unit(cond, _frame.level);
        }
        if (_hinted)
            extra_hints.push_back(*unit);
        return true;
    }

    // A declared side not yet known to be omittable: ask the tracker again.
    // Once the bound's atom exists without a pin it never will be, so stop
    // offering it as a candidate.
    auto confirm(
        bool & ok, bool & maybe, optional<ProofLine> & unit, const VariableConditionFrom<SimpleIntegerVariableID> & cond, Integer & candidate) -> bool
    {
        if (! maybe)
            return false;
        auto & tracker = _logger.names_and_ids_tracker();
        if (tracker.order_literal_holds_at_top(cond.var, cond.op, cond.value)) {
            ok = true;
            maybe = false;
            // The pin is keyed by the ge cut, which for `x < ub + 1` is ub + 1:
            // the condition's value either way.
            unit = tracker.boundary_pin_line(cond.var, cond.value);
            return true;
        }
        if (tracker.find_xliteral_for(cond)) {
            maybe = false;
            candidate = no_value;
        }
        return false;
    }

public:
    vector<ProofLine> extra_hints;

    AssumedReasonLiteralFilter(ProofLogger & logger, Imp::AssumptionFrame & frame, bool hinted) :
        ReasonLiteralFilter(frame.candidates), _logger(logger), _frame(frame), _hinted(hinted)
    {
    }

    [[nodiscard]] auto omit(const VariableConditionFrom<SimpleIntegerVariableID> & cond) -> bool override
    {
        if (cond.var.index >= _frame.by_variable.size())
            return false;
        auto & b = _frame.by_variable[cond.var.index];

        switch (cond.op) {
            using enum VariableConditionOperator;
        case GreaterEqual:
            if (cond.value != b.lower)
                return false;
            if (! b.lower_ok && ! confirm(b.lower_ok, b.lower_maybe, b.lower_unit, cond, _frame.candidates[cond.var.index].ge))
                return false;
            return use(b.lower_unit, b.lower_moved, cond);
        case Less:
            if (cond.value != b.upper + 1_i)
                return false;
            if (! b.upper_ok && ! confirm(b.upper_ok, b.upper_maybe, b.upper_unit, cond, _frame.candidates[cond.var.index].lt))
                return false;
            return use(b.upper_unit, b.upper_moved, cond);
        case Equal:
            if (! b.equal_ok || cond.value != b.lower)
                return false;
            return use(b.equal_unit, true, cond);
        default: return false;
        }
    }
};

auto ProofLogger::emit_assumed_unit(const VariableConditionFrom<SimpleIntegerVariableID> & cond, int level) -> ProofLine
{
    LineBufferLease lease{_imp->line_buffers, _imp->line_buffer_depth};
    auto & unit_line = lease.buffer();
    unit_line += "rup ";
    emit_inequality_to(names_and_ids_tracker(), WPBSum{} + 1_i * static_cast<IntegerVariableCondition>(cond) >= 1_i, unit_line, EnsureNames::Yes);
    unit_line += ";";
    write_indent();
    _imp->proof << unit_line << '\n';
    auto line = advance_proof_line_number();
    _imp->proof_lines_by_level.at(level).insert_at_end(line.number);
    return line;
}

auto ProofLogger::assume_current_bounds(const State & state) -> void
{
    if (_imp->assertion_level != AssertionLevel::Off)
        return;

    for ([[maybe_unused]] const auto & guess : state.guesses())
        throw UnexpectedException{"assume_current_bounds called with a guess in force"};

    auto level = _imp->active_proof_level;

    // Calling again at the same level (the root of the next restart pass)
    // replaces the frame, but a unit for a bound that has not moved since is
    // still there to be cited.
    optional<Imp::AssumptionFrame> previous;
    while (! _imp->assumption_frames.empty() && _imp->assumption_frames.back().level >= level) {
        if (_imp->assumption_frames.back().level == level)
            previous = std::move(_imp->assumption_frames.back());
        _imp->assumption_frames.pop_back();
    }

    Imp::AssumptionFrame frame{level, {}, {}};
    auto n = state.what_variable_id_will_be_created_next().index;
    frame.by_variable.resize(n);
    frame.candidates.resize(n, {ReasonLiteralFilter::no_value, ReasonLiteralFilter::no_value, ReasonLiteralFilter::no_value});
    for (decltype(n) i = 0; i < n; ++i) {
        SimpleIntegerVariableID var{i};
        auto declared = names_and_ids_tracker().declared_bounds_if_tracked(var);
        if (! declared)
            continue;
        auto [lower, upper] = state.bounds(var);
        auto & b = frame.by_variable[i];
        auto & tracker = names_and_ids_tracker();
        b.lower = lower;
        b.upper = upper;
        b.lower_moved = lower > declared->first;
        b.upper_moved = upper < declared->second;
        if (b.lower_moved)
            b.lower_ok = true;
        else if (tracker.order_literal_holds_at_top(var, VariableConditionOperator::GreaterEqual, lower)) {
            b.lower_ok = true;
            b.lower_unit = tracker.boundary_pin_line(var, lower);
        }
        else
            b.lower_maybe = ! tracker.find_xliteral_for(var >= lower);
        if (b.upper_moved)
            b.upper_ok = true;
        else if (tracker.order_literal_holds_at_top(var, VariableConditionOperator::Less, upper + 1_i)) {
            b.upper_ok = true;
            // The pin is keyed by the ge cut, which for `x < ub + 1` is ub + 1.
            b.upper_unit = tracker.boundary_pin_line(var, upper + 1_i);
        }
        else
            b.upper_maybe = ! tracker.find_xliteral_for(var < upper + 1_i);
        // A variable declared fixed has nothing for the search to derive.
        b.equal_ok = lower == upper && (b.lower_moved || b.upper_moved);

        auto & c = frame.candidates[i];
        if (b.lower_ok || b.lower_maybe)
            c.ge = lower;
        if (b.upper_ok || b.upper_maybe)
            c.lt = upper + 1_i;
        if (b.equal_ok)
            c.eq = lower;

        if (previous && i < previous->by_variable.size()) {
            auto & p = previous->by_variable[i];
            if (b.lower_moved && p.lower_moved && p.lower == lower)
                b.lower_unit = p.lower_unit;
            if (b.upper_moved && p.upper_moved && p.upper == upper)
                b.upper_unit = p.upper_unit;
            if (b.equal_ok && p.equal_ok && p.lower == lower)
                b.equal_unit = p.equal_unit;
        }
    }

    _imp->assumption_frames.push_back(std::move(frame));
}

ProofLogger::KeepAssumedReasonLiterals::KeepAssumedReasonLiterals(ProofLogger & logger) : _logger(logger)
{
    ++_logger._imp->keep_assumed_reason_literals;
}

ProofLogger::KeepAssumedReasonLiterals::~KeepAssumedReasonLiterals()
{
    --_logger._imp->keep_assumed_reason_literals;
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

    // Leaving out an assumed reason literal is sound for a line VeriPB checks
    // by unit propagation, which finds the literal's unit for itself, or by
    // propagation over hints, to which the filter adds the unit. Not for an
    // `ia`, which is checked against the one line it cites, term for term.
    optional<AssumedReasonLiteralFilter> filter;
    if (! reason.empty() && ! _imp->assumption_frames.empty() && 0 == _imp->keep_assumed_reason_literals &&
        ! std::holds_alternative<ImpliesProofRule>(rule)) {
        auto hinted = std::holds_alternative<RUPProofRule>(rule) && std::get<RUPProofRule>(rule).lines.has_value();
        filter.emplace(*this, _imp->assumption_frames.back(), hinted);
    }

    // EnsureNames::Yes: see emit() above. A unit the filter writes goes out to
    // the stream ahead of this line, as a definition does, and before any hint
    // below is turned into a relative ID.
    if (! reason.empty()) {
        emit_reified_inequality_to(names_and_ids_tracker(), ineq, reason, rule_line, EnsureNames::Yes, filter ? &*filter : nullptr);
    }
    else {
        emit_inequality_to(names_and_ids_tracker(), ineq, rule_line, EnsureNames::Yes);
    }

    overloaded{
        [&](const RUPProofRule & rule) {
            if (rule.lines) {
                rule_line += ": ";
                // The units go first: VeriPB takes the hints in the order given,
                // and the hints after them were written expecting the omitted
                // literals to be set already.
                if (filter)
                    for (const auto & line : filter->extra_hints) {
                        rule_line += relative_proof_line(line, _imp->proof_line.number);
                        rule_line += ' ';
                    }
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
    // An assumption made at this level or deeper relied on lines that are
    // about to go.
    while (! _imp->assumption_frames.empty() && _imp->assumption_frames.back().level >= depth)
        _imp->assumption_frames.pop_back();

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
    case ProofLevel::TopAndCore:
        _imp->proof_lines_by_level.at(0).insert_at_end(line.number);
        // Into VeriPB's core set as well: see ProofLevel::TopAndCore. Not from
        // inside a subproof, where the constraint does not survive the `qed;`
        // and `core id` would be addressing something the outer database has
        // never seen.
        if (0 == _imp->subproof_depth)
            move_to_core(line);
        break;
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
    ++_imp->subproof_depth;
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
    --_imp->subproof_depth;
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

auto ProofLogger::emit_pbc_proof_line(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLevel level, const Subproof & subproof)
    -> ProofLine
{
    names_and_ids_tracker().need_all_proof_names_in(ineq.lhs);

    log_stacktrace();
    write_indent();
    _imp->proof << "pbc ";
    emit_inequality_to(names_and_ids_tracker(), ineq, _imp->proof);
    _imp->proof << " : subproof\n";

    // The header adds the negated expression, once. (A RED step with a
    // `proofgoal #1` adds it twice, once at the header and again when the goal
    // opens.)
    advance_proof_line_number();
    _imp->current_indent += INDENT_WIDTH;
    ++_imp->subproof_depth;
    subproof(*this);
    --_imp->subproof_depth;
    _imp->current_indent -= INDENT_WIDTH;
    write_indent();
    // Name the subproof's last line as the contradiction. A bare `qed;` lets
    // VeriPB close the subproof by RUP instead, so a body that stopped short of
    // its contradiction would still verify, and mutation lanes that skip a
    // closing step would lose their teeth.
    _imp->proof << "qed : -1;\n";

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
    optional<ProofLine> form_lower_bound_line, form_upper_bound_line;
    if (bound_rows_derivable && have_bound_rows) {
        form_lower_bound_line = form_lower_bound.emit(*this, level);
        form_upper_bound_line = form_upper_bound.emit(*this, level);
    }

    // A [0, 0] target has no bits at all: BinEnc(target) is the empty sum,
    // identically zero (and [0, 0] is the only range with no bits, since a
    // negative lower bound buys a sign bit and a positive upper a magnitude
    // one). The pair the loop below would build is then just `0 >= form` for
    // the ge line and `0 <= form` for the le line --- which are exactly the two
    // bound lines emitted just above, swapped: a [0, 0] target means the
    // operands' declared bounds sum to exactly [0, 0], so form_upper_bound IS
    // `form <= 0` and form_lower_bound IS `form >= 0`.
    //
    // Cumulative's end proxy reaches this whenever a task's start and length
    // are both variables *fixed* to values summing to zero (issue #969): the
    // proxy is skipped for constant IDs, not for variables with fixed bounds.
    //
    // Unlike the m > 0 path, where every returned line is a `red` whose
    // redundancy VeriPB checks --- so a caller that lied about its target's
    // range is caught at check time --- these two are pol lines that hold
    // whatever the target's range is, and a caller whose target does not really
    // equal the form would silently be handed `form <= ub` as its ge line. So
    // check the claim here rather than assuming it.
    if (0 == m) {
        // No pol lines to hand back: an operand is a view, a flag or a literal,
        // or the form is nothing but constants (which no caller has --- and
        // cumulative in particular skips the proxy entirely when an operand is
        // a constant ID). Refuse rather than invent a pair.
        if (! form_lower_bound_line || ! form_upper_bound_line)
            throw ProofError{"introduce_bits_of cannot derive a zero-width target's bounds: its form has no usable bound rows"};

        Integer form_lower = 0_i, form_upper = 0_i;
        for (const auto & term : linear_form.terms) {
            auto accumulate_bounds_of = [&](const SimpleOrProofOnlyIntegerVariableID & id) {
                auto [lower, upper] = names_and_ids_tracker().tracked_bounds(id);
                if (term.coefficient >= 0_i) {
                    form_lower += term.coefficient * lower;
                    form_upper += term.coefficient * upper;
                }
                else {
                    form_lower += term.coefficient * upper;
                    form_upper += term.coefficient * lower;
                }
            };
            // Anything without tracked bounds cleared bound_rows_derivable
            // above, so these throws are unreachable unless that changes.
            auto no_bounds = []() -> void {
                throw ProofError{"introduce_bits_of needs tracked bounds for every term of a zero-width target's form"};
            };
            overloaded{
                [&](const ProofLiteral &) { no_bounds(); },                                     //
                [&](const ProofFlag &) { no_bounds(); },                                        //
                [&](const ProofBitVariable &) { no_bounds(); },                                 //
                [&](const ProofOnlySimpleIntegerVariableID & id) { accumulate_bounds_of(id); }, //
                [&](const IntegerVariableID & var) {
                    overloaded{
                        [&](const SimpleIntegerVariableID & id) { accumulate_bounds_of(id); }, //
                        [&](const ConstantIntegerVariableID & c) {
                            form_lower += term.coefficient * c.const_value;
                            form_upper += term.coefficient * c.const_value;
                        },                                                    //
                        [&](const ViewOfIntegerVariableID &) { no_bounds(); } //
                    }
                        .visit(var);
                } //
            }
                .visit(term.variable);
        }
        if (0_i != form_lower || 0_i != form_upper)
            throw ProofError{"introduce_bits_of was given a zero-width target for a form spanning [" + to_string(form_lower.raw_value) + ", " +
                to_string(form_upper.raw_value) + "]"};

        return {*form_upper_bound_line, *form_lower_bound_line};
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

auto ProofLogger::delete_proof_lines(const vector<ProofLine> & lines) -> void
{
    // Every offset against the same `current`, deletions not advancing the line
    // number, exactly as forget_proof_level does it.
    for (const auto & line : lines) {
        write_indent();
        _imp->proof << "del id " << relative_proof_line(line, _imp->proof_line.number) << ";\n";
    }
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
