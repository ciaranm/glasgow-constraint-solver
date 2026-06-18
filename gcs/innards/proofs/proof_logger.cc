#include <cstdio>
#include <gcs/expression.hh>
#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/interval_set.hh>
#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/state.hh>
#include <gcs/proof.hh>

#include <cstddef>
#include <cstdlib>
#include <deque>
#include <fstream>
#include <optional>
#include <sstream>

#include <version>
#ifdef __cpp_lib_stacktrace
#include <stacktrace>
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
                return VariableConditionFrom<SimpleIntegerVariableID>{cond.var.actual_variable, cond.op,
                    cond.var.then_add - cond.upper_value, cond.var.then_add - cond.value};
            else
                return VariableConditionFrom<SimpleIntegerVariableID>{cond.var.actual_variable, cond.op,
                    cond.value - cond.var.then_add, cond.upper_value - cond.var.then_add};
        }
        throw NonExhaustiveSwitch{};
    }

    [[nodiscard]] auto witness_literal(NamesAndIDsTracker & names_and_ids_tracker, const ProofLiteralOrFlag & lit) -> string
    {
        return overloaded{
            [&](const ProofLiteral & lit) {
                return overloaded{
                    [](const TrueLiteral &) -> string { return "1"; },
                    [](const FalseLiteral &) -> string { return "0"; },
                    [&]<typename T_>(const VariableConditionFrom<T_> & var) -> string {
                        return names_and_ids_tracker.pb_file_string_for(var);
                    }}
                    .visit(simplify_literal(names_and_ids_tracker, lit));
            },
            [&](const ProofFlag & flag) {
                return names_and_ids_tracker.pb_file_string_for(flag);
            },
            [&](const ProofBitVariable & bit) {
                return names_and_ids_tracker.pb_file_string_for(names_and_ids_tracker.get_bit(bit).second);
            }}
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
    int current_indent = 0;
    AssertionLevel assertion_level;

    Imp(NamesAndIDsTracker & t) :
        tracker(t)
    {
    }
};

ProofLogger::ProofLogger(const ProofOptions & proof_options, NamesAndIDsTracker & t) :
    _imp(make_unique<Imp>(t))
{
    _imp->proof_file = proof_options.proof_file_names.proof_file;
    _imp->proof_lines_by_level.resize(2);
    _imp->assertion_level = proof_options.assertion_level;
}

ProofLogger::~ProofLogger() = default;

auto ProofLogger::log_stacktrace() -> void
{
#ifdef __cpp_lib_stacktrace
    static bool do_logging = []() {
        return getenv("GCS_VERBOSE_LOGGING");
    }();

    using std::stacktrace;
    if (do_logging) [[unlikely]] {
        for (const auto & entry : stacktrace::current()) {
            if (entry.source_file().contains("/gcs/"))
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
            [&](const ConstantIntegerVariableID &) {},
            [&](const SimpleIntegerVariableID & var) {
                names_and_ids_tracker().need_proof_name(var == val);
            },
            [&](const ViewOfIntegerVariableID & var) {
                names_and_ids_tracker().need_proof_name(deview(var == val));
            }}
            .visit(var);

    _imp->proof << (optional_minimise_variable_and_value ? "soli" : "solx");

    WPBSum blocking_sum{};

    for (const auto & [var, val] : all_variables_and_values) {
        if (! optional_minimise_variable_and_value && _imp->assertion_level > AssertionLevel::Links)
            blocking_sum += 1_i * (var != val);

        overloaded{
            [&](const ConstantIntegerVariableID &) {
            },
            [&](const SimpleIntegerVariableID & var) {
                if (_imp->assertion_level > AssertionLevel::Definitions)
                    _imp->proof << " " << names_and_ids_tracker().bit_assignment_string_for(var, val);
                else
                    _imp->proof << " " << names_and_ids_tracker().pb_file_string_for(var == val);
            },
            [&](const ViewOfIntegerVariableID & var) {
                if (_imp->assertion_level > AssertionLevel::Definitions) {
                    _imp->proof << " " << names_and_ids_tracker().bit_assignment_string_for(*names_and_ids_tracker().find_view(var), val);
                }
                else
                    _imp->proof << " " << names_and_ids_tracker().pb_file_string_for(deview(var == val));
            }}
            .visit(var);
    }

    _imp->proof << ";\n";
    record_proof_line(advance_proof_line_number(), ProofLevel::Top);

    if (optional_minimise_variable_and_value && _imp->assertion_level > AssertionLevel::Definitions)
        // soli and no links => have to assert the objective improving constraint
        visit([&](const auto & id) {
            emit(AssertProofRule{}, WPBSum{} + 1_i * (id < optional_minimise_variable_and_value->second) >= 1_i, ProofLevel::Top, AssertionAnnotation{.hint_name = AssertionHintName::SoliImprove});
        },
            optional_minimise_variable_and_value->first);
    else if (optional_minimise_variable_and_value)
        // normal soli, emit e line for trimmer
        visit([&](const auto & id) {
            _imp->proof << "e ";
            emit_inequality_to(names_and_ids_tracker(), WPBSum{} + 1_i * id <= optional_minimise_variable_and_value->second - 1_i, _imp->proof);
            _imp->proof << ":" << relative_proof_line(_imp->proof_line, _imp->proof_line.number) << ";\n";

            emit_rup_proof_line(WPBSum{} + 1_i * (id < optional_minimise_variable_and_value->second) >= 1_i, ProofLevel::Top);
        },
            optional_minimise_variable_and_value->first);
    else if (_imp->assertion_level > AssertionLevel::Definitions) {
        // solx and no links => have to assert the blocking constraint
        emit(AssertProofRule{}, blocking_sum >= 1_i, ProofLevel::Top, AssertionAnnotation{.hint_name = AssertionHintName::SolxBlock});
    }
    // nothing needs done for solx below AssertionLevel::Links
}

auto ProofLogger::backtrack(const vector<Literal> & guesses) -> void
{
    _imp->proof << "% backtracking\n";
    WPBSum backtrack;
    for (const auto & guess : guesses)
        backtrack += 1_i * ! guess;
    auto assert_or_rup = (_imp->assertion_level >= AssertionLevel::Inferences) ? ProofRule(AssertProofRule{}) : ProofRule(RUPProofRule{});
    emit(assert_or_rup, move(backtrack) >= 1_i, ProofLevel::Current, AssertionAnnotation{.hint_name = AssertionHintName::Backtrack});
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
    auto assert_or_rup = _imp->assertion_level == AssertionLevel::Backtracking ? ProofRule(AssertProofRule{}) : ProofRule(RUPProofRule{});
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

auto ProofLogger::infer(const Literal & lit, const Justification & why,
    const ReasonFunction & reason, const optional<AssertionAnnotation> & annotation) -> void
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
                [&](const SimpleIntegerVariableID & v) { return ! names_and_ids_tracker().has_bit_representation(v); },
                [&](const ViewOfIntegerVariableID &) { return true; },
                [&](const ConstantIntegerVariableID &) { return false; }}
                                                .visit(cond->var);
            if (needs_per_value_fallback) {
                for (Integer val = cond->value; val <= cond->upper_value; ++val)
                    infer(cond->var != val, why, reason);
                return;
            }
        }

    auto need_lit = [&]() {
        overloaded{
            [&](const TrueLiteral &) {},
            [&](const FalseLiteral &) {},
            [&]<typename T_>(const VariableConditionFrom<T_> & cond) { names_and_ids_tracker().need_proof_name(cond); }}
            .visit(simplify_literal(names_and_ids_tracker(), lit));
    };

    if (_imp->assertion_level > AssertionLevel::Inferences)
        return;

    if ((_imp->assertion_level == AssertionLevel::Definitions && annotation) || _imp->assertion_level >= AssertionLevel::Links) {
        // At AssertionLevel::Definitions we can assert some inferences and not others (since the needed constraints for the justifications will
        // still be present). At higher levels, we need to assert all inferences.
        if (! is_literally_true(lit)) {
            emit_under_reason(AssertProofRule{}, WPBSum{} + 1_i * lit >= 1_i, ProofLevel::Current, reason, annotation);
        }
        return;
    }

    overloaded{
        [&]([[maybe_unused]] const JustifyUsingRUP & j) {
            if (! is_literally_true(lit)) {
                emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * lit >= 1_i, ProofLevel::Current);
            }
        },
        [&]([[maybe_unused]] const AssertRatherThanJustifying & j) {
            if (! is_literally_true(lit)) {
                emit_under_reason(AssertProofRule{}, WPBSum{} + 1_i * lit >= 1_i, ProofLevel::Current, reason);
            }
        },
        [&](const JustifyExplicitlyOnly & x) {
            auto t = temporary_proof_level();
            x.add_proof_steps(reason);
            forget_proof_level(t);
        },
        [&](const JustifyExplicitlyThenRUP & x) {
            need_lit();
            auto t = temporary_proof_level();
            x.add_proof_steps(reason);
            infer(lit, JustifyUsingRUP{}, reason);
            forget_proof_level(t);
        },
        [&](const NoJustificationNeeded &) {
        }}
        .visit(why);
}

auto ProofLogger::reason_to_lits(const ReasonFunction & reason) -> Reason
{
    optional<Reason> reason_literals;
    if (reason)
        reason_literals = reason();

    if (reason_literals)
        names_and_ids_tracker().need_all_proof_names_in(*reason_literals);

    return *reason_literals;
}

auto ProofLogger::reify(const WPBSumLE & ineq, const HalfReifyOnConjunctionOf & half_reif) -> WPBSumLE
{
    return names_and_ids_tracker().reify(ineq, half_reif);
}

auto ProofLogger::reify(const WPBSumLE & ineq, const ReasonFunction & reason) -> WPBSumLE
{
    return names_and_ids_tracker().reify(ineq, reason_to_lits(reason));
}

auto ProofLogger::emit_proof_line(const string & s, ProofLevel level) -> ProofLine
{
    log_stacktrace();
    write_indent();
    _imp->proof << s << '\n';
    auto result = record_proof_line(advance_proof_line_number(), level);
    return result;
}

auto ProofLogger::emit_proof_comment(const string & s) -> void
{
    _imp->proof << "% " << s << '\n';
}

auto ProofLogger::emit(const ProofRule & rule, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLevel level, const std::optional<AssertionAnnotation> & assertion_hint) -> ProofLine
{
    names_and_ids_tracker().need_all_proof_names_in(ineq.lhs);
    log_stacktrace();

    stringstream rule_line;

    rule_line << overloaded{
                     [&](const RUPProofRule &) -> string { return "rup"; },
                     [&](const ImpliesProofRule &) -> string { return "ia"; },
                     [&](const AssertProofRule &) -> string { return "a"; }}
                     .visit(rule)
              << " ";

    emit_inequality_to(names_and_ids_tracker(), ineq, rule_line);

    overloaded{
        [&](const RUPProofRule & rule) {
            if (rule.lines) {
                rule_line << ": ";
                for (auto & line : *rule.lines) {
                    rule_line << relative_proof_line(line, _imp->proof_line.number) << ' ';
                }
                rule_line << " ;";
            }
            else {
                rule_line << ";";
            }
        },
        [&](const ImpliesProofRule & rule) {
            if (rule.line) {
                rule_line << ": ";
                rule_line << relative_proof_line(*rule.line, _imp->proof_line.number) << ' ';
                rule_line << " ;";
            }
            else {
                rule_line << ";";
            }
        },
        [&](const AssertProofRule &) {
			if (assertion_hint) {
				rule_line << *assertion_hint;
	 		}
			rule_line << ";"; }}
        .visit(rule);

    auto line = emit_proof_line(rule_line.str(), level);
    // Note: no automatic deview-derivation here. Runtime RUP/red emissions
    // happen many times per propagator inference and per-call deview
    // derivation explodes proof size on tests with many view-using
    // constraints. Callers that need the deview-form of a runtime-mitted
    // constraint use the explicit `*_then_deview` variant (see
    // `emit_rup_proof_line_under_reason_then_deview`).
    return line;
}

auto ProofLogger::emit_under_reason(
    const ProofRule & rule, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq,
    ProofLevel level, const ReasonFunction & reason, const std::optional<AssertionAnnotation> & assertion_hint) -> ProofLine
{
    optional<Reason> reason_literals;
    if (reason)
        reason_literals = reason();
    if (reason_literals)
        names_and_ids_tracker().need_all_proof_names_in(*reason_literals);

    names_and_ids_tracker().need_all_proof_names_in(ineq.lhs);

    log_stacktrace();
    stringstream rule_line;

    rule_line << overloaded{
                     [&](const RUPProofRule &) -> string { return "rup"; },
                     [&](const ImpliesProofRule &) -> string { return "ia"; },
                     [&](const AssertProofRule &) -> string { return "a"; }}
                     .visit(rule)
              << " ";

    if (reason_literals) {
        emit_inequality_to(names_and_ids_tracker(), reify(ineq, *reason_literals), rule_line);
    }
    else {
        emit_inequality_to(names_and_ids_tracker(), ineq, rule_line);
    }

    overloaded{
        [&](const RUPProofRule & rule) {
			if(rule.lines) {
				rule_line << ": ";
				for (const auto & line : *rule.lines) {
					rule_line << relative_proof_line(line, _imp->proof_line.number) << " ";
				}
				rule_line << " ;";
			} else {
				rule_line << ";"; } },
        [&](const ImpliesProofRule & rule) { if (rule.line) {
				rule_line << ": ";
				rule_line << relative_proof_line(*rule.line, _imp->proof_line.number) << " ";
				rule_line << " ;";
			} else { rule_line << ";"; } },
        [&](const AssertProofRule &) { 
			if (assertion_hint) {
				rule_line << *assertion_hint;
	 		}

			rule_line << ";"; }}
        .visit(rule);

    auto line = emit_proof_line(rule_line.str(), level);
    // Note: see comment in `emit()` about why no auto-deview-derivation.
    return line;
}

auto ProofLogger::emit_rup_proof_line(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLevel level) -> ProofLine
{
    return emit(RUPProofRule{}, ineq, level);
}

auto ProofLogger::emit_rup_proof_line_under_reason(const ReasonFunction & reason, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq,
    ProofLevel level) -> ProofLine
{
    return emit_under_reason(RUPProofRule{}, ineq, level, reason);
}

auto ProofLogger::emit_rup_proof_line_under_reason_then_deview(const ReasonFunction & reason,
    const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLevel level) -> ProofLine
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
}

auto ProofLogger::start_proof(const ProofModel & model) -> void
{
    try {
        _imp->proof.exceptions(ios::failbit | ios::badbit);
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
    case ProofLevel::Top:
        _imp->proof_lines_by_level.at(0).insert_at_end(line.number);
        break;
    case ProofLevel::Current:
        _imp->proof_lines_by_level.at(_imp->active_proof_level).insert_at_end(line.number);
        break;
    case ProofLevel::Temporary:
        _imp->proof_lines_by_level.at(_imp->active_proof_level + 1).insert_at_end(line.number);
        break;
    }

    return line;
}

auto ProofLogger::names_and_ids_tracker() -> NamesAndIDsTracker &
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
                  [&](const ProofLine & l) { _imp->proof << relative_proof_line(l, goal_base); },
                  [&](const string & s) { _imp->proof << s; }},
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
    const std::vector<std::pair<ProofLiteralOrFlag, ProofLiteralOrFlag>> & witness,
    ProofLevel level, const std::optional<std::map<ProofGoal, Subproof>> & subproofs) -> ProofLine
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

auto ProofLogger::emit_red_proof_lines_reifying(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLiteralOrFlag reif,
    ProofLevel level) -> pair<ProofLine, ProofLine>
{
    log_stacktrace();

    auto forward_result = emit_red_proof_lines_forward_reifying(ineq, reif, level);
    auto reverse_result = emit_red_proof_lines_reverse_reifying(ineq, reif, level);
    return pair{forward_result, reverse_result};
}

auto ProofLogger::create_proof_flag_reifying(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq,
    const string & name, ProofLevel level) -> tuple<ProofFlag, ProofLine, ProofLine>
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
    _imp->proof << "del range " << relative_proof_line(from, _imp->proof_line.number)
                << " " << relative_proof_line(up_to, _imp->proof_line.number) << ";\n";
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
