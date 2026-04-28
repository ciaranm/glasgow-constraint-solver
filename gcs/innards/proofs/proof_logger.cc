#include <gcs/innards/interval_set.hh>
#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/state.hh>

#include <deque>
#include <fstream>
#include <iomanip>
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
using std::map;
using std::max;
using std::nullopt;
using std::optional;
using std::ostream;
using std::pair;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::variant;
using std::vector;

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
                    .visit(simplify_literal(lit));
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

    Imp(NamesAndIDsTracker & t) :
        tracker(t)
    {
    }
};

ProofLogger::ProofLogger(const ProofOptions & proof_options, NamesAndIDsTracker & t) :
    _imp(new Imp{t})
{
    _imp->proof_file = proof_options.proof_file_names.proof_file;
    _imp->proof_lines_by_level.resize(2);
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

    for (const auto & [var, val] : all_variables_and_values)
        overloaded{
            [&](const ConstantIntegerVariableID &) {
            },
            [&](const SimpleIntegerVariableID & var) {
                _imp->proof << " " << names_and_ids_tracker().pb_file_string_for(var == val);
            },
            [&](const ViewOfIntegerVariableID & var) {
                _imp->proof << " " << names_and_ids_tracker().pb_file_string_for(deview(var == val));
            }}
            .visit(var);

    _imp->proof << ";\n";
    record_proof_line(advance_proof_line_number(), ProofLevel::Top);

    if (optional_minimise_variable_and_value)
        visit([&](const auto & id) {
            emit_rup_proof_line(WPBSum{} + 1_i * (id < optional_minimise_variable_and_value->second) >= 1_i, ProofLevel::Top);
        },
            optional_minimise_variable_and_value->first);
}

auto ProofLogger::backtrack(const vector<Literal> & lits) -> void
{
    _imp->proof << "% backtracking\n";
    WPBSum backtrack;
    for (const auto & lit : lits)
        backtrack += 1_i * ! lit;
    emit_rup_proof_line(move(backtrack) >= 1_i, ProofLevel::Current);
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
    _imp->proof << "rup >= 1 ;\n";
    record_proof_line(advance_proof_line_number(), ProofLevel::Top);
    _imp->proof << "output NONE;\n";
    if (is_optimisation)
        _imp->proof << "conclusion BOUNDS INF INF;\n";
    else
        _imp->proof << "conclusion UNSAT : " << _imp->proof_line << ";\n";
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
    const ReasonFunction & reason) -> void
{
    auto need_lit = [&]() {
        overloaded{
            [&](const TrueLiteral &) {},
            [&](const FalseLiteral &) {},
            [&]<typename T_>(const VariableConditionFrom<T_> & cond) { names_and_ids_tracker().need_proof_name(cond); }}
            .visit(simplify_literal(lit));
    };

    overloaded{
        [&]([[maybe_unused]] const JustifyUsingRUP & j) {
            log_stacktrace();
            need_lit();
            optional<Reason> reason_literals;
            if (reason)
                reason_literals = reason();

            if (reason_literals)
                names_and_ids_tracker().need_all_proof_names_in(*reason_literals);

            if (! is_literally_true(lit)) {
                WPBSum terms;
                HalfReifyOnConjunctionOf reif{};
                if (reason_literals)
                    reif = *reason_literals;

                terms += 1_i * lit;
                write_indent();
                _imp->proof << "rup ";
                emit_inequality_to(names_and_ids_tracker(), reify(move(terms) >= 1_i, reif), _imp->proof);
                _imp->proof << ";\n";
                record_proof_line(advance_proof_line_number(), ProofLevel::Current);
            }
        },
        [&]([[maybe_unused]] const AssertRatherThanJustifying & j) {
            log_stacktrace();
            need_lit();
            optional<Reason> reason_literals;
            if (reason)
                reason_literals = reason();

            HalfReifyOnConjunctionOf reif{};
            if (reason_literals) {
                names_and_ids_tracker().need_all_proof_names_in(*reason_literals);
                reif = *reason_literals;
            }
            if (! is_literally_true(lit)) {
                WPBSum terms;
                terms += 1_i * lit;
                write_indent();
                _imp->proof << "a ";
                emit_inequality_to(names_and_ids_tracker(), reify(move(terms) >= 1_i, reif), _imp->proof);
                _imp->proof << ";\n";
                record_proof_line(advance_proof_line_number(), ProofLevel::Current);
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

auto ProofLogger::reason_to_lits(const ReasonFunction & reason) -> vector<ProofLiteralOrFlag>
{
    optional<Reason> reason_literals;
    if (reason)
        reason_literals = reason();

    if (reason_literals)
        names_and_ids_tracker().need_all_proof_names_in(*reason_literals);

    vector<ProofLiteralOrFlag> reason_proof_literals{};
    for (auto & r : *reason_literals)
        reason_proof_literals.emplace_back(r);

    return reason_proof_literals;
}

auto ProofLogger::reify(const WPBSumLE & ineq, const HalfReifyOnConjunctionOf & half_reif) -> WPBSumLE
{
    return names_and_ids_tracker().reify(ineq, half_reif);
}

auto ProofLogger::reify(const WPBSumLE & ineq, const ReasonFunction & reason) -> WPBSumLE
{
    auto reason_proof_literals = reason_to_lits(reason);

    return names_and_ids_tracker().reify(ineq, HalfReifyOnConjunctionOf{reason_proof_literals});
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

auto ProofLogger::emit(const ProofRule & rule, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLevel level) -> ProofLine
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
                                rule_line << line << ' ';
                            }
                            rule_line << " ;";
                        } else {
                            rule_line << ";";
                        } },
        [&](const ImpliesProofRule & rule) {
            if (rule.line) {
                rule_line << ": ";
                rule_line << *rule.line << ' ';
                rule_line << " ;";
            }
            else {
                rule_line << ";";
            }
        },
        [&](const AssertProofRule &) { rule_line << ";"; }}
        .visit(rule);

    return emit_proof_line(rule_line.str(), level);
}

auto ProofLogger::emit_under_reason(
    const ProofRule & rule, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq,
    ProofLevel level, const ReasonFunction & reason) -> ProofLine
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
        vector<ProofLiteralOrFlag> reason_proof_literals{};
        for (auto & r : *reason_literals)
            reason_proof_literals.emplace_back(r);
        emit_inequality_to(names_and_ids_tracker(), reify(ineq, reason_proof_literals), rule_line);
    }
    else {
        emit_inequality_to(names_and_ids_tracker(), ineq, rule_line);
    }

    overloaded{
        [&](const RUPProofRule & rule) { 
			if(rule.lines) {
				rule_line << ": ";
				for (const auto & line : *rule.lines) {
					rule_line << line << " ";
				}
				rule_line << " ;";
			} else {
				rule_line << ";"; } },
        [&](const ImpliesProofRule & rule) { if (rule.line) {
				rule_line << ": ";
				rule_line << *rule.line << " ";
				rule_line << " ;";
			} else { rule_line << ";"; } },
        [&](const AssertProofRule &) { rule_line << ";"; }}
        .visit(rule);

    return emit_proof_line(rule_line.str(), level);
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
    for (const auto & [l, u] : lines.each_interval()) {
        write_indent();
        if (l == u) {
            _imp->proof << "del id " << l << ";\n";
        }
        else
            _imp->proof << "del range " << l << " " << ProofLineNumber{u + 1} << ";\n";
    }
    lines.clear();
}

auto ProofLogger::start_proof(const ProofModel & model) -> void
{
    try {
        _imp->proof.exceptions(ios::failbit | ios::badbit);
        _imp->proof.open(_imp->proof_file, ios::out);
        _imp->proof << "pseudo-Boolean proof version 3.0\n";
        _imp->proof << "f " << model.number_of_constraints() << " ;\n";
    }
    catch (const ios_base::failure &) {
        throw ProofError{"Error writing proof file to '" + _imp->proof_file + "'"};
    }
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
        advance_proof_line_number();
        write_indent();
        _imp->proof << "proofgoal " << proofgoal << "\n";
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

auto ProofLogger::write_indent() -> void
{
    for (auto _ = _imp->current_indent; _--;) {
        _imp->proof << ' ';
    }
}
