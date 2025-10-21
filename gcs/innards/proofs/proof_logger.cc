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

using std::cmp_less_equal;
using std::deque;
using std::flush;
using std::fstream;
using std::ios;
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

    ProofLine proof_line = 0;
    int active_proof_level = 0;
    deque<IntervalSet<ProofLine>> proof_lines_by_level;

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
    record_proof_line(++_imp->proof_line, ProofLevel::Top);

    if (optional_minimise_variable_and_value)
        visit([&](const auto & id) {
            emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * (id < optional_minimise_variable_and_value->second) >= 1_i, ProofLevel::Top);
        },
            optional_minimise_variable_and_value->first);
}

auto ProofLogger::backtrack(const vector<Literal> & lits) -> void
{
    _imp->proof << "% backtracking\n";
    WeightedPseudoBooleanSum backtrack;
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
    record_proof_line(++_imp->proof_line, ProofLevel::Top);
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

auto ProofLogger::conclude_optimality(IntegerVariableID var, Integer value) -> void
{
    conclude_bounds(var, value, value);
}

auto ProofLogger::conclude_bounds(IntegerVariableID minimise_variable, Integer lower, Integer upper) -> void
{
    emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * minimise_variable >= lower, ProofLevel::Top);
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
    const Reason & reason) -> void
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
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            _imp->proof << "% RUP on lit " << debug_string(lit) << " with reason from " << j.where.file_name() << ":"
                        << j.where.line() << " in " << j.where.function_name() << "\n";
#endif
            need_lit();
            optional<Literals> reason_literals;
            if (reason)
                reason_literals = reason();

            if (reason_literals)
                for (auto & r : *reason_literals)
                    overloaded{
                        [&](const TrueLiteral &) {
                        },
                        [&](const FalseLiteral &) {
                        },
                        [&](const VariableConditionFrom<SimpleIntegerVariableID> & cond) {
                            names_and_ids_tracker().need_proof_name(cond);
                        },
                        [&](const ProofVariableCondition &) {
                        }}
                        .visit(simplify_literal(r));

            if (! is_literally_true(lit)) {
                WeightedPseudoBooleanSum terms;
                if (reason_literals)
                    for (auto & r : *reason_literals)
                        terms += 1_i * ! r;
                terms += 1_i * lit;
                write_indent();
                _imp->proof << "rup ";
                emit_inequality_to(names_and_ids_tracker(), move(terms) >= 1_i, _imp->proof);
                _imp->proof << ";\n";
                record_proof_line(++_imp->proof_line, ProofLevel::Current);
            }
        },
        [&]([[maybe_unused]] const AssertRatherThanJustifying & j) {
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            _imp->proof << "% assert on lit " << debug_string(lit) << " with reason from " << j.where.file_name() << ":"
                        << j.where.line() << " in " << j.where.function_name() << '\n';
#endif
            need_lit();
            optional<Literals> reason_literals;
            if (reason)
                reason_literals = reason();

            if (reason_literals)
                for (auto & r : *reason_literals)
                    overloaded{
                        [&](const TrueLiteral &) {
                        },
                        [&](const FalseLiteral &) {
                        },
                        [&](const VariableConditionFrom<SimpleIntegerVariableID> & cond) {
                            names_and_ids_tracker().need_proof_name(cond);
                        },
                        [&](const ProofVariableCondition &) {
                        }}
                        .visit(simplify_literal(r));

            if (! is_literally_true(lit)) {
                WeightedPseudoBooleanSum terms;
                if (reason)
                    for (auto & r : *reason_literals)
                        terms += 1_i * ! r;
                terms += 1_i * lit;
                write_indent();
                _imp->proof << "a ";
                emit_inequality_to(names_and_ids_tracker(), move(terms) >= 1_i, _imp->proof);
                _imp->proof << ";\n";
                record_proof_line(++_imp->proof_line, ProofLevel::Current);
            }
        },
        [&](const JustifyExplicitly & x) {
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            _imp->proof << "% explicit on lit " << debug_string(lit) << " with reason from " << x.where.file_name() << ":"
                        << x.where.line() << " in " << x.where.function_name() << '\n';
#endif
            need_lit();
            auto t = temporary_proof_level();
            x.add_proof_steps(reason);
            infer(lit, JustifyUsingRUP{
#ifdef GCS_TRACK_ALL_PROPAGATIONS
                           x.where
#endif
                       },
                reason);
            forget_proof_level(t);
        },
        [&](const NoJustificationNeeded &) {
        }}
        .visit(why);
}

auto ProofLogger::reason_to_lits(const Reason & reason) -> vector<ProofLiteralOrFlag>
{
    optional<Literals> reason_literals;
    if (reason)
        reason_literals = reason();

    if (reason_literals)
        names_and_ids_tracker().need_all_proof_names_in(*reason_literals);

    vector<ProofLiteralOrFlag> reason_proof_literals{};
    for (auto & r : *reason_literals)
        reason_proof_literals.emplace_back(r);

    return reason_proof_literals;
}

auto ProofLogger::reify(const WeightedPseudoBooleanLessEqual & ineq, const HalfReifyOnConjunctionOf & half_reif) -> WeightedPseudoBooleanLessEqual
{
    return names_and_ids_tracker().reify(ineq, half_reif);
}

auto ProofLogger::reify(const WeightedPseudoBooleanLessEqual & ineq, const Reason & reason) -> WeightedPseudoBooleanLessEqual
{
    auto reason_proof_literals = reason_to_lits(reason);

    return names_and_ids_tracker().reify(ineq, HalfReifyOnConjunctionOf{reason_proof_literals});
}

auto ProofLogger::emit_proof_line(const string & s, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "% emit proof line from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << '\n';
#endif
    write_indent();
    _imp->proof << s << '\n';
    auto result = record_proof_line(++_imp->proof_line, level);
    return result;
}

auto ProofLogger::emit_proof_comment(const string & s) -> void
{
    _imp->proof << "% " << s << '\n';
}

auto ProofLogger::emit(const ProofRule & rule, const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
    ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
    names_and_ids_tracker().need_all_proof_names_in(ineq.lhs);
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "% emit proof line from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << '\n';
#endif

    stringstream rule_line;

    rule_line << overloaded{
                     [&](const RUPProofRule &) -> string { return "rup"; },
                     [&](const ImpliesProofRule &) -> string { return "ia"; },
                     [&](const AssertProofRule &) -> string { return "a"; }}
                     .visit(rule)
              << " ";

    emit_inequality_to(names_and_ids_tracker(), ineq, rule_line);

    rule_line << overloaded{
                     [&](const RUPProofRule &) -> string { return ";"; },
                     [&](const ImpliesProofRule & rule) -> string { if (rule.line) { return " : " + to_string(*rule.line) + ";"; } else { return ";"; } },
                     [&](const AssertProofRule &) -> string { return ";"; }}
                     .visit(rule)
              << " ";

    return emit_proof_line(
        rule_line.str(), level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        ,
        where
#endif
    );
}

auto ProofLogger::emit_under_reason(
    const ProofRule & rule, const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
    ProofLevel level, const Reason & reason
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
    optional<Literals> reason_literals;
    if (reason)
        reason_literals = reason();
    if (reason_literals)
        names_and_ids_tracker().need_all_proof_names_in(*reason_literals);

    names_and_ids_tracker().need_all_proof_names_in(ineq.lhs);

#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "% emit proof line from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << '\n';
#endif

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

    rule_line << overloaded{
                     [&](const RUPProofRule &) -> string { return ";"; },
                     [&](const ImpliesProofRule & rule) -> string { if (rule.line) { return " : " + to_string(*rule.line) + ";" ;} else { return ";"; } },
                     [&](const AssertProofRule &) -> string { return ";"; }}
                     .visit(rule)
              << " ";

    return emit_proof_line(
        rule_line.str(), level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        ,
        where
#endif
    );
}

auto ProofLogger::emit_rup_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
    return emit(RUPProofRule{}, ineq, level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        ,
        where
#endif
    );
}

auto ProofLogger::emit_rup_proof_line_under_reason(const Reason & reason, const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
    ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
    return emit_under_reason(RUPProofRule{}, ineq, level, reason
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        ,
        where
#endif
    );
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
            _imp->proof << "del range " << l << " " << u + 1 << ";\n";
    }
    lines.clear();
}

auto ProofLogger::start_proof(const ProofModel & model) -> void
{
    _imp->proof.open(_imp->proof_file, ios::out);

    _imp->proof << "pseudo-Boolean proof version 3.0\n";

    _imp->proof << "f " << model.number_of_constraints() << " ;\n";
    _imp->proof_line += model.number_of_constraints();

    if (! _imp->proof)
        throw ProofError{"Error writing proof file to "
                         " + _imp->proof_file + "
                         ""};
}

auto ProofLogger::record_proof_line(ProofLine line, ProofLevel level) -> ProofLine
{
    switch (level) {
    case ProofLevel::Top:
        _imp->proof_lines_by_level.at(0).insert_at_end(line);
        break;
    case ProofLevel::Current:
        _imp->proof_lines_by_level.at(_imp->active_proof_level).insert_at_end(line);
        break;
    case ProofLevel::Temporary:
        _imp->proof_lines_by_level.at(_imp->active_proof_level + 1).insert_at_end(line);
        break;
    }

    return line;
}

auto ProofLogger::names_and_ids_tracker() -> NamesAndIDsTracker &
{
    return _imp->tracker;
}

auto ProofLogger::emit_subproofs(const map<string, Subproof> & subproofs)
{
    _imp->proof << " : subproof\n";
    ++_imp->proof_line;
    _imp->current_indent += INDENT_WIDTH;
    for (const auto & [proofgoal, proof] : subproofs) {
        ++_imp->proof_line;
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

auto ProofLogger::emit_red_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
    const std::vector<std::pair<ProofLiteralOrFlag, ProofLiteralOrFlag>> & witness,
    ProofLevel level, const std::optional<std::map<std::string, Subproof>> & subproofs
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
    names_and_ids_tracker().need_all_proof_names_in(ineq.lhs);

#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "% emit red line from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << "\n";
#endif
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

    return record_proof_line(++_imp->proof_line, level);
}

auto ProofLogger::emit_red_proof_lines_forward_reifying(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLiteralOrFlag reif,
    ProofLevel level, const optional<map<string, Subproof>> & subproofs
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "% emit red lines forward reifying from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << "\n";
#endif

    names_and_ids_tracker().need_all_proof_names_in(ineq.lhs);
    write_indent();
    _imp->proof << "red ";
    emit_inequality_to(names_and_ids_tracker(), reify(ineq, {{reif}}), _imp->proof);
    _imp->proof << " : " << witness_literal(names_and_ids_tracker(), reif) << " -> 0";
    if (subproofs)
        emit_subproofs(subproofs.value());
    else
        _imp->proof << ";\n";

    return record_proof_line(++_imp->proof_line, level);
}

auto ProofLogger::emit_red_proof_lines_reverse_reifying(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLiteralOrFlag reif,
    ProofLevel level, const optional<map<string, Subproof>> & subproofs
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "% emit red lines reverse reifying from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << '\n';
#endif

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
    return record_proof_line(++_imp->proof_line, level);
}

auto ProofLogger::emit_red_proof_lines_reifying(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLiteralOrFlag reif,
    ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> pair<ProofLine, ProofLine>
{
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "% emit red lines reifying from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << '\n';
#endif

    auto forward_result = emit_red_proof_lines_forward_reifying(ineq, reif, level);
    auto reverse_result = emit_red_proof_lines_reverse_reifying(ineq, reif, level);
    return pair{forward_result, reverse_result};
}

auto ProofLogger::create_proof_flag_reifying(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
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