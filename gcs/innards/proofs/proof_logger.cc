#include <gcs/innards/interval_set.hh>
#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
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

    [[nodiscard]] auto witness_literal(VariableConstraintsTracker & variable_constraints_tracker, const ProofLiteralOrFlag & lit) -> string
    {
        return overloaded{
            [&](const ProofLiteral & lit) {
                return overloaded{
                    [](const TrueLiteral &) -> string { return "1"; },
                    [](const FalseLiteral &) -> string { return "0"; },
                    [&]<typename T_>(const VariableConditionFrom<T_> & var) -> string {
                        return variable_constraints_tracker.proof_name(var);
                    }}
                    .visit(simplify_literal(lit));
            },
            [&](const ProofFlag & flag) { return variable_constraints_tracker.proof_name(flag); }}
            .visit(lit);
    }
}

struct ProofLogger::Imp
{
    VariableConstraintsTracker & tracker;

    ProofLine proof_line = 0;
    int active_proof_level = 0;
    deque<IntervalSet<ProofLine>> proof_lines_by_level;

    string proof_file;
    fstream proof;

    Imp(VariableConstraintsTracker & t) :
        tracker(t)
    {
    }
};

ProofLogger::ProofLogger(const ProofOptions & proof_options, VariableConstraintsTracker & t) :
    _imp(new Imp{t})
{
    _imp->proof_file = proof_options.proof_file;
    _imp->proof_lines_by_level.resize(2);
}

ProofLogger::~ProofLogger() = default;

auto ProofLogger::solution(const State & state, const vector<IntegerVariableID> & all_variables,
    const optional<IntegerVariableID> & optional_minimise_variable) -> void
{
    _imp->proof << "* solution\n";

    for (auto & var : all_variables)
        overloaded{
            [&](const ConstantIntegerVariableID &) {},
            [&](const SimpleIntegerVariableID & var) {
                variable_constraints_tracker().need_proof_name(var == state(var));
            },
            [&](const ViewOfIntegerVariableID & var) {
                variable_constraints_tracker().need_proof_name(deview(var == state(var)));
            }}
            .visit(var);

    _imp->proof << (optional_minimise_variable ? "soli" : "solx");

    for (auto & var : all_variables)
        overloaded{
            [&](const ConstantIntegerVariableID &) {
            },
            [&](const SimpleIntegerVariableID & var) {
                _imp->proof << " " << variable_constraints_tracker().proof_name(var == state(var));
            },
            [&](const ViewOfIntegerVariableID & var) {
                _imp->proof << " " << variable_constraints_tracker().proof_name(deview(var == state(var)));
            }}
            .visit(var);

    _imp->proof << '\n';
    record_proof_line(++_imp->proof_line, ProofLevel::Top);

    if (optional_minimise_variable)
        visit([&](const auto & id) {
            emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * (id < state(id)) >= 1_i, ProofLevel::Top);
        },
            *optional_minimise_variable);
}

auto ProofLogger::backtrack(const State & state) -> void
{
    _imp->proof << "* backtracking\n";
    WeightedPseudoBooleanSum backtrack;
    state.for_each_guess([&](const Literal & lit) {
        backtrack += 1_i * ! lit;
    });
    emit_rup_proof_line(move(backtrack) >= 1_i, ProofLevel::Current);
}

auto ProofLogger::end_proof() -> void
{
    _imp->proof << "end pseudo-Boolean proof\n";

    // this is mostly for tests: we haven't necessarily destroyed the
    // Problem before running the verifier.
    _imp->proof << flush;
}

auto ProofLogger::conclude_unsatisfiable(bool is_optimisation) -> void
{
    _imp->proof << "* asserting contradiction\n";
    _imp->proof << "u >= 1 ;\n";
    record_proof_line(++_imp->proof_line, ProofLevel::Top);
    _imp->proof << "output NONE\n";
    if (is_optimisation)
        _imp->proof << "conclusion BOUNDS INF INF\n";
    else
        _imp->proof << "conclusion UNSAT : " << _imp->proof_line << '\n';
    end_proof();
}

auto ProofLogger::conclude_satisfiable() -> void
{
    _imp->proof << "output NONE\n";
    _imp->proof << "conclusion SAT\n";
    end_proof();
}

auto ProofLogger::conclude_optimality(IntegerVariableID var, Integer value) -> void
{
    conclude_bounds(var, value, value);
}

auto ProofLogger::conclude_bounds(IntegerVariableID minimise_variable, Integer lower, Integer upper) -> void
{
    emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * minimise_variable >= lower, ProofLevel::Top);
    _imp->proof << "output NONE\n";
    _imp->proof << "conclusion BOUNDS " << lower << " " << upper << '\n';
    end_proof();
}

auto ProofLogger::conclude_none() -> void
{
    _imp->proof << "output NONE\n";
    _imp->proof << "conclusion NONE\n";
    end_proof();
}

auto ProofLogger::infer(const State & state, bool is_contradicting, const Literal & lit, const Justification & why,
    const Reason & reason) -> void
{
    auto need_lit = [&]() {
        overloaded{
            [&](const TrueLiteral &) {},
            [&](const FalseLiteral &) {},
            [&]<typename T_>(const VariableConditionFrom<T_> & cond) { variable_constraints_tracker().need_proof_name(cond); }}
            .visit(simplify_literal(lit));
    };

    overloaded{
        [&]([[maybe_unused]] const JustifyUsingRUP & j) {
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            _imp->proof << "* RUP on lit " << debug_string(lit) << " with reason from " << j.where.file_name() << ":"
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
                            variable_constraints_tracker().need_proof_name(cond);
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
                _imp->proof << "u ";
                emit_inequality_to(variable_constraints_tracker(), move(terms) >= 1_i, nullopt, _imp->proof);
                _imp->proof << '\n';
                record_proof_line(++_imp->proof_line, ProofLevel::Current);
            }
        },
        [&]([[maybe_unused]] const AssertRatherThanJustifying & j) {
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            _imp->proof << "* assert on lit " << debug_string(lit) << " with reason from " << j.where.file_name() << ":"
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
                            variable_constraints_tracker().need_proof_name(cond);
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
                _imp->proof << "a ";
                emit_inequality_to(variable_constraints_tracker(), move(terms) >= 1_i, nullopt, _imp->proof);
                _imp->proof << '\n';
                record_proof_line(++_imp->proof_line, ProofLevel::Current);
            }
        },
        [&](const JustifyExplicitly & x) {
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            _imp->proof << "* explicit on lit " << debug_string(lit) << " with reason from " << x.where.file_name() << ":"
                        << x.where.line() << " in " << x.where.function_name() << '\n';
#endif
            need_lit();
            auto t = temporary_proof_level();
            x.add_proof_steps(reason);
            infer(state, is_contradicting, lit, JustifyUsingRUP{
#ifdef GCS_TRACK_ALL_PROPAGATIONS
                                                    x.where
#endif
                                                },
                reason);
            forget_proof_level(t);
        },
        [&](const Guess &) {
            need_lit();
            if (! is_literally_true(lit)) {
                // we need this because it'll show up in the trail later
                _imp->proof << "* guessing " << debug_string(lit) << ", decision stack is [";
                state.for_each_guess([&](const Literal & lit) {
                    _imp->proof << " " << debug_string(lit);
                });
                _imp->proof << " ]\n";
            }
        },
        [&](const NoJustificationNeeded &) {
        }}
        .visit(why);
}

auto ProofLogger::emit_proof_line(const string & s, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "* emit proof line from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << '\n';
#endif
    _imp->proof << s << '\n';
    auto result = record_proof_line(++_imp->proof_line, level);
    return result;
}

auto ProofLogger::emit_proof_comment(const string & s) -> void
{
    _imp->proof << "* " << s << '\n';
}

auto ProofLogger::emit_rup_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
    variable_constraints_tracker().need_all_proof_names_in(ineq.lhs);

#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "* emit rup proof line from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << '\n';
#endif

    _imp->proof << "u ";
    emit_inequality_to(variable_constraints_tracker(), ineq, nullopt, _imp->proof);
    _imp->proof << '\n';
    return record_proof_line(++_imp->proof_line, level);
}

auto ProofLogger::emit_assert_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
    variable_constraints_tracker().need_all_proof_names_in(ineq.lhs);

#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "* emit assert line from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << '\n';
#endif
    _imp->proof << "a ";
    emit_inequality_to(variable_constraints_tracker(), ineq, nullopt, _imp->proof);
    _imp->proof << '\n';
    return record_proof_line(++_imp->proof_line, level);
}

auto ProofLogger::emit_rup_proof_line_under_reason(const State &, const Reason & reason, const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
    ProofLevel level
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
        for (auto & r : *reason_literals)
            overloaded{
                [&](const TrueLiteral &) {
                },
                [&](const FalseLiteral &) {
                },
                [&](const VariableConditionFrom<SimpleIntegerVariableID> & cond) {
                    variable_constraints_tracker().need_proof_name(cond);
                },
                [&](const ProofVariableCondition &) {
                }}
                .visit(simplify_literal(r));

    variable_constraints_tracker().need_all_proof_names_in(ineq.lhs);

#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "* emit rup proof line from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << '\n';
#endif

    stringstream rup_line;
    rup_line << "u ";

    if (reason_literals) {
        vector<ProofLiteralOrFlag> reason_proof_literals{};
        for (auto & r : *reason_literals)
            reason_proof_literals.emplace_back(r);
        emit_inequality_to(variable_constraints_tracker(), ineq, HalfReifyOnConjunctionOf{reason_proof_literals}, rup_line);
    }
    else {
        emit_inequality_to(variable_constraints_tracker(), ineq, nullopt, rup_line);
    }

    return emit_proof_line(
        rup_line.str(), level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        ,
        where
#endif
    );
}

auto ProofLogger::emit_red_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
    const std::vector<std::pair<ProofLiteralOrFlag, ProofLiteralOrFlag>> & witness,
    ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
    variable_constraints_tracker().need_all_proof_names_in(ineq.lhs);

#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "* emit red line from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << '\n';
#endif
    _imp->proof << "red ";
    emit_inequality_to(variable_constraints_tracker(), ineq, nullopt, _imp->proof);

    for (auto & [f, t] : witness)
        _imp->proof << " " << witness_literal(variable_constraints_tracker(), f) << " -> " << witness_literal(variable_constraints_tracker(), t);
    _imp->proof << " ;\n";

    return record_proof_line(++_imp->proof_line, level);
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
        if (l == u)
            _imp->proof << "del id " << l << '\n';
        else
            _imp->proof << "del range " << l << " " << u + 1 << '\n';
    }
    lines.clear();
}

auto ProofLogger::start_proof(const ProofModel & model) -> void
{
    _imp->proof.open(_imp->proof_file, ios::out);

    _imp->proof << "pseudo-Boolean proof version 2.0\n";

    _imp->proof << "f " << model.number_of_constraints() << " 0\n";
    _imp->proof_line += model.number_of_constraints();

    if (! _imp->proof)
        throw ProofError{"Error writing proof file to '" + _imp->proof_file + "'"};
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

auto ProofLogger::variable_constraints_tracker() -> VariableConstraintsTracker &
{
    return _imp->tracker;
}

auto ProofLogger::emit_subproofs(const map<string, JustifyExplicitly> & subproofs, const Reason & reason)
{
    _imp->proof << " begin\n";
    ++_imp->proof_line;
    for (const auto & [proofgoal, proof] : subproofs) {
        ++_imp->proof_line;
        _imp->proof
            << "     proofgoal " << proofgoal << "\n";
        proof.add_proof_steps(reason);
        _imp->proof << "     end -1\n";
    }
    _imp->proof << "end\n";
}

auto ProofLogger::emit_red_proof_lines_forward_reifying(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLiteralOrFlag reif,
    ProofLevel level, const optional<map<string, JustifyExplicitly>> & subproofs
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "* emit red lines forward reifying from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << '\n';
#endif

    variable_constraints_tracker().need_all_proof_names_in(ineq.lhs);
    _imp->proof << "red ";
    emit_inequality_to(variable_constraints_tracker(), ineq, {{reif}}, _imp->proof);
    _imp->proof << " " << witness_literal(variable_constraints_tracker(), reif) << " -> 0";
    _imp->proof << " ;";
    if (subproofs)
        emit_subproofs(subproofs.value(), Reason{});
    else
        _imp->proof << "\n";

    return record_proof_line(++_imp->proof_line, level);
}

auto ProofLogger::emit_red_proof_lines_reverse_reifying(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLiteralOrFlag reif,
    ProofLevel level, const optional<map<string, JustifyExplicitly>> & subproofs
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    ,
    const std::source_location & where
#endif
    ) -> ProofLine
{
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    _imp->proof << "* emit red lines reverse reifying from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << '\n';
#endif

    variable_constraints_tracker().need_all_proof_names_in(ineq.lhs);
    auto negated_ineq = ineq.lhs >= ineq.rhs + 1_i;
    _imp->proof << "red ";
    emit_inequality_to(variable_constraints_tracker(), negated_ineq, {{! reif}}, _imp->proof);
    _imp->proof << " " << witness_literal(variable_constraints_tracker(), reif) << " -> 1";
    _imp->proof << " ;";
    if (subproofs)
        emit_subproofs(subproofs.value(), Reason{});
    else
        _imp->proof << "\n";
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
    _imp->proof << "* emit red lines reifying from " << where.file_name() << ":" << where.line() << " in " << where.function_name() << '\n';
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
    return variable_constraints_tracker().create_proof_flag(name);
}
