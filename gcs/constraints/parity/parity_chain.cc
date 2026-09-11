#include <gcs/constraints/parity/parity_chain.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <util/enumerate.hh>

#include <map>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::map;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::to_string;
using std::vector;

auto gcs::innards::define_parity_chain(ProofModel & model, const ConstraintID & id, const optional<long long> & row, const Literals & lits)
    -> ParityChainRows
{
    // cake_pb_cp's accumulator scheme, over the literals as cake reads them
    // (each operand tuple maps to the same ge / eq atom our proof uses):
    // x[id][0] channels the parity bit (always the constant 1 here, which cake
    // carries as its pinned-true n[1][ge1] atom; our rows fold it), x[id][k] =
    // x[id][k-1] XOR the k'th literal via four labelled clauses, and the acc
    // row pins the final accumulator to 0, i.e. 1 XOR (parity of the literals)
    // = 0.
    auto role_prefix = row ? "r" + to_string(*row) + "_" : string{};
    auto flag_values = [&](long long k) {
        vector<long long> values;
        if (row)
            values.push_back(*row);
        values.push_back(k);
        return values;
    };

    ParityChainRows result;
    auto x0 = model.create_proof_flag(id, flag_values(0), nullopt);
    result.accumulators.push_back(x0);
    result.a0_le_1 = model.add_labelled_constraint(id, role_prefix + "0ge", WPBSum{} + 1_i * TrueLiteral{} + -1_i * x0 >= 0_i);
    result.a0_ge_1 = model.add_labelled_constraint(id, role_prefix + "0le", WPBSum{} + 1_i * x0 + -1_i * TrueLiteral{} >= 0_i);
    PseudoBooleanTerm acc = x0, not_acc = ! x0;
    for (const auto & [k, l] : enumerate(lits)) {
        auto new_acc = model.create_proof_flag(id, flag_values(static_cast<long long>(k) + 1), nullopt);
        auto stem = role_prefix + to_string(k + 1);
        result.steps.push_back(
            ParityChainRows::Step{model.add_labelled_constraint(id, stem + "_0_0", WPBSum{} + 1_i * acc + 1_i * l + 1_i * ! new_acc >= 1_i),
                model.add_labelled_constraint(id, stem + "_1_1", WPBSum{} + 1_i * not_acc + 1_i * ! l + 1_i * ! new_acc >= 1_i),
                model.add_labelled_constraint(id, stem + "_1_0", WPBSum{} + 1_i * not_acc + 1_i * l + 1_i * new_acc >= 1_i),
                model.add_labelled_constraint(id, stem + "_0_1", WPBSum{} + 1_i * acc + 1_i * ! l + 1_i * new_acc >= 1_i)});
        result.accumulators.push_back(new_acc);
        acc = new_acc;
        not_acc = ! new_acc;
    }
    result.an_le_0 = model.add_labelled_constraint(id, role_prefix + "acc", WPBSum{} + -1_i * acc >= 0_i);

    return result;
}

auto gcs::innards::derive_parity_slack_rows(ProofLogger & logger, const ParityChainRows & chain, const Literals & lits, const string & flag_stem)
    -> optional<pair<ProofLine, ProofLine>>
{
    if (lits.empty())
        return nullopt;

    auto & tracker = logger.names_and_ids_tracker();

    // Per step, a fresh y_k with a_{k-1} + l_k + a_k = 2 y_k, in two halves.
    // Neither half is RUP --- unit propagation cannot do parity --- so both are
    // redundance steps, and the order matters for cost: this way round the
    // first is goal-free and the second needs a five-line subproof, whereas
    // swapping them makes the first free and the second seven.
    vector<ProofLine> d1_lines, d2_lines;
    for (const auto & [k, l] : enumerate(lits)) {
        const auto & a = chain.accumulators[k];
        const auto & a_next = chain.accumulators[k + 1];
        auto y = logger.create_proof_flag(flag_stem + "y" + to_string(k + 1));

        // 2y >= a + l + a'. The only goal is on the constraint itself, and
        // reads a + l + a' <= 2, which is the step's own 1_1 clause; the goals
        // on the formula are vacuous because y is fresh, so nothing already in
        // the database mentions it.
        auto d1 = logger.emit_red_proof_line(WPBSum{} + 2_i * y + -1_i * a + -1_i * l + -1_i * a_next >= 0_i, {{y, TrueLiteral{}}}, ProofLevel::Top);

        // a + l + a' >= 2y. The goal on the constraint itself is trivial; the
        // one that is not is d1 under y = 0, namely a + l + a' <= 0, and that
        // is where the parity argument lives. Inside the subproof the negation
        // of the constraint being added sits one line below the negated goal,
        // and the three divisions below are what unit propagation cannot do.
        map<ProofGoal, Subproof> subproofs;
        subproofs.emplace(d1, Subproof{[&](ProofLogger & sub_logger) {
            // The negated goal is the last line added as the subproof opens,
            // and the negation of the constraint the `red` is adding sits one
            // before it. Both have to be captured here and used as absolute
            // references: a relative one would still say -1 several lines
            // later, by which point it means something else entirely.
            auto negated_goal = sub_logger.get_current_proof_line();
            auto negated_constraint = ProofLineNumber{negated_goal.number - 1};

            PolBuilder s1;
            s1.add(negated_constraint).add(! tracker.xliteral_for(y), 2_i, tracker);
            auto s1_line = s1.emit(sub_logger, ProofLevel::Temporary);

            vector<ProofLine> units;
            for (const auto & clause : {chain.steps[k].c00, chain.steps[k].c10, chain.steps[k].c01}) {
                PolBuilder unit;
                unit.add(s1_line).add(clause).divide_by(2_i);
                units.push_back(unit.emit(sub_logger, ProofLevel::Temporary));
            }

            // The three units sum to the goal; adding the negated goal turns
            // that into the contradiction a proofgoal block has to end on.
            PolBuilder contradiction;
            for (const auto & unit : units)
                contradiction.add(unit);
            contradiction.add(negated_goal);
            contradiction.emit(sub_logger, ProofLevel::Temporary);
        }});

        auto d2 = logger.emit_red_proof_line(
            WPBSum{} + 1_i * a + 1_i * l + 1_i * a_next + -2_i * y >= 0_i, {{y, FalseLiteral{}}}, ProofLevel::Top, subproofs);

        d1_lines.push_back(d1);
        d2_lines.push_back(d2);
    }

    // Telescoping: every interior accumulator appears in two consecutive steps,
    // so with coefficient 2, which is even and therefore part of B. The two
    // boundary rows each go with exactly one direction --- the d2 sum carries
    // +a_n and only `acc` supplies -a_n, the d1 sum carries -a_n and only the
    // literal axiom supplies +a_n --- so this placement is forced, not chosen.
    PolBuilder ge;
    for (const auto & d2 : d2_lines)
        ge.add(d2);
    ge.add(chain.a0_le_1).add(chain.an_le_0);
    auto ge_line = ge.emit(logger, ProofLevel::Top);

    PolBuilder le;
    for (const auto & d1 : d1_lines)
        le.add(d1);
    le.add(chain.a0_ge_1).add(tracker.xliteral_for(chain.accumulators.back()), tracker);
    auto le_line = le.emit(logger, ProofLevel::Top);

    return make_optional(pair{ge_line, le_line});
}
