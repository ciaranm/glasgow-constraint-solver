#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/constraints/circuit/circuit_base.hh>
#include <gcs/constraints/circuit/circuit_scc.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/propagators.hh>
#include <util/enumerate.hh>

#include <list>
#include <map>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <variant>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
using std::format;
#else
#include <fmt/core.h>
using fmt::format;
#endif

using std::cmp_less;
using std::cmp_less_equal;
using std::cmp_not_equal;
using std::list;
using std::make_optional;
using std::map;
using std::min;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::circuit;

namespace
{
    struct OrderingAssumption
    {
        ProofFlag assumption_flag;
        long first;
        long middle;
        long last;
    };

    auto select_root(long) -> long
    {
        // Might have better root selection in future
        return 0;
    }

    struct SCCPropagatorData
    {
        // Data required for the modified Tarjan SCC Propagator
        long count;
        vector<long> lowlink;
        vector<long> visit_number;
        long start_prev_subtree;
        long end_prev_subtree;
        long root;
        long prev_subroot;

        explicit SCCPropagatorData(size_t n) :
            count(1),
            lowlink(vector<long>(n, -1)),
            visit_number(vector<long>(n, -1)),
            start_prev_subtree(0),
            end_prev_subtree(0),
            root(select_root(n)),
            prev_subroot(root)
        {
            lowlink[root] = 0;
            visit_number[root] = 0;
        }
    };

    struct SCCProofData
    {
        PosVarDataMap & pos_var_data;
        ConstraintStateHandle proof_flag_data_handle;
        ConstraintStateHandle pos_alldiff_data_handle;
    };

    struct SCCProofContext
    {
        const State & state;
        ProofLogger & logger;
        const ReasonFunction & reason;
        const vector<IntegerVariableID> & succ;
        const long root;
        PosVarDataMap & pos_var_data;
        map<long, ShiftedPosDataMaps> & flag_data;
        ShiftedPosDataMaps & root_flag_data;
        PosAllDiffData & pos_alldiff_data;
        const SCCOptions & options;

        SCCProofContext(const State & state, ProofLogger & logger, const ReasonFunction & reason, const vector<IntegerVariableID> & succ,
            SCCProofData & proof_data, const long root, const SCCOptions & options) :
            state(state),
            logger(logger),
            reason(reason),
            succ(succ),
            root(root),
            pos_var_data(proof_data.pos_var_data),
            flag_data(any_cast<map<long, ShiftedPosDataMaps> &>(
                state.get_persistent_constraint_state(proof_data.proof_flag_data_handle))),
            root_flag_data(flag_data[root]),
            pos_alldiff_data(any_cast<PosAllDiffData &>(
                state.get_persistent_constraint_state(proof_data.pos_alldiff_data_handle))),
            options(options)
        {
        }

        SCCProofContext(SCCProofContext & other, const long root) :
            state(other.state),
            logger(other.logger),
            reason(other.reason),
            succ(other.succ),
            root(root),
            pos_var_data(other.pos_var_data),
            flag_data(other.flag_data),
            root_flag_data(flag_data[root]),
            pos_alldiff_data(other.pos_alldiff_data),
            options(other.options)
        {
        }
    };

    // Running-saturate add: the first push is plain, every subsequent push
    // is followed by `s`. Matches the historical PLine.add_and_saturate
    // pattern this file used everywhere — preserved here rather than tidied
    // because some sums combine non-clause-shaped bounds, where the
    // intermediate `s` can shrink coefficients and the final result is not
    // necessarily equal to saturate-at-end.
    auto add_sat(PolBuilder & p, ProofLine line) -> PolBuilder &
    {
        return p.empty() ? p.add(line) : p.add(line).saturate();
    }

    auto pos_min(const long a, const long b)
    {
        // Take the min of a and b, unless one of them is -1 (representing undefined)
        if (b == -1)
            return a;
        else if (a == -1)
            return b;
        else
            return min(a, b);
    }

    auto prove_not_both(SCCProofContext & ctx, long i, long l, long k, const bool using_shifted_pos) -> ProofLine
    {
        // Prove that (shift)pos[i] != l \/ (shift)pos[i] != k
        ProofLine neq_line{};

        if (using_shifted_pos) {
            auto & shifted_pos_eq = ctx.root_flag_data.shifted_pos_eq;
            auto & shifted_pos_geq = ctx.root_flag_data.shifted_pos_geq;

            if (shifted_pos_eq[i][l].neq_lines.contains(k)) {
                // Don't reprove this if we did it before
                return shifted_pos_eq[i][l].neq_lines[k];
            }

            // Assumes l < k
            PolBuilder p_line;
            add_sat(p_line, shifted_pos_geq[i][k].forwards_reif_line);
            add_sat(p_line, shifted_pos_geq[i][l + 1].backwards_reif_line);
            p_line.emit(ctx.logger, ProofLevel::Temporary);

            ctx.logger.emit_proof_comment(format("Not both: {}={} and {}={}",
                shifted_pos_eq[i][k].comment_name, k,
                shifted_pos_eq[i][l].comment_name, l));

            neq_line = ctx.logger.emit_rup_proof_line(
                WPBSum{} + 1_i * ! shifted_pos_eq[i][k].flag + 1_i * ! shifted_pos_eq[i][l].flag >= 1_i,
                ProofLevel::Top);

            shifted_pos_eq[i][l].neq_lines[k] = neq_line;
        }
        else {
            auto & shifted_pos = ctx.root_flag_data.shifted_pos_eq;
            if (shifted_pos[i][l].neq_lines.contains(k)) {
                // Don't reprove this if we did it before
                return shifted_pos[i][l].neq_lines[k];
            }

            ctx.logger.emit_proof_comment(format("Not both:{}={} and {}={}",
                ctx.pos_var_data.at(i).comment_name, k,
                ctx.pos_var_data.at(i).comment_name, l));

            neq_line = ctx.logger.emit_rup_proof_line(
                WPBSum{} + 1_i * (ctx.pos_var_data.at(i).var != Integer{k}) + 1_i * (ctx.pos_var_data.at(i).var != Integer{l}) >= 1_i,
                ProofLevel::Top);

            shifted_pos[i][l].neq_lines[k] = neq_line;
        }
        return neq_line;
    }

    auto prove_at_most_1_pos_using_clique(SCCProofContext & ctx, const long & node, const set<long> & values, bool using_shifted_pos) -> ProofLine
    {
        // Prove that at most one (shift)pos[node] == v is true for v in values
        // We should document properly why this works somewhere now that it's in more than one place
        // Essentially, we can always recover an at most 1 constraint from a clique of "not both" constraints.
        if (values.size() > 1) {
            PolBuilder pol;
            auto k = ++values.begin();
            auto l = values.begin();
            pol.add(prove_not_both(ctx, node, (*l), (*k), using_shifted_pos));
            k++;
            auto k_count = 2;
            while (k != values.end()) {
                pol.multiply_by(Integer{k_count});
                l = values.begin();
                while (l != k) {
                    pol.add(prove_not_both(ctx, node, (*l), (*k), using_shifted_pos));
                    l++;
                }
                pol.divide_by(Integer{k_count + 1});
                k++;
                k_count++;
            }

            if (using_shifted_pos)
                ctx.logger.emit_proof_comment("AM1 " + ctx.root_flag_data.shifted_pos_eq[node][*values.begin()].comment_name);
            else
                ctx.logger.emit_proof_comment(format("AM1 p[{}]", node));

            return pol.emit(ctx.logger, ProofLevel::Top);
        }
        else if (values.size() == 1) {
            auto idx = *values.begin();
            if (using_shifted_pos) {
                ctx.logger.emit_proof_comment("AM1 " +
                    ctx.root_flag_data.shifted_pos_eq[node][*values.begin()].comment_name);
                return ctx.logger.emit_rup_proof_line(
                    WPBSum{} + 1_i * ! (ctx.root_flag_data.shifted_pos_eq[node][idx].flag) >= 0_i,
                    ProofLevel::Top);
            }
            else {
                ctx.logger.emit_proof_comment(format("AM1 p[{}]", node));
                return ctx.logger.emit_rup_proof_line(
                    WPBSum{} + 1_i * ! (ctx.pos_var_data.at(node).var == Integer{idx}) >= 0_i,
                    ProofLevel::Top);
            }
        }
        else
            throw UnexpectedException{"trying to prove an AM1 over zero values?"};
    }

    auto prove_at_most_1_pos_using_contradiction(SCCProofContext & ctx, const long & node, const set<long> & values, bool using_shifted_pos) -> ProofLine
    {
        auto am1_sum = WPBSum{};
        if (using_shifted_pos) {
            for (const auto & val : values) {
                am1_sum += -1_i * ctx.root_flag_data.shifted_pos_eq[node][val].flag;
            }

            map<ProofGoal, Subproof> subproofs{};

            auto subproof = [&](ProofLogger & logger) {
                auto geq_data = ctx.root_flag_data.shifted_pos_geq;
                for (auto it = values.begin(); next(it) != values.end(); ++it) {
                    long val = *it;
                    auto next_val = *next(it);
                    auto geq_this_val = geq_data.at(node).at(val);
                    auto geq_this_val_plus_1 = geq_data.at(node).at(val + 1);
                    auto geq_next_val = geq_data.at(node).at(next_val);
                    auto geq_next_val_plus_1 = geq_data.at(node).at(next_val + 1);
                    PolBuilder{}
                        .add(geq_this_val.backwards_reif_line)
                        .add(geq_next_val.forwards_reif_line)
                        .emit(logger, ProofLevel::Temporary);
                    PolBuilder{}
                        .add(geq_this_val_plus_1.backwards_reif_line)
                        .add(geq_next_val.forwards_reif_line)
                        .emit(logger, ProofLevel::Temporary);
                }
                for (auto it = values.begin(); it != values.end(); ++it) {
                    long val = *it;
                    logger.emit_rup_proof_line(WPBSum{} + -1_i * ctx.root_flag_data.shifted_pos_eq[node][val].flag >= 0_i, ProofLevel::Temporary);
                }
                logger.emit_proof_line("rup >= 1;", ProofLevel::Temporary);
            };

            subproofs.emplace("#1", subproof);

            return ctx.logger.emit_red_proof_line(am1_sum >= -1_i, {}, ProofLevel::Top, subproofs);
        }
        else {
            for (const auto & val : values) {
                am1_sum += -1_i * (ctx.pos_var_data.at(node).var == Integer(val));
            }

            map<ProofGoal, Subproof> subproofs{};

            auto subproof = [&](ProofLogger & logger) {
                for (auto it = values.begin(); it != values.end(); ++it) {
                    long val = *it;
                    logger.emit_rup_proof_line(WPBSum{} + -1_i * (ctx.pos_var_data.at(node).var == Integer(val)) >= 0_i, ProofLevel::Temporary);
                }
                logger.emit_proof_line("rup >= 1;", ProofLevel::Temporary);
            };

            subproofs.emplace("#1", subproof);

            return ctx.logger.emit_red_proof_line(am1_sum >= -1_i, {}, ProofLevel::Top, subproofs);
        }
    }

    auto prove_at_most_1_pos(SCCProofContext & ctx, const long & node, const set<long> & values, bool using_shifted_pos) -> ProofLine
    {
        if (ctx.options.prove_am1_by_contradiction) {
            return prove_at_most_1_pos_using_contradiction(ctx, node, values, using_shifted_pos);
        }
        else {
            return prove_at_most_1_pos_using_clique(ctx, node, values, using_shifted_pos);
        }
    }

    auto prove_pos_alldiff_lines(SCCProofContext & ctx) -> void
    {
        // Recover an all different constraint (al1/am1) over the pos variables
        // This is O(n^3) where n is the number of variables in the circuit but only needs to be done once.
        auto n = static_cast<long>(ctx.succ.size());

        // First prove the at least 1 lines
        ctx.logger.emit_proof_comment("Pos all diff lines:");
        WPBSum pb_sum;
        for (long i = 0; i < n; i++) {
            pb_sum += 1_i * (ctx.pos_var_data.at(i).var == 0_i);
        }
        ctx.logger.emit_proof_comment("AL1 p[i] = 0");
        ctx.pos_alldiff_data.at_least_1_lines[0] =
            ctx.logger.emit_rup_proof_line(pb_sum >= 1_i, ProofLevel::Top);
        auto last_al1_line = ctx.pos_alldiff_data.at_least_1_lines[0];
        for (long j = 1; j < n; j++) {
            pb_sum = WPBSum{};
            PolBuilder p_line;
            for (long i = 0; i < n; i++) {
                auto next_pos_vars = WPBSum{};
                for (long k = 0; k < n; k++) {
                    next_pos_vars += 1_i * (ctx.pos_var_data.at(k).var == Integer{j});
                    ctx.logger.emit_rup_proof_line(
                        WPBSum{} + 1_i * ! (ctx.pos_var_data.at(i).var == Integer{j - 1}) +
                                1_i * ! (ctx.succ[i] == Integer{k}) + 1_i * (ctx.pos_var_data.at(k).var == Integer{j}) >=
                            1_i,
                        ProofLevel::Top);
                }

                add_sat(p_line,
                    ctx.logger.emit_rup_proof_line(
                        next_pos_vars + 1_i * ! (ctx.pos_var_data.at(i).var == Integer{j - 1}) >= 1_i, ProofLevel::Top));
            }
            ctx.logger.emit_proof_comment(format("AL1 p[i] = {}", j));
            add_sat(p_line, last_al1_line);
            ctx.pos_alldiff_data.at_least_1_lines[j] = p_line.emit(ctx.logger, ProofLevel::Top);
            last_al1_line = ctx.pos_alldiff_data.at_least_1_lines[j];
        }

        // Now prove the at most 1 lines
        for (long i = 0; i < n; i++) {
            set<long> values{};
            for (int j = 0; j < n; j++) {
                values.insert(j);
            }
            // Need to use ctx.root = 0 here to make sure flag data for root isn't overwritten ?
            auto temp_ctx = SCCProofContext(ctx, 0);
            ctx.pos_alldiff_data.at_most_1_lines.emplace(i, prove_at_most_1_pos(temp_ctx, i, values, false));
        }
    }

    auto create_flag_for_greater_than(SCCProofContext & ctx, const long j, const long i) -> ProofFlagData
    {
        // Create a flag which is reified as follows:
        // d[j, i] => p[j] - p[i] >= 1
        // ~d[j, i] => p[i] - p[j] >= 1
        // This requires us to essentially prove p[j] != p[i] in a redundance subproof

        auto & gt_data = ctx.flag_data[j].greater_than;
        ProofFlag greater_than_flag{};

        if (gt_data.contains(i)) {
            // If it was already defined, don't redefine it
            return gt_data.at(i);
        }
        else {
            auto flag_name = format("d[{}][{}]", ctx.root, i);
            greater_than_flag = ctx.logger.create_proof_flag(flag_name);

            auto forwards_reif_line = ctx.logger.emit_red_proof_lines_forward_reifying(
                WPBSum{} + 1_i * ctx.pos_var_data.at(j).var + -1_i * ctx.pos_var_data.at(i).var >= 1_i,
                greater_than_flag, ProofLevel::Top);

            if (ctx.pos_alldiff_data.at_least_1_lines.empty()) {
                prove_pos_alldiff_lines(ctx);
            }

            ProofLine backwards_reif_line;
            if (i != j) {
                // Redundance subproof:
                auto subproofs = make_optional(map<ProofGoal, Subproof>{});
                auto subproof = [&](ProofLogger & logger) {
                    logger.emit_proof_line("pol -2 " + logger.names_and_ids_tracker().pb_file_string_for(greater_than_flag) + " w;", ProofLevel::Top);
                    for (long k = 0; cmp_less(k, ctx.succ.size()); k++) {
                        PolBuilder p_line;
                        // Prove p[i] = k is not possible
                        // First add all AL1 lines except for k
                        for (const auto & [val, al1_line] : ctx.pos_alldiff_data.at_least_1_lines) {
                            if (val == k) continue;
                            add_sat(p_line, al1_line);
                        }

                        // Now add all AM1 lines except for i and j
                        for (const auto & my_pair : ctx.pos_alldiff_data.at_most_1_lines) {
                            if (my_pair.first == i || my_pair.first == j) {
                                continue;
                            }
                            add_sat(p_line, my_pair.second);
                        }
                        p_line.emit(logger, ProofLevel::Top);
                        logger.emit_rup_proof_line(WPBSum{} + 1_i * ! (ctx.pos_var_data.at(i).var == Integer{k}) >= 1_i, ProofLevel::Top);
                    }
                    logger.emit_rup_proof_line(WPBSum{} >= 1_i, ProofLevel::Top);
                };
                subproofs.value().emplace(forwards_reif_line, subproof);

                backwards_reif_line = ctx.logger.emit_red_proof_lines_reverse_reifying(
                    WPBSum{} + 1_i * ctx.pos_var_data.at(j).var + -1_i * ctx.pos_var_data.at(i).var >= 0_i,
                    greater_than_flag, ProofLevel::Top, subproofs);
            }
            else {
                // If i == root, d[r, i] is just "false"
                // I think this should maybe be forwards, but it's working anyway???
                backwards_reif_line = ctx.logger.emit_red_proof_lines_reverse_reifying(
                    WPBSum{} + 1_i * ctx.pos_var_data.at(j).var + -1_i * ctx.pos_var_data.at(i).var >= 1_i,
                    greater_than_flag, ProofLevel::Top);
            }

            gt_data[i] = ProofFlagData{
                flag_name, greater_than_flag, forwards_reif_line, backwards_reif_line, {}};
            return gt_data[i];
        }
    }

    auto create_shifted_pos(SCCProofContext & ctx, const long i, const long dist)
    {
        // Define a "shifted" pos flag q[r, i], that represents the value of p[i] shifted relative to p[root] mod n
        // i.e. q[r, i] == j <=> p[i] - p[r] + n * d[r, i] (the last term corrects for when we go negative)
        auto n = static_cast<long>(ctx.succ.size());
        ProofFlagData greater_than_flag_data{};

        greater_than_flag_data = create_flag_for_greater_than(ctx, ctx.root, i);
        auto greater_than_flag = greater_than_flag_data.flag;

        auto maybe_create_and_emplace_flag_data =
            [&ctx](ProofFlagDataMap & flag_data, const long i, const long dist, const WPBSumLE & definition, const string & name, const string & name_suffix) {
                if (! flag_data[i].contains(dist)) {
                    auto [flag, forwards_reif_line, backwards_reif_line] = ctx.logger.create_proof_flag_reifying(definition, name + name_suffix, ProofLevel::Top);
                    flag_data[i][dist] = ProofFlagData{name, flag, forwards_reif_line, backwards_reif_line, {}};
                }
            };

        // q[r,i]gej <=> pos[i] - pos[r] + nd[r,i] >= j
        maybe_create_and_emplace_flag_data(ctx.root_flag_data.shifted_pos_geq, i, dist,
            WPBSum{} + 1_i * ctx.pos_var_data.at(i).var + -1_i * ctx.pos_var_data.at(ctx.root).var + Integer{n} * greater_than_flag >= Integer{dist},
            format("q[{}][{}]", ctx.root, i), format("ge{}", dist));

        // q[r,i]gej+1 <=> pos[i] - pos[r] + nd[r,i] >= j+1
        maybe_create_and_emplace_flag_data(ctx.root_flag_data.shifted_pos_geq, i, dist + 1,
            WPBSum{} + 1_i * ctx.pos_var_data.at(i).var + -1_i * ctx.pos_var_data.at(ctx.root).var + Integer{n} * greater_than_flag >= Integer{dist + 1},
            format("q[{}][{}]", ctx.root, i), format("ge{}", dist + 1));

        // q[r,i]eqj <=> q[r,i]gej /\ ~q[r,i]gej+1
        maybe_create_and_emplace_flag_data(ctx.root_flag_data.shifted_pos_eq, i, dist,
            WPBSum{} + 1_i * ctx.root_flag_data.shifted_pos_geq[i][dist].flag + 1_i * ! ctx.root_flag_data.shifted_pos_geq[i][dist + 1].flag >= 2_i,
            format("q[{}][{}]", ctx.root, i), format("eq{}", dist));
    }

    auto prove_root_is_0(SCCProofContext & ctx) -> ProofLine
    {
        // Prove that (shift)pos[root]== 0
        ctx.logger.emit_proof_comment("AL1 pos = 0");

        auto line = ProofLine{};
        if (ctx.root != 0) {
            create_shifted_pos(ctx, ctx.root, 0);
            line = ctx.logger.emit_rup_proof_line(
                WPBSum{} + 1_i * ctx.root_flag_data.shifted_pos_eq[ctx.root][0].flag >= 1_i,
                ProofLevel::Current);
        }
        else {
            line = ctx.logger.emit_rup_proof_line(
                WPBSum{} + 1_i * (ctx.pos_var_data.at(ctx.root).var == 0_i) >= 1_i,
                ProofLevel::Current);
        }

        return line;
    }

    auto prove_mid_is_at_least(SCCProofContext & ctx,
        const OrderingAssumption & ordering, const long & val, const Literal & assumption)
    {
        // The ordering assumption assumes we will see "middle" before "last" when we start at "first"
        // If we haven't seen middle yet under our assumptions we can prove (shift)pos[middle] >= val
        auto & mid = ordering.middle;
        ctx.logger.emit_proof_comment("Haven't seen mid node yet:");
        if (ctx.root != 0) {
            create_shifted_pos(ctx, mid, val);

            if (val == 1) {
                PolBuilder p_line;
                add_sat(p_line, ctx.root_flag_data.shifted_pos_geq[mid][1].backwards_reif_line);
                add_sat(p_line, ctx.root_flag_data.greater_than[mid].backwards_reif_line);
                p_line.emit(ctx.logger, ProofLevel::Temporary);
            }

            ctx.logger.emit_rup_proof_line_under_reason(ctx.reason,
                WPBSum{} + 1_i * ! ordering.assumption_flag + 1_i * ! assumption + 1_i * ctx.root_flag_data.shifted_pos_geq[mid][val].flag >= 1_i,
                ProofLevel::Current);
        }
        else {
            ctx.logger.emit_rup_proof_line_under_reason(ctx.reason,
                WPBSum{} + 1_i * (ctx.pos_var_data.at(mid).var >= Integer{val}) >= 1_i,
                ProofLevel::Current);
        }
    }

    auto prove_pos_and_node_implies_next_node(SCCProofContext & ctx, const long & node, const long & next_node, const long & count)
    {
        // successor_implies_line := Prove (shift)pos[node][count - 1] /\ succ[node] = next_node => (shift)pos[next_node][count]
        auto successor_implies_line = ProofLine{};
        auto n = static_cast<long>(ctx.succ.size());

        if (ctx.root != 0) {

            create_shifted_pos(ctx, next_node, count);
            auto & root_greater_than = ctx.root_flag_data.greater_than;
            auto & shifted_pos_geq = ctx.root_flag_data.shifted_pos_geq;
            auto & shifted_pos_eq = ctx.root_flag_data.shifted_pos_eq;

            // Some painful adding up to get us to rup what we want
            // Need to document that this always works
            // --- Update 2026, now finally documented in my thesis :-)
            if (next_node != ctx.root) {
                PolBuilder p_line;
                // aaaa so many edge cases
                if (next_node != 0) {
                    p_line.add(ctx.pos_var_data.at(node).plus_one_lines.at(next_node).leq_line)
                        .add(root_greater_than.at(node).forwards_reif_line)
                        .add(root_greater_than.at(next_node).backwards_reif_line)
                        .divide_by(Integer{2 * n});
                }
                else {
                    p_line.add(ctx.logger.emit_rup_proof_line(
                        WPBSum{} + 1_i * ! (ctx.succ[node] == Integer{next_node}) + 1_i * ! root_greater_than.at(node).flag >= 1_i,
                        ProofLevel::Temporary));
                    p_line.add(ctx.logger.emit_rup_proof_line(
                        WPBSum{} + 1_i * ! (ctx.succ[node] == Integer{next_node}) + 1_i * root_greater_than.at(next_node).flag >= 1_i,
                        ProofLevel::Temporary));
                }

                p_line.multiply_by(Integer{n})
                    .add(ctx.pos_var_data.at(node).plus_one_lines.at(next_node).geq_line)
                    .add(shifted_pos_geq.at(node).at(count - 1).forwards_reif_line)
                    .add(shifted_pos_geq.at(next_node).at(count).backwards_reif_line)
                    .emit(ctx.logger, ProofLevel::Temporary);

                PolBuilder{}
                    .add(ctx.pos_var_data.at(node).plus_one_lines.at(next_node).geq_line)
                    .add(root_greater_than.at(node).backwards_reif_line)
                    .add(root_greater_than.at(next_node).forwards_reif_line)
                    .divide_by(Integer{2 * n})
                    .multiply_by(Integer{n})
                    .add(ctx.pos_var_data.at(node).plus_one_lines.at(next_node).leq_line)
                    .add(shifted_pos_geq.at(node).at(count).backwards_reif_line)
                    .add(shifted_pos_geq.at(next_node).at(count + 1).forwards_reif_line)
                    .emit(ctx.logger, ProofLevel::Temporary);

                ctx.logger.emit_proof_comment(format("Next implies: succ[{}] = {} and {} = {} => {} = {}",
                    node, next_node,
                    shifted_pos_eq[node][count - 1].comment_name, count - 1,
                    shifted_pos_eq[next_node][count].comment_name, count));

                // RUP shifted_pos[node][count-1] /\ succ[node] = next_node => shifted_pos[next_node][i]
                successor_implies_line = ctx.logger.emit_rup_proof_line_under_reason(ctx.reason,
                    WPBSum{} + 1_i * shifted_pos_eq[next_node][count].flag + 1_i * (ctx.succ[node] != Integer{next_node}) +
                            1_i * (! shifted_pos_eq[node][count - 1].flag) >=
                        1_i,
                    ProofLevel::Current);
            }
            else {
                PolBuilder{}
                    .add(shifted_pos_geq[node][count - 1].forwards_reif_line)
                    .add(ctx.pos_var_data.at(node).plus_one_lines.at(next_node).geq_line)
                    .saturate()
                    .emit(ctx.logger, ProofLevel::Temporary);
                PolBuilder{}
                    .add(shifted_pos_geq[node][count].backwards_reif_line)
                    .add(ctx.pos_var_data.at(node).plus_one_lines.at(next_node).leq_line)
                    .saturate()
                    .emit(ctx.logger, ProofLevel::Temporary);

                ctx.logger.emit_proof_comment(format("Next implies: succ[{}] = {} and {} = {} => 0 >= 1",
                    node, next_node,
                    shifted_pos_eq[node][count - 1].comment_name, count - 1));

                successor_implies_line = ctx.logger.emit_rup_proof_line(WPBSum{} + 1_i * (! shifted_pos_eq[node][count - 1].flag) + 1_i * (ctx.succ[node] != Integer{next_node}) >= 1_i, ProofLevel::Current);
            }
        }
        else {
            // Not using shifted pos, just use the actual pos values
            // succ[node] == next_node /\ pos[node] == count - 1 => pos[next_node] == count
            successor_implies_line = ctx.logger.emit_rup_proof_line(
                WPBSum{} + 1_i * (ctx.pos_var_data.at(node).var != Integer{count - 1}) +
                        1_i * (ctx.succ[node] != Integer{next_node}) + 1_i * (ctx.pos_var_data.at(next_node).var == Integer{count}) >=
                    1_i,
                ProofLevel::Current);
        }

        return successor_implies_line;
    }

    auto prove_not_same_val(SCCProofContext & ctx, const long & middle, const long & next_node, const long & count)
    {
        auto succesor_implies_not_mid_line = ProofLine{};
        // successor_implies_line :=
        // Prove (shift)pos[next_node][count] => ! (shift)pos[mid][count]
        create_shifted_pos(ctx, middle, count);
        ctx.logger.emit_proof_comment("Successor implies not mid");
        auto n = static_cast<long>(ctx.succ.size());
        if (ctx.root != 0) {
            create_flag_for_greater_than(ctx, next_node, middle);

            PolBuilder temp_p_line;

            auto & shifted_pos_geq = ctx.flag_data[ctx.root].shifted_pos_geq;
            auto & shifted_pos_eq = ctx.flag_data[ctx.root].shifted_pos_eq;

            ctx.logger.emit_proof_comment("Step 1");

            add_sat(temp_p_line, shifted_pos_geq[next_node][count + 1].backwards_reif_line);
            add_sat(temp_p_line, shifted_pos_geq[middle][count].forwards_reif_line);
            auto geq_and_leq = temp_p_line.emit(ctx.logger, ProofLevel::Temporary);

            add_sat(temp_p_line, shifted_pos_geq[next_node][count].forwards_reif_line);
            add_sat(temp_p_line, shifted_pos_geq[middle][count + 1].backwards_reif_line);
            ctx.logger.emit_proof_comment("Step 2");
            auto leq_and_geq = temp_p_line.emit(ctx.logger, ProofLevel::Temporary);

            add_sat(temp_p_line, geq_and_leq);
            add_sat(temp_p_line, ctx.flag_data[next_node].greater_than[middle].forwards_reif_line);
            ctx.logger.emit_proof_comment("Step 3");
            temp_p_line.emit(ctx.logger, ProofLevel::Temporary);

            add_sat(temp_p_line, leq_and_geq);
            add_sat(temp_p_line, ctx.logger.emit_rup_proof_line(
                WPBSum{} + -1_i * ctx.pos_var_data.at(next_node).var + 1_i * ctx.pos_var_data.at(middle).var >= Integer{-n + 1}, ProofLevel::Temporary));
            ctx.logger.emit_proof_comment("Step 4");
            temp_p_line.emit(ctx.logger, ProofLevel::Temporary);

            ctx.logger.emit_proof_comment("Step 5");
            ctx.logger.emit_rup_proof_line_under_reason(ctx.reason,
                WPBSum{} +
                        1_i * ! ctx.flag_data[ctx.root].greater_than[middle].flag +
                        1_i * ! ctx.flag_data[next_node].greater_than[middle].flag +
                        1_i * ! shifted_pos_eq[middle][count].flag +
                        1_i * (! shifted_pos_eq[next_node][count].flag) >=
                    1_i,
                ProofLevel::Temporary);

            ctx.logger.emit_rup_proof_line_under_reason(ctx.reason,
                WPBSum{} +
                        1_i * ! ctx.flag_data[next_node].greater_than[middle].flag +
                        1_i * ! shifted_pos_eq[middle][count].flag +
                        1_i * (! shifted_pos_eq[next_node][count].flag) >=
                    1_i,
                ProofLevel::Temporary);

            add_sat(temp_p_line, leq_and_geq);
            add_sat(temp_p_line, ctx.flag_data[next_node].greater_than[middle].backwards_reif_line);
            ctx.logger.emit_proof_comment("Step 6");
            temp_p_line.emit(ctx.logger, ProofLevel::Temporary);

            add_sat(temp_p_line, geq_and_leq);
            add_sat(temp_p_line, ctx.logger.emit_rup_proof_line(
                WPBSum{} + -1_i * ctx.pos_var_data.at(middle).var + 1_i * ctx.pos_var_data.at(next_node).var >= Integer{-n + 1}, ProofLevel::Temporary));
            ctx.logger.emit_proof_comment("Step 7");
            temp_p_line.emit(ctx.logger, ProofLevel::Temporary);

            ctx.logger.emit_rup_proof_line_under_reason(ctx.reason,
                WPBSum{} +
                        1_i * ! ctx.flag_data[ctx.root].greater_than[next_node].flag +
                        1_i * ctx.flag_data[next_node].greater_than[middle].flag +
                        1_i * ! shifted_pos_eq[middle][count].flag +
                        1_i * (! shifted_pos_eq[next_node][count].flag) >=
                    1_i,
                ProofLevel::Temporary);

            ctx.logger.emit_proof_comment("Step 8");
            ctx.logger.emit_rup_proof_line_under_reason(ctx.reason,
                WPBSum{} + 1_i * ! ctx.flag_data[next_node].greater_than[middle].flag +
                        1_i * ! shifted_pos_eq[middle][count].flag +
                        1_i * (! shifted_pos_eq[next_node][count].flag) >=
                    1_i,
                ProofLevel::Temporary);

            succesor_implies_not_mid_line = ctx.logger.emit_rup_proof_line_under_reason(ctx.reason,
                WPBSum{} + 1_i * ! shifted_pos_eq[middle][count].flag +
                        1_i * (! shifted_pos_eq[next_node][count].flag) >=
                    1_i,
                ProofLevel::Current);
        }
        else {
            succesor_implies_not_mid_line = ctx.logger.emit_rup_proof_line_under_reason(ctx.reason,
                WPBSum{} +
                        1_i * ! (ctx.pos_var_data.at(middle).var == Integer{count}) +
                        1_i * ! (ctx.pos_var_data.at(next_node).var == Integer{count}) >=
                    1_i,
                ProofLevel::Temporary);
        }

        return succesor_implies_not_mid_line;
    }

    auto prove_exclude_last_based_on_ordering(SCCProofContext & ctx, const OrderingAssumption & ordering, const long & root, const long & count,
        const Literal & assumption) -> ProofLine
    {
        // Based on an ordering assumption and the fact we haven't seen
        auto mid = ordering.middle;
        auto last = ordering.last;
        auto exclusion_line = ProofLine{};

        ctx.logger.emit_proof_comment("Exclude based on ordering");

        if (root != 0) {
            auto & shifted_pos_geq = ctx.flag_data[root].shifted_pos_geq;
            auto & shifted_pos_eq = ctx.flag_data[root].shifted_pos_eq;

            create_shifted_pos(ctx, mid, count);
            create_shifted_pos(ctx, root, last);
            PolBuilder p_line;

            add_sat(p_line, shifted_pos_geq[mid][count].forwards_reif_line);
            add_sat(p_line, shifted_pos_geq[last][count].backwards_reif_line);
            add_sat(p_line, ctx.flag_data[mid].greater_than[last].backwards_reif_line);

            add_sat(p_line, ctx.logger.emit_rup_proof_line(
                WPBSum{} + 1_i * ctx.flag_data[root].greater_than[last].flag + 1_i * ctx.flag_data[last].greater_than[root].flag >= 1_i,
                ProofLevel::Temporary));

            p_line.emit(ctx.logger, ProofLevel::Temporary);
            exclusion_line = ctx.logger.emit_rup_proof_line_under_reason(ctx.reason,
                WPBSum{} + 1_i * ! assumption + 1_i * ! ordering.assumption_flag + 1_i * ! shifted_pos_eq[last][count].flag >= 1_i,
                ProofLevel::Current);
        }
        else {
            exclusion_line = ctx.logger.emit_rup_proof_line_under_reason(ctx.reason,
                WPBSum{} + 1_i * ! assumption + 1_i * ! ordering.assumption_flag + 1_i * ! (ctx.pos_var_data.at(last).var == Integer{count}) >= 1_i,
                ProofLevel::Current);
        }

        return exclusion_line;
    }

    auto prove_reachable_set_too_small(SCCProofContext & ctx, const Literal & assumption = TrueLiteral{}, const optional<OrderingAssumption> & ordering = nullopt) -> void
    {
        ctx.logger.emit_proof_comment(format("REACHABLE SET from {}", ctx.root));

        map<long, set<long>> all_values_seen{};
        const auto using_shifted_pos = ctx.root != 0;

        all_values_seen[ctx.root].insert(0);
        PolBuilder contradiction_line;

        auto last_al1_line = prove_root_is_0(ctx);
        add_sat(contradiction_line, last_al1_line);

        if (ordering) {
            if (ordering.value().first != ctx.root) {
                throw UnexpectedException{"SCC Proof Error: First component of ordering assumption must be root of reachability argument."};
            }
            // Mid is not the root, so it must be at least 1
            prove_mid_is_at_least(ctx, ordering.value(), 1, assumption);
        }

        long count = 1;
        set<long> all_reached_nodes = {ctx.root};
        set<long> last_reached_nodes = {ctx.root};

        bool seen_middle = false;

        auto skip_based_on_assumption = [&](IntegerVariableID var, Integer val, Literal assumption) -> bool {
            return overloaded{
                [&](TrueLiteral) {
                    return false;
                },
                [&](FalseLiteral) {
                    return false;
                },
                [&](IntegerVariableCondition cond) {
                    if (cond.var == var) {
                        if ((cond.op == VariableConditionOperator::Equal && val != cond.value) ||
                            (cond.op == VariableConditionOperator::NotEqual && val == cond.value)) {
                            return true;
                        }
                        else if (cond.op == VariableConditionOperator::GreaterEqual || cond.op == VariableConditionOperator::Less) {
                            throw UnexpectedException{"Comparison assumptions not supported for reachability proof."};
                        }
                        else {
                            return false;
                        }
                    }
                    else {
                        if (cond.op == VariableConditionOperator::Equal && val == cond.value) {
                            return true;
                        }
                        else if (cond.op == VariableConditionOperator::GreaterEqual || cond.op == VariableConditionOperator::Less) {
                            throw UnexpectedException{"Comparison assumptions not supported for reachability proof."};
                        }
                        else {
                            return false;
                        }
                    }
                }}
                .visit(assumption);
        };

        // At least one lines
        while (cmp_less_equal(count, all_reached_nodes.size())) {
            PolBuilder add_for_at_least_1;
            add_sat(add_for_at_least_1, last_al1_line);
            int add_for_at_least_1_count = 1;
            PolBuilder add_for_not_mid;

            set<long> new_reached_nodes{};
            bool exclude_based_on_ordering = false;
            for (const auto & node : last_reached_nodes) {
                WPBSum possible_next_nodes_sum{};
                PolBuilder add_for_node_implies_at_least_1;
                PolBuilder add_for_node_implies_not_mid;

                for (auto val : ctx.state.each_value_immutable(ctx.succ[node])) {
                    if (skip_based_on_assumption(ctx.succ[node], val, assumption))
                        continue;

                    possible_next_nodes_sum += 1_i * (ctx.succ[node] == val);
                    auto next_node = val.raw_value;

                    all_values_seen[next_node].insert(count);

                    add_sat(add_for_node_implies_at_least_1,
                        prove_pos_and_node_implies_next_node(ctx, node, next_node, count));

                    if (ordering && next_node == ordering.value().last && ! seen_middle) {
                        // Ordering says that since we haven't seen "middle" yet, we can't visit "last"
                        exclude_based_on_ordering = true;
                    }
                    else if (ordering && ! seen_middle && next_node != ordering.value().middle) {
                        // If we see any other node, prove that we can't have middle == count for this
                        // node and pos combination
                        add_sat(add_for_node_implies_not_mid, prove_not_same_val(ctx, ordering.value().middle, next_node, count));
                        if (next_node != ctx.root)
                            new_reached_nodes.insert(next_node);
                    }
                    else if (ordering && next_node == ordering.value().middle) {
                        // Now we've seen "middle"
                        seen_middle = true;
                        new_reached_nodes.insert(next_node);
                    }
                    else if (next_node != ctx.root) {
                        new_reached_nodes.insert(next_node);
                    }
                }

                add_sat(add_for_node_implies_at_least_1,
                    ctx.logger.emit_rup_proof_line_under_reason(ctx.reason,
                        possible_next_nodes_sum + 1_i * ! assumption >= 1_i, ProofLevel::Temporary));

                add_sat(add_for_at_least_1,
                    add_for_node_implies_at_least_1.emit(ctx.logger, ProofLevel::Current));
                ++add_for_at_least_1_count;

                if (ordering && ! seen_middle) {
                    if (! add_for_node_implies_not_mid.empty()) {
                        add_sat(add_for_not_mid,
                            add_for_node_implies_not_mid.emit(ctx.logger, ProofLevel::Current));
                    }
                }
            }

            ctx.logger.emit_proof_comment(format("AL1 pos = {}", count));
            if (add_for_at_least_1_count > 1)
                add_for_at_least_1.divide_by(Integer{add_for_at_least_1_count});
            last_al1_line = add_for_at_least_1.emit(ctx.logger, ProofLevel::Current);
            if (exclude_based_on_ordering) {
                PolBuilder new_last_al1_line;
                add_sat(new_last_al1_line,
                    prove_exclude_last_based_on_ordering(ctx, ordering.value(), ctx.root, count, assumption));
                add_sat(new_last_al1_line, last_al1_line);
                last_al1_line = new_last_al1_line.emit(ctx.logger, ProofLevel::Current);
            }
            add_sat(contradiction_line, last_al1_line);

            if (ordering && ! seen_middle) {
                add_sat(add_for_not_mid, last_al1_line);
                ctx.logger.emit_proof_comment("Not mid");
                add_for_not_mid.emit(ctx.logger, ProofLevel::Current);
                prove_mid_is_at_least(ctx, ordering.value(), count + 1, assumption);
            }

            last_reached_nodes = new_reached_nodes;

            // Continue until we've logged more layers than we have reached nodes (Hall violator)
            all_reached_nodes.insert(new_reached_nodes.begin(), new_reached_nodes.end());
            count++;
        }

        // At most one lines
        for (const auto & node : all_reached_nodes) {
            add_sat(contradiction_line,
                prove_at_most_1_pos(ctx, node, all_values_seen[node], using_shifted_pos));
        }

        ctx.logger.emit_proof_comment("Hall violator gives contradiction: ");
        contradiction_line.emit(ctx.logger, ProofLevel::Current);
    }

    auto prove_skipped_subtree(SCCProofContext & ctx, const long node, const long next_node, const long skipped_subroot)
    {
        auto root_gt_next = create_flag_for_greater_than(ctx, ctx.root, next_node);
        auto subroot_gt_root = create_flag_for_greater_than(ctx, skipped_subroot, ctx.root);
        auto next_gt_subroot = create_flag_for_greater_than(ctx, next_node, skipped_subroot);

        auto node_then_subroot_then_root = ctx.logger.create_proof_flag_reifying(
            WPBSum{} + 1_i * ! root_gt_next.flag + 1_i * ! subroot_gt_root.flag + 1_i * ! next_gt_subroot.flag >= 2_i,
            "ord1", ProofLevel::Current);

        OrderingAssumption ordering1{
            get<0>(node_then_subroot_then_root),
            next_node,
            skipped_subroot,
            ctx.root};

        auto next_node_root_ctx = SCCProofContext(ctx, next_node);
        prove_reachable_set_too_small(next_node_root_ctx, ctx.succ[node] == Integer{next_node}, ordering1);

        auto subroot_gt_node = create_flag_for_greater_than(ctx, skipped_subroot, node);
        auto node_gt_root = create_flag_for_greater_than(ctx, node, ctx.root);

        auto subroot_then_node_then_root = ctx.logger.create_proof_flag_reifying(
            WPBSum{} + 1_i * ! subroot_gt_node.flag + 1_i * ! node_gt_root.flag + 1_i * subroot_gt_root.flag >= 2_i, "ord2", ProofLevel::Current);

        OrderingAssumption ordering2{
            get<0>(subroot_then_node_then_root),
            skipped_subroot,
            node,
            ctx.root};

        auto skipped_subroot_ctx = SCCProofContext(ctx, skipped_subroot);
        prove_reachable_set_too_small(skipped_subroot_ctx, ctx.succ[node] == Integer{next_node}, ordering2);

        PolBuilder{}
            .add(ctx.pos_var_data.at(node).plus_one_lines.at(next_node).geq_line)
            .add(root_gt_next.forwards_reif_line)
            .emit(ctx.logger, ProofLevel::Temporary);
        auto rup1 = ctx.logger.emit_rup_proof_line(
            WPBSum{} + 1_i * (ctx.succ[node] != Integer{next_node}) +
                    1_i * ! root_gt_next.flag + 1_i * ! node_gt_root.flag >=
                1_i,
            ProofLevel::Current);
        PolBuilder{}
            .add(ctx.pos_var_data.at(node).plus_one_lines.at(next_node).leq_line)
            .add(next_gt_subroot.forwards_reif_line)
            .add(subroot_gt_node.forwards_reif_line)
            .emit(ctx.logger, ProofLevel::Temporary);
        auto rup2 = ctx.logger.emit_rup_proof_line(
            WPBSum{} + 1_i * (ctx.succ[node] != Integer{next_node}) +
                    1_i * ! next_gt_subroot.flag + 1_i * ! subroot_gt_node.flag >=
                1_i,
            ProofLevel::Current);
        PolBuilder{}
            .add(rup1)
            .add(rup2)
            .add(get<2>(node_then_subroot_then_root))
            .add(get<2>(subroot_then_node_then_root))
            .saturate()
            .emit(ctx.logger, ProofLevel::Current);

        ctx.logger.emit_rup_proof_line_under_reason(ctx.reason,
            WPBSum{} + 1_i * (ctx.succ[node] != Integer{next_node}) >= 1_i, ProofLevel::Current);
    }

    auto explore(const State & state, auto & inference, ProofLogger * const logger, const ReasonFunction & reason,
        const long & node, const vector<IntegerVariableID> & succ, SCCPropagatorData & data, SCCProofData & proof_data,
        const SCCOptions & options)
        -> vector<pair<long, long>>
    {
        data.visit_number[node] = data.count;
        data.lowlink[node] = data.count;
        data.count++;

        vector<pair<long, long>> back_edges{};

        for (const auto & w : state.each_value_mutable(succ[node])) {
            auto next_node = w.raw_value;

            if (data.visit_number[next_node] == -1) {
                auto w_back_edges = explore(state, inference, logger, reason, next_node, succ, data, proof_data, options);
                back_edges.insert(back_edges.end(), w_back_edges.begin(), w_back_edges.end());
                data.lowlink[node] = pos_min(data.lowlink[node], data.lowlink[next_node]);
            }

            else {
                if (data.visit_number[next_node] >= data.start_prev_subtree && data.visit_number[next_node] <= data.end_prev_subtree) {
                    back_edges.emplace_back(node, next_node);
                }
                else if (options.prune_skip && data.visit_number[next_node] < data.start_prev_subtree) {
                    if (logger) {
                        if (next_node == data.root) {
                            logger->emit_proof_comment(format("Pruning edge to the root from a subtree other than the first ({}, {})", node, next_node));
                            auto ctx = SCCProofContext(state, *logger, reason, succ, proof_data, data.prev_subroot, options);
                            prove_reachable_set_too_small(ctx, succ[node] == w);
                        }
                        else {
                            logger->emit_proof_comment(format("Pruning edge that would skip subtree ({}, {})", node, next_node));
                            auto ctx = SCCProofContext(state, *logger, reason, succ, proof_data, data.root, options);
                            prove_skipped_subtree(ctx, node, next_node, data.prev_subroot);
                        }
                    }

                    inference.infer(logger, succ[node] != w, NoJustificationNeeded{}, ReasonFunction{});
                }
                data.lowlink[node] = pos_min(data.lowlink[node], data.visit_number[next_node]);
            }
        }

        if (data.lowlink[node] == data.visit_number[node]) {
            if (logger) {
                logger->emit_proof_comment("More than one SCC");
                auto ctx = SCCProofContext{state, *logger, reason, succ, proof_data, node, options};
                prove_reachable_set_too_small(ctx);
            }
            inference.contradiction(logger, JustifyUsingRUP{}, reason);
        }
        else
            return back_edges;
    }

    auto check_sccs(
        const State & state,
        auto & inference,
        ProofLogger * const logger,
        const ReasonFunction & reason,
        const vector<IntegerVariableID> & succ,
        const SCCOptions & options,
        SCCProofData & proof_data)
        -> void
    {
        auto data = SCCPropagatorData(succ.size());

        for (const auto & v : state.each_value_mutable(succ[data.root])) {
            auto next_node = v.raw_value;
            if (data.visit_number[next_node] == -1) {
                auto back_edges = explore(state, inference, logger, reason, next_node, succ, data, proof_data, options);

                if (back_edges.empty()) {
                    if (logger) {
                        logger->emit_proof_comment("No back edges");
                        auto ctx = SCCProofContext(state, *logger, reason, succ, proof_data, next_node, options);
                        prove_reachable_set_too_small(ctx);
                    }
                    inference.contradiction(logger, JustifyUsingRUP{}, reason);
                }
                else if (options.fix_req && back_edges.size() == 1) {
                    auto from_node = back_edges[0].first;
                    auto to_node = back_edges[0].second;
                    if (! state.optional_single_value(succ[from_node])) {
                        if (logger) {
                            logger->emit_proof_comment(format("Fix required back edge ({}, {}):", from_node, to_node));

                            auto ctx = SCCProofContext(state, *logger, reason, succ, proof_data, from_node, options);
                            prove_reachable_set_too_small(ctx, succ[from_node] != Integer{to_node});
                        }
                        inference.infer(logger, succ[from_node] == Integer{to_node}, NoJustificationNeeded{}, ReasonFunction{});
                    }
                }
                data.start_prev_subtree = data.end_prev_subtree + 1;
                data.end_prev_subtree = data.count - 1;
                data.prev_subroot = next_node;
            }
        }

        if (cmp_not_equal(data.count, succ.size())) {
            if (logger) {
                logger->emit_proof_comment("Disconnected graph");
                auto ctx = SCCProofContext(state, *logger, reason, succ, proof_data, data.root, options);
                prove_reachable_set_too_small(ctx);
            }
            inference.contradiction(logger, JustifyUsingRUP{}, reason);
        }

        if (options.prune_root && data.start_prev_subtree > 1) {
            for (const auto & v : state.each_value_mutable(succ[data.root])) {
                if (data.visit_number[v.as_index()] < data.start_prev_subtree) {
                    if (logger) {
                        logger->emit_proof_comment("Prune impossible edges from root node");
                        auto ctx = SCCProofContext(state, *logger, reason, succ, proof_data, data.root, options);
                        prove_reachable_set_too_small(ctx, succ[data.root] == v);
                    }
                    inference.infer(logger, succ[data.root] != v, JustifyUsingRUP{}, reason);
                }
            }
        }
    }

    auto propagate_circuit_using_scc(
        const State & state,
        auto & inference,
        ProofLogger * const logger,
        const ReasonFunction & reason,
        const vector<IntegerVariableID> & succ,
        const SCCOptions & scc_options,
        const ConstraintStateHandle & pos_var_data_handle,
        const ConstraintStateHandle & proof_flag_data_handle,
        const ConstraintStateHandle & pos_alldiff_data_handle,
        const ConstraintStateHandle & unassigned_handle)
        -> void
    {
        auto & pos_var_data = any_cast<PosVarDataMap &>(state.get_persistent_constraint_state(pos_var_data_handle));
        propagate_non_gac_alldifferent(unassigned_handle, state, inference, logger);
        auto proof_data = SCCProofData{pos_var_data, proof_flag_data_handle, pos_alldiff_data_handle};
        check_sccs(state, inference, logger, reason, succ, scc_options, proof_data);
        auto & unassigned = any_cast<list<IntegerVariableID> &>(state.get_constraint_state(unassigned_handle));
        // Remove any newly assigned vals from unassigned
        auto it = unassigned.begin();
        while (it != unassigned.end()) {
            if (state.optional_single_value(*it))
                it = unassigned.erase(it);
            else
                ++it;
        }
        prevent_small_cycles(succ, pos_var_data, unassigned_handle, state, inference, logger);
    }
}

CircuitSCC::CircuitSCC(std::vector<IntegerVariableID> var, bool gacAllDifferent, const SCCOptions s) :
    CircuitBase(std::move(var), gacAllDifferent),
    scc_options(s)
{
}

auto CircuitSCC::clone() const -> unique_ptr<Constraint>
{
    return make_unique<CircuitSCC>(_succ, _gac_all_different, scc_options);
}

auto CircuitSCC::install(Propagators & propagators, State & initial_state, ProofModel * const model) && -> void
{
    auto pos_var_data = CircuitBase::set_up(propagators, initial_state, model);

    // Keep track of unassigned vars
    list<IntegerVariableID> unassigned{};
    for (auto v : _succ) {
        unassigned.emplace_back(v);
    }
    auto pos_var_data_handle = initial_state.add_persistent_constraint_state(pos_var_data);
    auto unassigned_handle = initial_state.add_constraint_state(unassigned);
    auto proof_flag_data_handle = initial_state.add_persistent_constraint_state(map<long, ShiftedPosDataMaps>{});
    auto pos_alldiff_data_handle = initial_state.add_persistent_constraint_state(PosAllDiffData{});

    Triggers triggers;
    triggers.on_change = {_succ.begin(), _succ.end()};
    propagators.install(
        [succ = _succ,
            pos_var_data_handle = pos_var_data_handle,
            proof_flag_data_handle = proof_flag_data_handle,
            pos_alldiff_data_handle = pos_alldiff_data_handle,
            unassigned_handle = unassigned_handle,
            options = scc_options](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            auto reason = generic_reason(state, succ);

            if (logger && options.short_reasons) {
                auto reason_sum = WPBSum{};
                for (const auto & lit : reason()) {
                    reason_sum += 1_i * get<ProofLiteral>(lit);
                }
                // We will manually delete this later.
                auto [_reason_short, _line1, _line2] =
                    logger->create_proof_flag_reifying(reason_sum >= Integer(reason_sum.terms.size()), "sr", ProofLevel::Current);
                ProofFlag reason_short = _reason_short;
                reason = singleton_reason(reason_short);
            }

            propagate_circuit_using_scc(state, inference, logger, reason,
                succ, options, pos_var_data_handle, proof_flag_data_handle, pos_alldiff_data_handle, unassigned_handle);
            return PropagatorState::Enable;
        },
        triggers);
}
