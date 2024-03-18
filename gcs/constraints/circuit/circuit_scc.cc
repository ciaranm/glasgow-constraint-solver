#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/constraints/circuit/circuit_base.hh>
#include <gcs/constraints/circuit/circuit_scc.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/propagators.hh>

#include <list>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using std::cmp_equal;
using std::cmp_less;
using std::cmp_less_equal;
using std::cmp_not_equal;
using std::get;
using std::holds_alternative;
using std::list;
using std::make_optional;
using std::make_pair;
using std::map;
using std::min;
using std::move;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::random_device;
using std::set;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::uniform_int_distribution;
using std::unique_ptr;
using std::variant;
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

    struct PLine
    {
        // Represents a pol line in the proof that we can add terms to.
        // Maybe this could be generalised (e.g. to other operations) and live in proof.cc?
        stringstream p_line;
        bool first_added;
        int count;

        PLine() :
            first_added(true),
            count(0)
        {
            p_line << "p ";
        }

        auto add_and_saturate(ProofLine line_number)
        {
            count++;
            p_line << line_number;
            if (first_added) {
                p_line << " ";
                first_added = false;
            }
            else
                p_line << " + s ";
        }

        auto str() const -> string
        {
            return p_line.str();
        }

        auto clear()
        {
            p_line.str("");
            p_line << "p ";
            first_added = true;
            count = 0;
        }

        auto divide_by(long div)
        {
            if (div > 1 && ! first_added)
                p_line << " " << div << " d "
                       << " ";
        }
    };

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

    auto prove_not_both(ProofLogger & logger, long i, long l, long k,
        ShiftedPosDataMaps & flag_data, const PosVarDataMap & pos_var_data, const bool using_shifted_pos) -> ProofLine
    {
        // Prove that (shift)pos[i] != l \/ (shift)pos[i] != k
        ProofLine neq_line{};

        if (using_shifted_pos) {
            auto & shifted_pos_eq = flag_data.shifted_pos_eq;
            auto & shifted_pos_geq = flag_data.shifted_pos_geq;

            if (shifted_pos_eq[i][l].neq_lines.contains(k)) {
                // Don't reprove this if we did it before
                return shifted_pos_eq[i][l].neq_lines[k];
            }

            // Assumes l < k
            PLine p_line;
            p_line.add_and_saturate(shifted_pos_geq[i][k].forwards_reif_line);
            p_line.add_and_saturate(shifted_pos_geq[i][l + 1].backwards_reif_line);
            logger.emit_proof_line(p_line.str(), ProofLevel::Temporary);

            logger.emit_proof_comment("Not both: " +
                shifted_pos_eq[i][k].comment_name + "=" + to_string(k) + " and " +
                shifted_pos_eq[i][l].comment_name + "=" + to_string(l));

            neq_line = logger.emit_rup_proof_line(
                WeightedPseudoBooleanSum{} + 1_i * ! shifted_pos_eq[i][k].flag + 1_i * ! shifted_pos_eq[i][l].flag >= 1_i,
                ProofLevel::Top);

            shifted_pos_eq[i][l].neq_lines[k] = neq_line;
        }
        else {
            auto & shifted_pos = flag_data.shifted_pos_eq;
            if (shifted_pos[i][l].neq_lines.contains(k)) {
                // Don't reprove this if we did it before
                return shifted_pos[i][l].neq_lines[k];
            }

            logger.emit_proof_comment("Not both:" +
                pos_var_data.at(i).comment_name + "=" + to_string(k) + " and " +
                pos_var_data.at(i).comment_name + "=" + to_string(l));

            neq_line = logger.emit_rup_proof_line(
                WeightedPseudoBooleanSum{} + 1_i * (pos_var_data.at(i).var != Integer{k}) + 1_i * (pos_var_data.at(i).var != Integer{l}) >= 1_i,
                ProofLevel::Top);

            shifted_pos[i][l].neq_lines[k] = neq_line;
        }
        return neq_line;
    }

    auto prove_at_most_1_pos(ProofLogger & logger,
        const long & node, const set<long> & values, ShiftedPosDataMaps & flag_data,
        PosVarDataMap pos_var_data, bool using_shifted_pos) -> ProofLine
    {
        // Prove that at most one (shift)pos[node] == v is true for v in values
        stringstream proofline;

        // We should document properly why this works somewhere now that it's in more than one place
        // Essentially, we can always recover an at most 1 constraint from a clique of "not both" constraints.
        if (values.size() > 1) {
            auto k = ++values.begin();
            auto l = values.begin();
            proofline << "p " << prove_not_both(logger, node, (*l), (*k), flag_data, pos_var_data, using_shifted_pos);
            vector<ProofLine> neq_lines{};
            k++;
            auto k_count = 2;
            while (k != values.end()) {
                proofline << " " << k_count << " * ";
                l = values.begin();
                while (l != k) {
                    proofline << prove_not_both(logger, node, (*l), (*k), flag_data, pos_var_data,
                                     using_shifted_pos)
                              << " + ";
                    l++;
                }
                proofline << k_count + 1 << " d ";
                k++;
                k_count++;
            }

            if (using_shifted_pos)
                logger.emit_proof_comment("AM1 " + flag_data.shifted_pos_eq[node][*values.begin()].comment_name);
            else
                logger.emit_proof_comment("AM1 p[" + to_string(node) + "]");

            return logger.emit_proof_line(proofline.str(), ProofLevel::Top);
        }
        else if (values.size() == 1) {
            auto idx = *values.begin();
            if (using_shifted_pos) {
                logger.emit_proof_comment("AM1 " +
                    flag_data.shifted_pos_eq[node][*values.begin()].comment_name);
                return logger.emit_rup_proof_line(
                    WeightedPseudoBooleanSum{} + 1_i * ! (flag_data.shifted_pos_eq[node][idx].flag) >= 0_i,
                    ProofLevel::Top);
            }
            else {
                logger.emit_proof_comment("AM1 p[" + to_string(node) + "]");
                return logger.emit_rup_proof_line(
                    WeightedPseudoBooleanSum{} + 1_i * ! (pos_var_data.at(node).var == Integer{idx}) >= 0_i,
                    ProofLevel::Top);
            }
        }
        else
            throw UnexpectedException{"trying to prove an AM1 over zero values?"};
    }

    auto prove_pos_alldiff_lines(ProofLogger & logger,
        const vector<IntegerVariableID> & succ, const PosVarDataMap & pos_var_data,
        PosAllDiffData & pos_alldiff_data) -> void
    {
        // Recover an all different constraint (al1/am1) over the pos variables
        // This is O(n^3) where n is the number of variables in the circuit but only needs to be done once.
        auto n = static_cast<long>(succ.size());

        // First prove the at least 1 lines
        logger.emit_proof_comment("Pos all diff lines:");
        WeightedPseudoBooleanSum pb_sum;
        for (long i = 0; i < n; i++) {
            pb_sum += 1_i * (pos_var_data.at(i).var == 0_i);
        }
        logger.emit_proof_comment("AL1 p[i] = 0");
        pos_alldiff_data.at_least_1_lines[0] =
            logger.emit_rup_proof_line(pb_sum >= 1_i, ProofLevel::Top);
        auto last_al1_line = pos_alldiff_data.at_least_1_lines[0];
        for (long j = 1; j < n; j++) {
            pb_sum = WeightedPseudoBooleanSum{};
            PLine p_line;
            for (long i = 0; i < n; i++) {
                auto next_pos_vars = WeightedPseudoBooleanSum{};
                for (long k = 0; k < n; k++) {
                    next_pos_vars += 1_i * (pos_var_data.at(k).var == Integer{j});
                    logger.emit_rup_proof_line(
                        WeightedPseudoBooleanSum{} + 1_i * ! (pos_var_data.at(i).var == Integer{j - 1}) +
                                1_i * ! (succ[i] == Integer{k}) + 1_i * (pos_var_data.at(k).var == Integer{j}) >=
                            1_i,
                        ProofLevel::Top);
                }

                p_line.add_and_saturate(
                    logger.emit_rup_proof_line(
                        next_pos_vars + 1_i * ! (pos_var_data.at(i).var == Integer{j - 1}) >= 1_i, ProofLevel::Top));
            }
            logger.emit_proof_comment("AL1 p[i] = " + to_string(j));
            p_line.add_and_saturate(last_al1_line);
            pos_alldiff_data.at_least_1_lines[j] = logger.emit_proof_line(p_line.str(), ProofLevel::Top);
            last_al1_line = pos_alldiff_data.at_least_1_lines[j];
        }

        // Now prove the at most 1 lines
        for (long i = 0; i < n; i++) {
            set<long> values{};
            for (int j = 0; j < n; j++) {
                values.insert(j);
            }
            ShiftedPosDataMaps dummy{};
            pos_alldiff_data.at_most_1_lines.emplace(i, prove_at_most_1_pos(logger, i, values, dummy, pos_var_data, false));
        }
    }

    auto create_flag_for_greater_than(ProofLogger & logger, const long & root, const long & i, ShiftedPosDataMaps & flag_data_for_root,
        const PosVarDataMap & pos_var_data, PosAllDiffData & pos_alldiff_data,
        const vector<IntegerVariableID> & succ) -> ProofFlagData
    {
        // Create a flag which is reified as follows:
        // d[r, i] => p[r] - p[i] >= 1
        // ~d[r, i] => p[i] - p[r] >= 1
        // This requires us to essentially prove p[r] != p[i] in a redundance subproof

        auto & root_gt_data = flag_data_for_root.greater_than;
        ProofFlag greater_than_flag{};

        if (root_gt_data.count(i)) {
            // If it was already defined, don't redefine it
            return root_gt_data.at(i);
        }
        else {
            auto flag_name = "d[" + to_string(root) + "," + to_string(i) + "]";
            greater_than_flag = logger.create_proof_flag(flag_name);

            auto forwards_reif_line = logger.emit_red_proof_lines_forward_reifying(
                WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(root).var + -1_i * pos_var_data.at(i).var >= 1_i,
                greater_than_flag, ProofLevel::Top);

            if (pos_alldiff_data.at_least_1_lines.empty()) {
                prove_pos_alldiff_lines(logger, succ, pos_var_data, pos_alldiff_data);
            }

            long backwards_reif_line;
            if (i != root) {
                // Redundance subproof:
                auto subproofs = make_optional(map<string, JustifyExplicitly>{});
                auto justf = [&]() {
                    logger.emit_proof_line("     p -2 " + logger.variable_constraints_tracker().proof_name(greater_than_flag) + " w", ProofLevel::Top);
                    for (long k = 0; cmp_less(k, succ.size()); k++) {
                        PLine p_line;
                        // Prove p[i] = k is not possible
                        // First add all AL1 lines except for k
                        for (const auto & [val, al1_line] : pos_alldiff_data.at_least_1_lines) {
                            if (val == k) continue;
                            p_line.add_and_saturate(al1_line);
                        }

                        // Now add all AM1 lines except for i and j
                        for (const auto & my_pair : pos_alldiff_data.at_most_1_lines) {
                            if (my_pair.first == i || my_pair.first == root) {
                                continue;
                            }
                            p_line.add_and_saturate(my_pair.second);
                        }
                        logger.emit_proof_line(p_line.str(), ProofLevel::Top);
                        logger.emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * ! (pos_var_data.at(i).var == Integer{k}) >= 1_i, ProofLevel::Top);
                    }
                    logger.emit_rup_proof_line(WeightedPseudoBooleanSum{} >= 1_i, ProofLevel::Top);
                };
                subproofs.value().emplace(to_string(forwards_reif_line), JustifyExplicitly{justf, {}});

                backwards_reif_line = logger.emit_red_proof_lines_reverse_reifying(
                    WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(root).var + -1_i * pos_var_data.at(i).var >= 0_i,
                    greater_than_flag, ProofLevel::Top, subproofs);
            }
            else {
                // If i == root, d[r, i] is just "false"
                backwards_reif_line = logger.emit_red_proof_lines_reverse_reifying(
                    WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(root).var + -1_i * pos_var_data.at(i).var >= 1_i,
                    greater_than_flag, ProofLevel::Top);
            }

            root_gt_data[i] = ProofFlagData{
                flag_name, greater_than_flag, forwards_reif_line, backwards_reif_line, {}};
            return root_gt_data[i];
        }
    }

    auto create_shifted_pos(ProofLogger & logger,
        const long & root, const long & i, const long & j, ShiftedPosDataMaps & flag_data_for_root,
        const PosVarDataMap & pos_var_data, PosAllDiffData & pos_alldiff_data,
        const vector<IntegerVariableID> & succ)
    {
        // Define a "shifted" pos flag q[r, i], that represents the value of p[i] shifted relative to p[root] mod n
        // i.e. q[r, i] == j <=> p[i] - p[r] + n * d[r, i] (the last term corrects for when we go negative)
        auto n = static_cast<long>(succ.size());
        ProofFlagData greater_than_flag_data{};

        greater_than_flag_data = create_flag_for_greater_than(logger, root, i, flag_data_for_root, pos_var_data, pos_alldiff_data, succ);
        auto greater_than_flag = greater_than_flag_data.flag;

        auto maybe_create_and_emplace_flag_data =
            [&](ProofFlagDataMap & flag_data, const long i, const long j, const WeightedPseudoBooleanLessEqual & definition, const string & name, const string & name_suffix) {
                if (! flag_data[i].count(j)) {
                    auto [flag, forwards_reif_line, backwards_reif_line] = logger.create_proof_flag_reifying(definition, name + name_suffix, ProofLevel::Top);
                    flag_data[i][j] = ProofFlagData{name, flag, forwards_reif_line, backwards_reif_line, {}};
                }
            };

        // q[r,i]gej <=> pos[i] - pos[r] + nd[r,i] >= j
        maybe_create_and_emplace_flag_data(flag_data_for_root.shifted_pos_geq, i, j,
            WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(i).var + -1_i * pos_var_data.at(root).var + Integer{n} * greater_than_flag >= Integer{j},
            "q[" + to_string(root) + "," + to_string(i) + "]", "ge" + to_string(j));

        // q[r,i]gej+1 <=> pos[i] - pos[r] + nd[r,i] >= j+1
        maybe_create_and_emplace_flag_data(flag_data_for_root.shifted_pos_geq, i, j + 1,
            WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(i).var + -1_i * pos_var_data.at(root).var + Integer{n} * greater_than_flag >= Integer{j + 1},
            "q[" + to_string(root) + "," + to_string(i) + "]", "ge" + to_string(j + 1));

        // q[r,i]eqj <=> q[r,i]gej /\ ~q[r,i]gej+1
        maybe_create_and_emplace_flag_data(flag_data_for_root.shifted_pos_eq, i, j,
            WeightedPseudoBooleanSum{} + 1_i * flag_data_for_root.shifted_pos_geq[i][j].flag + 1_i * ! flag_data_for_root.shifted_pos_geq[i][j + 1].flag >= 2_i,
            "q[" + to_string(root) + "," + to_string(i) + "]", "eq" + to_string(j));
    }

    auto prove_root_is_0(ProofLogger & logger,
        const long & root, ShiftedPosDataMaps & flag_data_for_root, const PosVarDataMap & pos_var_data,
        PosAllDiffData & pos_alldiff_data, const vector<IntegerVariableID> & succ) -> ProofLine
    {
        // Prove that (shift)pos[root]== 0
        logger.emit_proof_comment("AL1 pos = " + to_string(0));

        auto line = ProofLine{};
        if (root != 0) {
            create_shifted_pos(logger, root, root, 0, flag_data_for_root, pos_var_data, pos_alldiff_data, succ);
            line = logger.emit_rup_proof_line(
                WeightedPseudoBooleanSum{} + 1_i * flag_data_for_root.shifted_pos_eq[root][0].flag >= 1_i,
                ProofLevel::Current);
        }
        else {
            line = logger.emit_rup_proof_line(
                WeightedPseudoBooleanSum{} + 1_i * (pos_var_data.at(root).var == 0_i) >= 1_i,
                ProofLevel::Current);
        }

        return line;
    }

    auto prove_mid_is_at_least(State & state, ProofLogger & logger, const Reason & reason,
        const long & root, const OrderingAssumption & ordering, const long & val, const Literal & assumption,
        ShiftedPosDataMaps & flag_data_for_root,
        const PosVarDataMap & pos_var_data, PosAllDiffData & pos_alldiff_data,
        const vector<IntegerVariableID> & succ)
    {
        // The ordering assumption assumes we will see "middle" before "last" when we start at "first"
        // If we haven't seen middle yet under our assumptions we can prove (shift)pos[middle] >= val
        auto & mid = ordering.middle;
        logger.emit_proof_comment("Haven't seen mid node yet:");
        if (root != 0) {
            create_shifted_pos(logger, root, mid, val, flag_data_for_root, pos_var_data, pos_alldiff_data, succ);

            if (val == 1) {
                PLine p_line;
                p_line.add_and_saturate(flag_data_for_root.shifted_pos_geq[mid][1].backwards_reif_line);
                p_line.add_and_saturate(flag_data_for_root.greater_than[mid].backwards_reif_line);
                logger.emit_proof_line(p_line.str(), ProofLevel::Temporary);
            }

            logger.emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} + 1_i * ! ordering.assumption_flag + 1_i * ! assumption + 1_i * flag_data_for_root.shifted_pos_geq[mid][val].flag >= 1_i,
                ProofLevel::Current);
        }
        else {
            logger.emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} + 1_i * (pos_var_data.at(mid).var >= Integer{val}) >= 1_i,
                ProofLevel::Current);
        }
    }

    auto prove_pos_and_node_implies_next_node(State & state, ProofLogger & logger, const Reason & reason,
        const long & root, const long & node, const long & next_node, const long & count,
        ShiftedPosDataMaps & flag_data_for_root, const PosVarDataMap & pos_var_data, PosAllDiffData & pos_alldiff_data,
        const vector<IntegerVariableID> & succ)
    {
        // successor_implies_line := Prove (shift)pos[node][count - 1] /\ succ[node] = next_node => (shift)pos[next_node][count]
        auto successor_implies_line = ProofLine{};
        auto n = static_cast<long>(succ.size());

        if (root != 0) {
            create_shifted_pos(logger, root, next_node, count, flag_data_for_root, pos_var_data, pos_alldiff_data, succ);
            auto & root_greater_than = flag_data_for_root.greater_than;
            auto & shifted_pos_geq = flag_data_for_root.shifted_pos_geq;
            auto & shifted_pos_eq = flag_data_for_root.shifted_pos_eq;

            // Some painful adding up to get us to rup what we want
            // Need to document that this always works
            if (next_node != root) {
                stringstream p_line;
                p_line << "p ";
                // aaaa so many edge cases
                if (next_node != 0) {
                    p_line << pos_var_data.at(node).plus_one_lines.at(next_node).leq_line << " "
                           << root_greater_than.at(node).forwards_reif_line << " + "
                           << root_greater_than.at(next_node).backwards_reif_line << " + "
                           << to_string(2 * n) << " d ";
                }
                else {
                    p_line << logger.emit_rup_proof_line(
                                  WeightedPseudoBooleanSum{} + 1_i * ! (succ[node] == Integer{next_node}) + 1_i * ! root_greater_than.at(node).flag >= 1_i,
                                  ProofLevel::Temporary)
                           << " ";
                    p_line << logger.emit_rup_proof_line(
                                  WeightedPseudoBooleanSum{} + 1_i * ! (succ[node] == Integer{next_node}) + 1_i * root_greater_than.at(next_node).flag >= 1_i,
                                  ProofLevel::Temporary)
                           << " + ";
                }

                p_line
                    << to_string(n) << " * "
                    << pos_var_data.at(node).plus_one_lines.at(next_node).geq_line << " + "
                    << shifted_pos_geq.at(node).at(count - 1).forwards_reif_line << " + "
                    << shifted_pos_geq.at(next_node).at(count).backwards_reif_line << " +";
                logger.emit_proof_line(p_line.str(), ProofLevel::Temporary);

                p_line.str("");
                p_line << "p ";

                p_line << pos_var_data.at(node).plus_one_lines.at(next_node).geq_line << " "
                       << root_greater_than.at(node).backwards_reif_line << " + "
                       << root_greater_than.at(next_node).forwards_reif_line << " + "
                       << to_string(2 * n) << " d ";

                p_line
                    << to_string(n) << " * "
                    << pos_var_data.at(node).plus_one_lines.at(next_node).leq_line << " + "
                    << shifted_pos_geq.at(node).at(count).backwards_reif_line << " + "
                    << shifted_pos_geq.at(next_node).at(count + 1).forwards_reif_line << " +";
                logger.emit_proof_line(p_line.str(), ProofLevel::Temporary);

                logger.emit_proof_comment("Next implies: succ[" + to_string(node) + "] = " + to_string(next_node) + " and " +
                    shifted_pos_eq[node][count - 1].comment_name + " = " + to_string(count - 1) + " => " +
                    shifted_pos_eq[next_node][count].comment_name + " = " + to_string(count));

                // RUP shifted_pos[node][count-1] /\ succ[node] = next_node => shifted_pos[next_node][i]
                successor_implies_line = logger.emit_rup_proof_line_under_reason(state, reason,
                    WeightedPseudoBooleanSum{} + 1_i * shifted_pos_eq[next_node][count].flag + 1_i * (succ[node] != Integer{next_node}) +
                            1_i * (! shifted_pos_eq[node][count - 1].flag) >=
                        1_i,
                    ProofLevel::Current);
            }
            else {
                stringstream p_line;
                p_line << "p ";
                p_line << shifted_pos_geq[node][count - 1].forwards_reif_line << " ";
                p_line << pos_var_data.at(node).plus_one_lines.at(next_node).geq_line << " + s";
                logger.emit_proof_line(p_line.str(), ProofLevel::Temporary);
                p_line.str("");
                p_line << "p ";
                p_line << shifted_pos_geq[node][count].backwards_reif_line << " ";
                p_line << pos_var_data.at(node).plus_one_lines.at(next_node).leq_line << " + s";
                logger.emit_proof_line(p_line.str(), ProofLevel::Temporary);

                logger.emit_proof_comment("Next implies: succ[" + to_string(node) + "] = " + to_string(next_node) + " and " +
                    shifted_pos_eq[node][count - 1].comment_name + " = " + to_string(count - 1) + " => 0 >= 1");

                successor_implies_line = logger.emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * (! shifted_pos_eq[node][count - 1].flag) + 1_i * (succ[node] != Integer{next_node}) >= 1_i, ProofLevel::Current);
            }
        }
        else {
            // Not using shifted pos, just use the actual pos values
            // succ[node] == next_node /\ pos[node] == count - 1 => pos[next_node] == count
            successor_implies_line = logger.emit_rup_proof_line(
                WeightedPseudoBooleanSum{} + 1_i * (pos_var_data.at(node).var != Integer{count - 1}) +
                        1_i * (succ[node] != Integer{next_node}) + 1_i * (pos_var_data.at(next_node).var == Integer{count}) >=
                    1_i,
                ProofLevel::Current);
        }

        return successor_implies_line;
    }

    auto prove_not_same_val(State & state, ProofLogger & logger, const Reason & reason,
        const long & root, const long & middle, const long & next_node, const long & count,
        map<long, ShiftedPosDataMaps> & flag_data, const PosVarDataMap & pos_var_data, PosAllDiffData & pos_alldiff_data,
        const vector<IntegerVariableID> & succ)
    {
        auto succesor_implies_not_mid_line = ProofLine{};
        // successor_implies_line :=
        // Prove (shift)pos[next_node][count] => ! (shift)pos[mid][count]
        create_shifted_pos(logger, root, middle, count, flag_data[root], pos_var_data, pos_alldiff_data, succ);
        logger.emit_proof_comment("Successor implies not mid");
        auto n = static_cast<long>(succ.size());
        if (root != 0) {
            create_flag_for_greater_than(logger, next_node, middle, flag_data[next_node], pos_var_data, pos_alldiff_data, succ);

            PLine temp_p_line;

            auto & shifted_pos_geq = flag_data[root].shifted_pos_geq;
            auto & shifted_pos_eq = flag_data[root].shifted_pos_eq;

            logger.emit_proof_comment("Step 1");

            temp_p_line.add_and_saturate(shifted_pos_geq[next_node][count + 1].backwards_reif_line);
            temp_p_line.add_and_saturate(shifted_pos_geq[middle][count].forwards_reif_line);
            auto geq_and_leq = logger.emit_proof_line(temp_p_line.str(), ProofLevel::Temporary);

            temp_p_line.clear();
            temp_p_line.add_and_saturate(shifted_pos_geq[next_node][count].forwards_reif_line);
            temp_p_line.add_and_saturate(shifted_pos_geq[middle][count + 1].backwards_reif_line);
            logger.emit_proof_comment("Step 2");
            auto leq_and_geq = logger.emit_proof_line(temp_p_line.str(), ProofLevel::Temporary);

            temp_p_line.clear();
            temp_p_line.add_and_saturate(geq_and_leq);
            temp_p_line.add_and_saturate(flag_data[next_node].greater_than[middle].forwards_reif_line);
            logger.emit_proof_comment("Step 3");
            logger.emit_proof_line(temp_p_line.str(), ProofLevel::Temporary);
            temp_p_line.clear();

            temp_p_line.add_and_saturate(leq_and_geq);
            temp_p_line.add_and_saturate(logger.emit_rup_proof_line(
                WeightedPseudoBooleanSum{} + -1_i * pos_var_data.at(next_node).var + 1_i * pos_var_data.at(middle).var >= Integer{-n + 1}, ProofLevel::Temporary));
            logger.emit_proof_comment("Step 4");
            logger.emit_proof_line(temp_p_line.str(), ProofLevel::Temporary);
            temp_p_line.clear();

            logger.emit_proof_comment("Step 5");
            logger.emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} +
                        1_i * ! flag_data[root].greater_than[middle].flag +
                        1_i * ! flag_data[next_node].greater_than[middle].flag +
                        1_i * ! shifted_pos_eq[middle][count].flag +
                        1_i * (! shifted_pos_eq[next_node][count].flag) >=
                    1_i,
                ProofLevel::Temporary);

            logger.emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} +
                        1_i * ! flag_data[next_node].greater_than[middle].flag +
                        1_i * ! shifted_pos_eq[middle][count].flag +
                        1_i * (! shifted_pos_eq[next_node][count].flag) >=
                    1_i,
                ProofLevel::Temporary);

            temp_p_line.add_and_saturate(leq_and_geq);
            temp_p_line.add_and_saturate(flag_data[next_node].greater_than[middle].backwards_reif_line);
            logger.emit_proof_comment("Step 6");
            logger.emit_proof_line(temp_p_line.str(), ProofLevel::Temporary);
            temp_p_line.clear();

            temp_p_line.add_and_saturate(geq_and_leq);
            temp_p_line.add_and_saturate(logger.emit_rup_proof_line(
                WeightedPseudoBooleanSum{} + -1_i * pos_var_data.at(middle).var + 1_i * pos_var_data.at(next_node).var >= Integer{-n + 1}, ProofLevel::Temporary));
            logger.emit_proof_comment("Step 7");
            logger.emit_proof_line(temp_p_line.str(), ProofLevel::Temporary);
            temp_p_line.clear();

            logger.emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} +
                        1_i * ! flag_data[root].greater_than[next_node].flag +
                        1_i * flag_data[next_node].greater_than[middle].flag +
                        1_i * ! shifted_pos_eq[middle][count].flag +
                        1_i * (! shifted_pos_eq[next_node][count].flag) >=
                    1_i,
                ProofLevel::Temporary);

            logger.emit_proof_comment("Step 8");
            logger.emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} + 1_i * ! flag_data[next_node].greater_than[middle].flag +
                        1_i * ! shifted_pos_eq[middle][count].flag +
                        1_i * (! shifted_pos_eq[next_node][count].flag) >=
                    1_i,
                ProofLevel::Temporary);

            succesor_implies_not_mid_line = logger.emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} + 1_i * ! shifted_pos_eq[middle][count].flag +
                        1_i * (! shifted_pos_eq[next_node][count].flag) >=
                    1_i,
                ProofLevel::Current);
        }
        else {
            succesor_implies_not_mid_line = logger.emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} +
                        1_i * ! (pos_var_data.at(middle).var == Integer{count}) +
                        1_i * ! (pos_var_data.at(next_node).var == Integer{count}) >=
                    1_i,
                ProofLevel::Temporary);
        }

        return succesor_implies_not_mid_line;
    }

    auto prove_exclude_last_based_on_ordering(State & state, ProofLogger & logger, const Reason & reason,
        const OrderingAssumption & ordering, const long & root, const long & count, const Literal & assumption,
        map<long, ShiftedPosDataMaps> & flag_data, const PosVarDataMap & pos_var_data, PosAllDiffData & pos_alldiff_data,
        const vector<IntegerVariableID> & succ) -> ProofLine
    {
        // Based on an ordering assumption and the fact we haven't seen
        auto mid = ordering.middle;
        auto last = ordering.last;
        auto exclusion_line = ProofLine{};

        logger.emit_proof_comment("Exclude based on ordering");

        if (root != 0) {
            auto & shifted_pos_geq = flag_data[root].shifted_pos_geq;
            auto & shifted_pos_eq = flag_data[root].shifted_pos_eq;

            create_shifted_pos(logger, root, mid, count, flag_data[root], pos_var_data, pos_alldiff_data, succ);
            create_shifted_pos(logger, root, last, count, flag_data[root], pos_var_data, pos_alldiff_data, succ);
            PLine p_line;

            p_line.add_and_saturate(shifted_pos_geq[mid][count].forwards_reif_line);
            p_line.add_and_saturate(shifted_pos_geq[last][count].backwards_reif_line);
            p_line.add_and_saturate(flag_data[mid].greater_than[last].backwards_reif_line);

            p_line.add_and_saturate(logger.emit_rup_proof_line(
                WeightedPseudoBooleanSum{} + 1_i * flag_data[root].greater_than[last].flag + 1_i * flag_data[last].greater_than[root].flag >= 1_i,
                ProofLevel::Temporary));

            logger.emit_proof_line(p_line.str(), ProofLevel::Temporary);
            exclusion_line = logger.emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} + 1_i * ! assumption + 1_i * ! ordering.assumption_flag + 1_i * ! shifted_pos_eq[last][count].flag >= 1_i,
                ProofLevel::Current);
        }
        else {
            exclusion_line = logger.emit_rup_proof_line_under_reason(state, reason,
                WeightedPseudoBooleanSum{} + 1_i * ! assumption + 1_i * ! ordering.assumption_flag + 1_i * ! (pos_var_data.at(last).var == Integer{count}) >= 1_i,
                ProofLevel::Current);
        }

        return exclusion_line;
    }

    auto prove_reachable_set_too_small(State & state, ProofLogger & logger, const Reason & reason,
        const vector<IntegerVariableID> & succ, const long & root, SCCProofData & proof_data,
        const Literal & assumption = TrueLiteral{}, const optional<OrderingAssumption> & ordering = nullopt)
    {
        logger.emit_proof_comment("REACHABLE SET from " + to_string(root));

        map<long, set<long>> all_values_seen{};
        const auto using_shifted_pos = root != 0;
        const auto & pos_var_data = proof_data.pos_var_data;

        auto & flag_data = any_cast<map<long, ShiftedPosDataMaps> &>(
            state.get_persistent_constraint_state(proof_data.proof_flag_data_handle));
        auto & pos_alldiff_data = any_cast<PosAllDiffData &>(
            state.get_persistent_constraint_state(proof_data.pos_alldiff_data_handle));

        ShiftedPosDataMaps & flag_data_for_root = flag_data[root];

        all_values_seen[root].insert(0);
        PLine contradiction_line;

        auto last_al1_line = prove_root_is_0(logger, root, flag_data_for_root, pos_var_data, pos_alldiff_data, succ);
        contradiction_line.add_and_saturate(last_al1_line);

        if (ordering) {
            if (ordering.value().first != root) {
                throw UnexpectedException{"SCC Proof Error: First component of ordering assumption must be root of reachability argument."};
            }
            // Mid is not the root, so it must be at least 1
            prove_mid_is_at_least(state, logger, reason, root, ordering.value(), 1, assumption, flag_data_for_root, pos_var_data,
                pos_alldiff_data, succ);
        }

        long count = 1;
        set<long> all_reached_nodes = {root};
        set<long> last_reached_nodes = {root};

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
            PLine add_for_at_least_1;
            add_for_at_least_1.add_and_saturate(last_al1_line);
            PLine add_for_not_mid;

            set<long> new_reached_nodes{};
            bool exclude_based_on_ordering = false;
            for (const auto & node : last_reached_nodes) {
                WeightedPseudoBooleanSum possible_next_nodes_sum{};
                PLine add_for_node_implies_at_least_1;
                PLine add_for_node_implies_not_mid;
                state.for_each_value(succ[node], [&](Integer val) {
                    if (skip_based_on_assumption(succ[node], val, assumption)) return;
                    possible_next_nodes_sum += 1_i * (succ[node] == val);
                    auto next_node = val.raw_value;

                    all_values_seen[next_node].insert(count);

                    add_for_node_implies_at_least_1.add_and_saturate(
                        prove_pos_and_node_implies_next_node(state, logger, reason, root, node, next_node, count,
                            flag_data_for_root, pos_var_data, pos_alldiff_data, succ));

                    if (ordering && next_node == ordering.value().last && ! seen_middle) {
                        // Ordering says that since we haven't seen "middle" yet, we can't visit "last"
                        exclude_based_on_ordering = true;
                    }
                    else if (ordering && ! seen_middle && next_node != ordering.value().middle) {
                        // If we see any other node, prove that we can't have middle == count for this
                        // node and pos combination
                        add_for_node_implies_not_mid.add_and_saturate(prove_not_same_val(state, logger, reason,
                            root, ordering.value().middle, next_node, count,
                            flag_data, pos_var_data, pos_alldiff_data, succ));
                        if (next_node != root)
                            new_reached_nodes.insert(next_node);
                    }
                    else if (ordering && next_node == ordering.value().middle) {
                        // Now we've seen "middle"
                        seen_middle = true;
                        new_reached_nodes.insert(next_node);
                    }
                    else if (next_node != root) {
                        new_reached_nodes.insert(next_node);
                    }
                });

                add_for_node_implies_at_least_1.add_and_saturate(
                    logger.emit_rup_proof_line_under_reason(state, reason,
                        possible_next_nodes_sum + 1_i * ! assumption >= 1_i, ProofLevel::Temporary));

                add_for_at_least_1.add_and_saturate(
                    logger.emit_proof_line(add_for_node_implies_at_least_1.str(), ProofLevel::Current));

                if (ordering && ! seen_middle) {
                    if (add_for_node_implies_not_mid.count >= 1) {
                        add_for_not_mid.add_and_saturate(
                            logger.emit_proof_line(add_for_node_implies_not_mid.str(), ProofLevel::Current));
                    }
                }
            }

            logger.emit_proof_comment("AL1 pos = " + to_string(count));
            add_for_at_least_1.divide_by(add_for_at_least_1.count);
            last_al1_line = logger.emit_proof_line(add_for_at_least_1.str(), ProofLevel::Current);
            if (exclude_based_on_ordering) {
                PLine new_last_al1_line;
                new_last_al1_line.add_and_saturate(
                    prove_exclude_last_based_on_ordering(state, logger, reason, ordering.value(), root, count, assumption, flag_data,
                        pos_var_data, pos_alldiff_data, succ));
                new_last_al1_line.add_and_saturate(last_al1_line);
                last_al1_line = logger.emit_proof_line(new_last_al1_line.str(), ProofLevel::Current);
            }
            contradiction_line.add_and_saturate(last_al1_line);

            if (ordering && ! seen_middle) {
                add_for_not_mid.add_and_saturate(last_al1_line);
                logger.emit_proof_comment("Not mid");
                logger.emit_proof_line(add_for_not_mid.str(), ProofLevel::Current);
                prove_mid_is_at_least(state, logger, reason, root, ordering.value(), count + 1, assumption, flag_data_for_root,
                    pos_var_data, pos_alldiff_data, succ);
            }

            last_reached_nodes = new_reached_nodes;

            // Continue until we've logged more layers than we have reached nodes (Hall violator)
            all_reached_nodes.insert(new_reached_nodes.begin(), new_reached_nodes.end());
            count++;
        }

        // At most one lines
        for (const auto & node : all_reached_nodes) {
            contradiction_line.add_and_saturate(
                prove_at_most_1_pos(logger, node, all_values_seen[node], flag_data_for_root, pos_var_data, using_shifted_pos));
        }

        logger.emit_proof_comment("Hall violator gives contradiction: ");
        logger.emit_proof_line(contradiction_line.str(), ProofLevel::Current);
    }

    auto prove_skipped_subtree(State & state, ProofLogger & logger, const Reason & reason,
        const vector<IntegerVariableID> & succ, const long & node, const long & next_node, const long & root, const long & skipped_subroot,
        SCCProofData & proof_data)
    {
        auto & flag_data = any_cast<map<long, ShiftedPosDataMaps> &>(state.get_persistent_constraint_state(proof_data.proof_flag_data_handle));
        auto & pos_all_diff_data = any_cast<PosAllDiffData &>(state.get_persistent_constraint_state(proof_data.pos_alldiff_data_handle));
        auto & pos_var_data = proof_data.pos_var_data;

        auto root_gt_next = create_flag_for_greater_than(
            logger, root, next_node, flag_data[root], pos_var_data, pos_all_diff_data, succ);
        auto subroot_gt_root = create_flag_for_greater_than(
            logger, skipped_subroot, root, flag_data[skipped_subroot], pos_var_data, pos_all_diff_data, succ);
        auto next_gt_subroot = create_flag_for_greater_than(
            logger, next_node, skipped_subroot, flag_data[next_node], pos_var_data, pos_all_diff_data, succ);

        auto node_then_subroot_then_root = logger.create_proof_flag_reifying(
            WeightedPseudoBooleanSum{} + 1_i * ! root_gt_next.flag + 1_i * ! subroot_gt_root.flag + 1_i * ! next_gt_subroot.flag >= 2_i,
            "ord1", ProofLevel::Current);

        OrderingAssumption ordering1{
            get<0>(node_then_subroot_then_root),
            next_node,
            skipped_subroot,
            root};

        prove_reachable_set_too_small(state, logger, reason, succ, next_node, proof_data, succ[node] == Integer{next_node}, ordering1);

        auto subroot_gt_node = create_flag_for_greater_than(
            logger, skipped_subroot, node, flag_data[skipped_subroot], pos_var_data, pos_all_diff_data, succ);
        auto node_gt_root = create_flag_for_greater_than(
            logger, node, root, flag_data[node], pos_var_data, pos_all_diff_data, succ);

        auto subroot_then_node_then_root = logger.create_proof_flag_reifying(
            WeightedPseudoBooleanSum{} + 1_i * ! subroot_gt_node.flag + 1_i * ! node_gt_root.flag + 1_i * subroot_gt_root.flag >= 2_i, "ord2", ProofLevel::Current);

        OrderingAssumption ordering2{
            get<0>(subroot_then_node_then_root),
            skipped_subroot,
            node,
            root};

        prove_reachable_set_too_small(state, logger, reason, succ, skipped_subroot, proof_data, succ[node] == Integer{next_node}, ordering2);

        stringstream final_contradiction_p_line;
        final_contradiction_p_line << "p ";
        stringstream temp_p_line;
        temp_p_line << "p ";
        temp_p_line << pos_var_data.at(node).plus_one_lines.at(next_node).geq_line << " ";
        temp_p_line << root_gt_next.forwards_reif_line << " + ";
        logger.emit_proof_line(temp_p_line.str(), ProofLevel::Temporary);
        final_contradiction_p_line << logger.emit_rup_proof_line(
                                          WeightedPseudoBooleanSum{} + 1_i * (succ[node] != Integer{next_node}) +
                                                  1_i * ! root_gt_next.flag + 1_i * ! node_gt_root.flag >=
                                              1_i,
                                          ProofLevel::Current)
                                   << " ";
        temp_p_line.str("");
        temp_p_line << "p ";
        temp_p_line << pos_var_data.at(node).plus_one_lines.at(next_node).leq_line << " ";
        temp_p_line << next_gt_subroot.forwards_reif_line << " + ";
        temp_p_line << subroot_gt_node.forwards_reif_line << " + ";
        logger.emit_proof_line(temp_p_line.str(), ProofLevel::Temporary);
        final_contradiction_p_line << logger.emit_rup_proof_line(
                                          WeightedPseudoBooleanSum{} + 1_i * (succ[node] != Integer{next_node}) +
                                                  1_i * ! next_gt_subroot.flag + 1_i * ! subroot_gt_node.flag >=
                                              1_i,
                                          ProofLevel::Current)
                                   << " + ";
        final_contradiction_p_line << get<2>(node_then_subroot_then_root) << " + ";
        final_contradiction_p_line << get<2>(subroot_then_node_then_root) << " + s ";
        logger.emit_proof_line(final_contradiction_p_line.str(), ProofLevel::Current);

        logger.emit_rup_proof_line_under_reason(state, reason,
            WeightedPseudoBooleanSum{} + 1_i * (succ[node] != Integer{next_node}) >= 1_i, ProofLevel::Current);
    }

    auto explore(State & state, ProofLogger * const logger, const Reason & reason,
        const long & node, const vector<IntegerVariableID> & succ, SCCPropagatorData & data, SCCProofData & proof_data,
        const SCCOptions & options)
        -> pair<Inference, vector<pair<long, long>>>
    {
        data.visit_number[node] = data.count;
        data.lowlink[node] = data.count;
        data.count++;

        Inference result = gcs::innards::Inference::NoChange;
        vector<pair<long, long>> back_edges{};

        state.for_each_value_while(succ[node], [&](Integer w) -> bool {
            auto next_node = w.raw_value;

            if (data.visit_number[next_node] == -1) {
                auto explore_result = explore(state, logger, reason, next_node, succ, data, proof_data, options);
                increase_inference_to(result, explore_result.first);
                if (result == Inference::Contradiction) {
                    return false;
                }
                auto w_back_edges = explore_result.second;
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
                            logger->emit_proof_comment("Pruning edge to the root from a subtree other than the first (" +
                                to_string(node) + ", " + to_string(next_node) + ")");
                            prove_reachable_set_too_small(state, *logger, reason, succ, data.prev_subroot, proof_data, succ[node] == w);
                        }
                        else {
                            logger->emit_proof_comment("Pruning edge that would skip subtree (" +
                                to_string(node) + ", " + to_string(next_node) + ")");
                            prove_skipped_subtree(state, *logger, reason, succ, node, next_node, data.root, data.prev_subroot, proof_data);
                        }
                    }

                    increase_inference_to(result, state.infer(logger, succ[node] != w, NoJustificationNeeded{}));
                }
                data.lowlink[node] = pos_min(data.lowlink[node], data.visit_number[next_node]);
            }

            return true;
        });

        if (result == Inference::Contradiction) {
            // Shortcut if we contradicted at a deeper layer, trying to prove contradiction again will cause problems.
            return make_pair(result, back_edges);
        }

        if (data.lowlink[node] == data.visit_number[node]) {
            if (logger) {
                logger->emit_proof_comment("More than one SCC");
                prove_reachable_set_too_small(state, *logger, reason, succ, node, proof_data);
            }
            return make_pair(Inference::Contradiction, back_edges);
        }
        else
            return make_pair(result, back_edges);
    }

    auto check_sccs(
        State & state,
        ProofLogger * const logger,
        const Reason & reason,
        const vector<IntegerVariableID> & succ,
        const SCCOptions & options,
        SCCProofData & proof_data)
        -> Inference
    {
        auto result = Inference::NoChange;
        auto data = SCCPropagatorData(succ.size());

        state.for_each_value_while(succ[data.root], [&](Integer v) -> bool {
            auto next_node = v.raw_value;
            if (data.visit_number[next_node] == -1) {
                auto [explore_result, back_edges] = explore(state, logger, reason, next_node, succ, data, proof_data, options);
                increase_inference_to(result, explore_result);
                if (result == Inference::Contradiction) return false;

                if (back_edges.empty()) {
                    if (logger) {
                        logger->emit_proof_comment("No back edges");
                        prove_reachable_set_too_small(state, *logger, reason, succ, next_node, proof_data);
                    }
                    increase_inference_to(result, Inference::Contradiction);
                    return false;
                }
                else if (options.fix_req && back_edges.size() == 1) {
                    auto from_node = back_edges[0].first;
                    auto to_node = back_edges[0].second;
                    if (! state.optional_single_value(succ[from_node])) {
                        if (logger) {
                            logger->emit_proof_comment("Fix required back edge (" + to_string(from_node) + ", " + to_string(to_node) + "):");

                            prove_reachable_set_too_small(state, *logger, reason, succ, from_node, proof_data,
                                succ[from_node] != Integer{to_node});
                        }
                        increase_inference_to(result, state.infer(logger, succ[from_node] == Integer{to_node}, NoJustificationNeeded{}));
                    }
                }
                data.start_prev_subtree = data.end_prev_subtree + 1;
                data.end_prev_subtree = data.count - 1;
                data.prev_subroot = next_node;
            }
            return true;
        });

        if (result == Inference::Contradiction) return result;

        if (cmp_not_equal(data.count, succ.size())) {
            if (logger) {
                logger->emit_proof_comment("Disconnected graph");
                prove_reachable_set_too_small(state, *logger, reason, succ, data.root, proof_data);
            }

            return Inference::Contradiction;
        }

        if (options.prune_root && data.start_prev_subtree > 1) {
            state.for_each_value_while(succ[data.root], [&](Integer v) -> bool {
                if (data.visit_number[v.raw_value] < data.start_prev_subtree) {
                    if (logger) {
                        logger->emit_proof_comment("Prune impossible edges from root node");
                        prove_reachable_set_too_small(state, *logger, reason, succ, data.root, proof_data, succ[data.root] == v);
                    }
                    increase_inference_to(result, state.infer(logger, succ[data.root] != v, JustifyUsingRUP{reason}));
                }
                return true;
            });
        }

        return result;
    }

    auto propagate_circuit_using_scc(
        State & state,
        ProofLogger * const logger,
        const Reason & reason,
        const vector<IntegerVariableID> & succ,
        const SCCOptions & scc_options,
        const ConstraintStateHandle & pos_var_data_handle,
        const ConstraintStateHandle & proof_flag_data_handle,
        const ConstraintStateHandle & pos_alldiff_data_handle,
        const ConstraintStateHandle & unassigned_handle)
        -> Inference
    {
        auto & pos_var_data = any_cast<PosVarDataMap &>(state.get_persistent_constraint_state(pos_var_data_handle));
        auto result = propagate_non_gac_alldifferent(unassigned_handle, state, logger);
        if (result == Inference::Contradiction) return result;
        auto proof_data = SCCProofData{pos_var_data, proof_flag_data_handle, pos_alldiff_data_handle};
        increase_inference_to(result, check_sccs(state, logger, reason, succ, scc_options, proof_data));
        if (result == Inference::Contradiction) return result;
        auto & unassigned = any_cast<list<IntegerVariableID> &>(state.get_constraint_state(unassigned_handle));
        // Remove any newly assigned vals from unassigned
        auto it = unassigned.begin();
        while (it != unassigned.end()) {
            if (state.optional_single_value(*it))
                it = unassigned.erase(it);
            else
                ++it;
        }
        increase_inference_to(result, prevent_small_cycles(succ, pos_var_data, unassigned_handle, state, logger));
        return result;
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
            options = scc_options](State & state, ProofLogger * const logger) -> pair<Inference, PropagatorState> {
            auto reason = generic_reason(state, succ);
            auto result = propagate_circuit_using_scc(state, logger, reason,
                succ, options, pos_var_data_handle, proof_flag_data_handle, pos_alldiff_data_handle, unassigned_handle);
            return pair{result, PropagatorState::Enable};
        },
        triggers,
        "circuit");
}
