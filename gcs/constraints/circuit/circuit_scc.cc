#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/innards/propagators.hh>
#include <iostream>
#include <list>
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
using std::cout;
using std::get;
using std::holds_alternative;
using std::list;
using std::make_optional;
using std::make_pair;
using std::map;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::variant;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

namespace
{

    struct OrderingAssumption
    {
        ProofFlag assumption_flag;
        long first;
        long middle;
        long last;
    };

    auto select_root() -> long
    {
        // Might have better root selection in future
        // e.g. random
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
            root(select_root()),
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

    auto emit_proof_comment_if_enabled(const string & comment, const SCCOptions & options, State & state) -> void
    {
        // So that we can turn the comments off
        if (options.enable_comments) {
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                proof.emit_proof_comment(comment);
            }});
        }
    }

    auto prove_not_both(long i, long l, long k,
        ShiftedPosDataMaps & flag_data, const PosVarDataMap & pos_var_data, const bool using_shifted_pos,
        const SCCOptions & options, State & state) -> ProofLine
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

            state.infer_true(JustifyExplicitly{
                [&](Proof & proof) {
                    // Assumes l < k
                    PLine p_line;
                    p_line.add_and_saturate(shifted_pos_geq[i][k].forwards_reif_line);
                    p_line.add_and_saturate(shifted_pos_geq[i][l + 1].backwards_reif_line);
                    proof.emit_proof_line(p_line.str(), ProofLevel::Current);

                    emit_proof_comment_if_enabled("Not both: " +
                            shifted_pos_eq[i][k].comment_name + "=" + to_string(k) + " and " +
                            shifted_pos_eq[i][l].comment_name + "=" + to_string(l),
                        options, state);

                    neq_line = proof.emit_rup_proof_line(
                        WeightedPseudoBooleanSum{} + 1_i * ! shifted_pos_eq[i][k].flag + 1_i * ! shifted_pos_eq[i][l].flag >= 1_i,
                        ProofLevel::Top);
                }});

            shifted_pos_eq[i][l].neq_lines[k] = neq_line;
        }
        else {
            auto & shifted_pos = flag_data.shifted_pos_eq;
            if (shifted_pos[i][l].neq_lines.contains(k)) {
                // Don't reprove this if we did it before
                return shifted_pos[i][l].neq_lines[k];
            }
            state.infer_true(JustifyExplicitly{
                [&](Proof & proof) {
                    emit_proof_comment_if_enabled("Not both:" +
                            pos_var_data.at(i).comment_name + "=" + to_string(k) + " and " +
                            pos_var_data.at(i).comment_name + "=" + to_string(l),
                        options, state);

                    neq_line = proof.emit_rup_proof_line(
                        WeightedPseudoBooleanSum{} + 1_i * (pos_var_data.at(i).var != Integer{k}) + 1_i * (pos_var_data.at(i).var != Integer{l}) >= 1_i,
                        ProofLevel::Top);
                }});

            shifted_pos[i][l].neq_lines[k] = neq_line;
        }
        return neq_line;
    }

    auto prove_at_most_1_pos(const long & node, const set<long> & values, ShiftedPosDataMaps & flag_data,
        PosVarDataMap pos_var_data, bool using_shifted_pos,
        const SCCOptions & options, State & state) -> ProofLine
    {
        // Prove that at most one (shift)pos[node] == v is true for v in values
        ProofLine am1line;

        state.infer_true(JustifyExplicitly{[&](Proof & proof) {
            stringstream proofline;

            // We should document properly why this works somewhere now that it's in more than one place
            // Essentially, we can always recover an at most 1 constraint from a clique of "not both" constraints.
            if (values.size() > 1) {
                auto k = ++values.begin();
                auto l = values.begin();
                proofline << "p " << prove_not_both(node, (*l), (*k), flag_data, pos_var_data, using_shifted_pos, options, state);
                vector<ProofLine> neq_lines{};
                k++;
                auto k_count = 2;
                while (k != values.end()) {
                    proofline << " " << k_count << " * ";
                    l = values.begin();
                    while (l != k) {
                        proofline << prove_not_both(node, (*l), (*k), flag_data, pos_var_data, using_shifted_pos, options, state) << " + ";
                        l++;
                    }
                    proofline << k_count + 1 << " d ";
                    k++;
                    k_count++;
                }
                if (using_shifted_pos)
                    emit_proof_comment_if_enabled("AM1 " +
                            flag_data.shifted_pos_eq[node][*values.begin()].comment_name,
                        options, state);
                else
                    emit_proof_comment_if_enabled("AM1 p[" + to_string(node) + "]", options, state);
                am1line = proof.emit_proof_line(proofline.str(), ProofLevel::Top);
            }
            else if (values.size() == 1) {
                auto idx = *values.begin();
                if (using_shifted_pos) {
                    emit_proof_comment_if_enabled("AM1 " +
                            flag_data.shifted_pos_eq[node][*values.begin()].comment_name,
                        options, state);
                    am1line = proof.emit_rup_proof_line(
                        WeightedPseudoBooleanSum{} + 1_i * ! (flag_data.shifted_pos_eq[node][idx].flag) >= 0_i,
                        ProofLevel::Top);
                }
                else {
                    emit_proof_comment_if_enabled("AM1 p[" + to_string(node) + "]", options, state);
                    am1line = proof.emit_rup_proof_line(
                        WeightedPseudoBooleanSum{} + 1_i * ! (pos_var_data.at(node).var == Integer{idx}) >= 0_i,
                        ProofLevel::Top);
                }
            }
        }});

        return am1line;
    }

    auto prove_pos_alldiff_lines(State & state, const vector<IntegerVariableID> & succ, const PosVarDataMap & pos_var_data,
        PosAllDiffData & pos_alldiff_data, const SCCOptions & options) -> void
    {
        // Recover an all different constraint (al1/am1) over the pos variables
        // This is O(n^3) where n is the number of variables in the circuit but only needs to be done once.
        auto n = static_cast<long>(succ.size());

        // First prove the at least 1 lines
        state.infer_true(JustifyExplicitly{
            [&](Proof & proof) {
                emit_proof_comment_if_enabled("POS ALL DIFF LINES:", options, state);
                WeightedPseudoBooleanSum pb_sum;
                for (long i = 0; i < n; i++) {
                    pb_sum += 1_i * (pos_var_data.at(i).var == 0_i);
                }
                emit_proof_comment_if_enabled("AL1 p[i] = 0", options, state);
                pos_alldiff_data.at_least_1_lines[0] =
                    proof.emit_rup_proof_line(pb_sum >= 1_i, ProofLevel::Top);
                auto last_al1_line = pos_alldiff_data.at_least_1_lines[0];
                for (long j = 1; j < n; j++) {
                    pb_sum = WeightedPseudoBooleanSum{};
                    PLine p_line;
                    for (long i = 0; i < n; i++) {
                        auto next_pos_vars = WeightedPseudoBooleanSum{};
                        for (long k = 0; k < n; k++) {
                            next_pos_vars += 1_i * (pos_var_data.at(k).var == Integer{j});
                            proof.emit_rup_proof_line(
                                WeightedPseudoBooleanSum{} + 1_i * ! (pos_var_data.at(i).var == Integer{j - 1}) +
                                        1_i * ! (succ[i] == Integer{k}) + 1_i * (pos_var_data.at(k).var == Integer{j}) >=
                                    1_i,
                                ProofLevel::Top);
                        }

                        p_line.add_and_saturate(
                            proof.emit_rup_proof_line(
                                next_pos_vars + 1_i * ! (pos_var_data.at(i).var == Integer{j - 1}) >= 1_i, ProofLevel::Top));
                    }
                    emit_proof_comment_if_enabled("AL1 p[i] = " + to_string(j), options, state);
                    p_line.add_and_saturate(last_al1_line);
                    pos_alldiff_data.at_least_1_lines[j] = proof.emit_proof_line(p_line.str(), ProofLevel::Top);
                    last_al1_line = pos_alldiff_data.at_least_1_lines[j];
                }
            }});

        // Now prove the at most 1 lines
        for (long i = 0; i < n; i++) {
            set<long> values{};
            for (int j = 0; j < n; j++) {
                values.insert(j);
            }
            ShiftedPosDataMaps dummy{};
            pos_alldiff_data.at_most_1_lines.emplace(i, prove_at_most_1_pos(i, values, dummy, pos_var_data, false, options, state));
        }
    }

    auto create_flag_for_greater_than(const long & root, const long & i, ShiftedPosDataMaps & flag_data_for_root,
        const PosVarDataMap & pos_var_data, PosAllDiffData & pos_alldiff_data,
        const vector<IntegerVariableID> & succ, const SCCOptions & options, State & state) -> ProofFlagData
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
            greater_than_flag = state.maybe_proof()->create_proof_flag(flag_name);

            auto forwards_reif_line = state.maybe_proof()->emit_red_proof_lines_forward_reifying(
                WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(root).var + -1_i * pos_var_data.at(i).var >= 1_i,
                greater_than_flag, ProofLevel::Top);

            if (pos_alldiff_data.at_least_1_lines.empty()) {
                prove_pos_alldiff_lines(state, succ, pos_var_data, pos_alldiff_data, options);
            }

            long backwards_reif_line;
            if (i != root) {
                // Redundance subproof:
                auto subproofs = make_optional(map<string, JustifyExplicitly>{});
                subproofs.value().emplace(to_string(forwards_reif_line), JustifyExplicitly{[&](Proof & proof) {
                    proof.emit_proof_line("     p -2 " + proof.proof_name(greater_than_flag) + " w", ProofLevel::Top);
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
                        proof.emit_proof_line(p_line.str(), ProofLevel::Top);
                        proof.emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * ! (pos_var_data.at(i).var == Integer{k}) >= 1_i, ProofLevel::Top);
                    }
                    proof.emit_rup_proof_line(WeightedPseudoBooleanSum{} >= 1_i, ProofLevel::Top);
                }});

                backwards_reif_line = state.maybe_proof()->emit_red_proof_lines_reverse_reifying(
                    WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(root).var + -1_i * pos_var_data.at(i).var >= 0_i,
                    greater_than_flag, ProofLevel::Top, subproofs);
            }
            else {
                // If i == root, d[r, i] is just "false"
                backwards_reif_line = state.maybe_proof()->emit_red_proof_lines_reverse_reifying(
                    WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(root).var + -1_i * pos_var_data.at(i).var >= 1_i,
                    greater_than_flag, ProofLevel::Top);
            }

            root_gt_data[i] = ProofFlagData{
                flag_name, greater_than_flag, forwards_reif_line, backwards_reif_line, {}};
            return root_gt_data[i];
        }
    }

    auto create_shifted_pos(const long & root, const long & i, const long & j, ShiftedPosDataMaps & flag_data_for_root,
        const PosVarDataMap & pos_var_data, PosAllDiffData & pos_alldiff_data,
        const vector<IntegerVariableID> & succ, const SCCOptions & options, State & state)
    {
        // Define a "shifted" pos flag q[r, i], that represents the value of p[i] shifted relative to p[root] mod n
        // i.e. q[r, i] == j <=> p[i] - p[r] + n * d[r, i] (the last term corrects for when we go negative)
        auto n = static_cast<long>(succ.size());
        ProofFlagData greater_than_flag_data{};

        greater_than_flag_data = create_flag_for_greater_than(root, i, flag_data_for_root, pos_var_data, pos_alldiff_data, succ, options, state);
        auto greater_than_flag = greater_than_flag_data.flag;

        auto maybe_create_and_emplace_flag_data =
            [&](ProofFlagDataMap & flag_data, const long i, const long j, const WeightedPseudoBooleanLessEqual & definition, const string & name, const string & name_suffix) {
                if (! flag_data[i].count(j)) {
                    auto [flag, forwards_reif_line, backwards_reif_line] = state.maybe_proof()->create_proof_flag_reifying(definition, name + name_suffix, ProofLevel::Top);
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

    auto prove_root_is_0(const long & root, ShiftedPosDataMaps & flag_data_for_root, const PosVarDataMap & pos_var_data, PosAllDiffData & pos_alldiff_data,
        const vector<IntegerVariableID> & succ, const SCCOptions & options, State & state) -> ProofLine
    {
        // Prove that (shift)pos[root]== 0
        emit_proof_comment_if_enabled("AL1 pos = " + to_string(0), options, state);

        auto line = ProofLine{};
        if (root != 0) {
            create_shifted_pos(root, root, 0, flag_data_for_root, pos_var_data, pos_alldiff_data, succ, options, state);
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                line = proof.emit_rup_proof_line(
                    WeightedPseudoBooleanSum{} + 1_i * flag_data_for_root.shifted_pos_eq[root][0].flag >= 1_i,
                    ProofLevel::Current);
            }});
        }
        else {
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                line = proof.emit_rup_proof_line(
                    WeightedPseudoBooleanSum{} + 1_i * (pos_var_data.at(root).var == 0_i) >= 1_i,
                    ProofLevel::Current);
            }});
        }

        return line;
    }

    auto prove_mid_is_at_least(const long & root, const OrderingAssumption & ordering, const long & val, const Literal & assumption, ShiftedPosDataMaps & flag_data_for_root,
        const PosVarDataMap & pos_var_data, PosAllDiffData & pos_alldiff_data,
        const vector<IntegerVariableID> & succ, const SCCOptions & options, State & state)
    {
        // The ordering assumption assumes we will see "middle" before "last" when we start at "first"
        // If we haven't seen middle yet under our assumptions we can prove (shift)pos[middle] >= val
        auto mid_at_least_line = ProofLine{};
        auto & mid = ordering.middle;
        emit_proof_comment_if_enabled("Haven't seen mid node yet:", options, state);
        state.infer_true(JustifyExplicitly{[&](Proof & proof) {
            if (root != 0) {
                create_shifted_pos(root, mid, val, flag_data_for_root, pos_var_data, pos_alldiff_data, succ, options, state);

                if (val == 1) {
                    PLine p_line;
                    p_line.add_and_saturate(flag_data_for_root.shifted_pos_geq[mid][1].backwards_reif_line);
                    p_line.add_and_saturate(flag_data_for_root.greater_than[mid].backwards_reif_line);
                    proof.emit_proof_line(p_line.str(), ProofLevel::Temporary);
                }

                mid_at_least_line = proof.emit_rup_proof_line_under_trail(state,
                    WeightedPseudoBooleanSum{} + 1_i * ! ordering.assumption_flag + 1_i * ! assumption + 1_i * flag_data_for_root.shifted_pos_geq[mid][val].flag >= 1_i,
                    ProofLevel::Current);
            }
            else {
                mid_at_least_line = proof.emit_rup_proof_line_under_trail(state,
                    WeightedPseudoBooleanSum{} + 1_i * (pos_var_data.at(mid).var >= Integer{val}) >= 1_i,
                    ProofLevel::Current);
            }
        }});
    }

    auto prove_pos_and_node_implies_next_node(const long & root, const long & node, const long & next_node, const long & count,
        ShiftedPosDataMaps & flag_data_for_root, const PosVarDataMap & pos_var_data, PosAllDiffData & pos_alldiff_data,
        const vector<IntegerVariableID> & succ, const SCCOptions & options, State & state)
    {
        // successor_implies_line := Prove (shift)pos[node][count - 1] /\ succ[node] = next_node => (shift)pos[next_node][count]
        auto successor_implies_line = ProofLine{};
        auto n = static_cast<long>(succ.size());

        if (root != 0) {
            create_shifted_pos(root, next_node, count, flag_data_for_root, pos_var_data, pos_alldiff_data, succ, options, state);
            auto & root_greater_than = flag_data_for_root.greater_than;
            auto & shifted_pos_geq = flag_data_for_root.shifted_pos_geq;
            auto & shifted_pos_eq = flag_data_for_root.shifted_pos_eq;

            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
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
                        p_line << proof.emit_rup_proof_line(
                                      WeightedPseudoBooleanSum{} + 1_i * ! (succ[node] == Integer{next_node}) + 1_i * ! root_greater_than.at(node).flag >= 1_i,
                                      ProofLevel::Current)
                               << " ";
                        p_line << proof.emit_rup_proof_line(
                                      WeightedPseudoBooleanSum{} + 1_i * ! (succ[node] == Integer{next_node}) + 1_i * root_greater_than.at(next_node).flag >= 1_i,
                                      ProofLevel::Current)
                               << " + ";
                    }

                    p_line
                        << to_string(n) << " * "
                        << pos_var_data.at(node).plus_one_lines.at(next_node).geq_line << " + "
                        << shifted_pos_geq.at(node).at(count - 1).forwards_reif_line << " + "
                        << shifted_pos_geq.at(next_node).at(count).backwards_reif_line << " +";
                    proof.emit_proof_line(p_line.str(), ProofLevel::Current);

                    p_line.str("");
                    p_line << "p ";

                    //                    if (next_node != 0) {
                    p_line << pos_var_data.at(node).plus_one_lines.at(next_node).geq_line << " "
                           << root_greater_than.at(node).backwards_reif_line << " + "
                           << root_greater_than.at(next_node).forwards_reif_line << " + "
                           << to_string(2 * n) << " d ";
                    //                    }
                    //                    else
                    //                        p_line << proof.emit_rup_proof_line(
                    //                                      WeightedPseudoBooleanSum{} + 1_i * ! (succ[node] == Integer{next_node}) + 1_i * root_greater_than.at(node).flag + 1_i * ! root_greater_than.at(next_node).flag >= 1_i,
                    //                                      ProofLevel::Current)
                    //                               << " ";

                    p_line
                        << to_string(n) << " * "
                        << pos_var_data.at(node).plus_one_lines.at(next_node).leq_line << " + "
                        << shifted_pos_geq.at(node).at(count).backwards_reif_line << " + "
                        << shifted_pos_geq.at(next_node).at(count + 1).forwards_reif_line << " +";
                    proof.emit_proof_line(p_line.str(), ProofLevel::Current);

                    emit_proof_comment_if_enabled("Next implies: succ[" + to_string(node) + "] = " + to_string(next_node) + " and " +
                            shifted_pos_eq[node][count - 1].comment_name + " = " + to_string(count - 1) + " => " +
                            shifted_pos_eq[next_node][count].comment_name + " = " + to_string(count),
                        options, state);

                    // RUP shifted_pos[node][count-1] /\ succ[node] = next_node => shifted_pos[next_node][i]
                    successor_implies_line = proof.emit_rup_proof_line_under_trail(state,
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
                    proof.emit_proof_line(p_line.str(), ProofLevel::Current);
                    p_line.str("");
                    p_line << "p ";
                    p_line << shifted_pos_geq[node][count].backwards_reif_line << " ";
                    p_line << pos_var_data.at(node).plus_one_lines.at(next_node).leq_line << " + s";
                    proof.emit_proof_line(p_line.str(), ProofLevel::Current);

                    emit_proof_comment_if_enabled("Next implies: succ[" + to_string(node) + "] = " + to_string(next_node) + " and " +
                            shifted_pos_eq[node][count - 1].comment_name + " = " + to_string(count - 1) + " => 0 >= 1",
                        options, state);

                    successor_implies_line = proof.emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * (! shifted_pos_eq[node][count - 1].flag) + 1_i * (succ[node] != Integer{next_node}) >= 1_i, ProofLevel::Current);
                    // proof.emit_proof_line("fail", ProofLevel::Top);
                }
            }});
        }
        else {
            // Not using shifted pos, just use the actual pos values
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                // succ[node] == next_node /\ pos[node] == count - 1 => pos[next_node] == count
                successor_implies_line = proof.emit_rup_proof_line(
                    WeightedPseudoBooleanSum{} + 1_i * (pos_var_data.at(node).var != Integer{count - 1}) +
                            1_i * (succ[node] != Integer{next_node}) + 1_i * (pos_var_data.at(next_node).var == Integer{count}) >=
                        1_i,
                    ProofLevel::Current);
            }});
        }

        return successor_implies_line;
    }

    auto prove_not_same_val(const long & root, const long & middle, const long & next_node, const long & count,
        map<long, ShiftedPosDataMaps> & flag_data, const PosVarDataMap & pos_var_data, PosAllDiffData & pos_alldiff_data,
        const vector<IntegerVariableID> & succ, const SCCOptions & options, State & state)
    {
        auto succesor_implies_not_mid_line = ProofLine{};
        // successor_implies_line :=
        // Prove (shift)pos[next_node][count] => ! (shift)pos[mid][count]
        create_shifted_pos(root, middle, count, flag_data[root], pos_var_data, pos_alldiff_data,
            succ, options, state);
        emit_proof_comment_if_enabled("Successor implies not mid", options, state);
        auto n = static_cast<long>(succ.size());
        if (root != 0) {
            create_flag_for_greater_than(next_node, middle, flag_data[next_node], pos_var_data, pos_alldiff_data,
                succ, options, state);

            PLine temp_p_line;

            auto & shifted_pos_geq = flag_data[root].shifted_pos_geq;
            auto & shifted_pos_eq = flag_data[root].shifted_pos_eq;

            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                // TODO: All these should be ProofLevel::Temporary, but unfortunately that fails in specific instances
                // e.g. build/circuit_random --n 9 --seed 1783129817
                emit_proof_comment_if_enabled("Step 1", options, state);

                temp_p_line.add_and_saturate(shifted_pos_geq[next_node][count + 1].backwards_reif_line);
                temp_p_line.add_and_saturate(shifted_pos_geq[middle][count].forwards_reif_line);
                auto geq_and_leq = proof.emit_proof_line(temp_p_line.str(), ProofLevel::Current);

                temp_p_line.clear();
                temp_p_line.add_and_saturate(shifted_pos_geq[next_node][count].forwards_reif_line);
                temp_p_line.add_and_saturate(shifted_pos_geq[middle][count + 1].backwards_reif_line);
                emit_proof_comment_if_enabled("Step 2", options, state);
                auto leq_and_geq = proof.emit_proof_line(temp_p_line.str(), ProofLevel::Current);

                temp_p_line.clear();
                temp_p_line.add_and_saturate(geq_and_leq);
                temp_p_line.add_and_saturate(flag_data[next_node].greater_than[middle].forwards_reif_line);
                emit_proof_comment_if_enabled("Step 3", options, state);
                proof.emit_proof_line(temp_p_line.str(), ProofLevel::Current);
                temp_p_line.clear();

                temp_p_line.add_and_saturate(leq_and_geq);
                temp_p_line.add_and_saturate(proof.emit_rup_proof_line(
                    WeightedPseudoBooleanSum{} + -1_i * pos_var_data.at(next_node).var + 1_i * pos_var_data.at(middle).var >= Integer{-n + 1}, ProofLevel::Current));
                emit_proof_comment_if_enabled("Step 4", options, state);
                proof.emit_proof_line(temp_p_line.str(), ProofLevel::Current);
                temp_p_line.clear();

                emit_proof_comment_if_enabled("Step 5", options, state);
                proof.emit_rup_proof_line_under_trail(state,
                    WeightedPseudoBooleanSum{} +
                            1_i * ! flag_data[root].greater_than[middle].flag +
                            1_i * ! flag_data[next_node].greater_than[middle].flag +
                            1_i * ! shifted_pos_eq[middle][count].flag +
                            1_i * (! shifted_pos_eq[next_node][count].flag) >=
                        1_i,
                    ProofLevel::Current);

                proof.emit_rup_proof_line_under_trail(state,
                    WeightedPseudoBooleanSum{} +
                            1_i * ! flag_data[next_node].greater_than[middle].flag +
                            1_i * ! shifted_pos_eq[middle][count].flag +
                            1_i * (! shifted_pos_eq[next_node][count].flag) >=
                        1_i,
                    ProofLevel::Current);

                temp_p_line.add_and_saturate(leq_and_geq);
                temp_p_line.add_and_saturate(flag_data[next_node].greater_than[middle].backwards_reif_line);
                emit_proof_comment_if_enabled("Step 6", options, state);
                proof.emit_proof_line(temp_p_line.str(), ProofLevel::Current);
                temp_p_line.clear();

                temp_p_line.add_and_saturate(geq_and_leq);
                temp_p_line.add_and_saturate(proof.emit_rup_proof_line(
                    WeightedPseudoBooleanSum{} + -1_i * pos_var_data.at(middle).var + 1_i * pos_var_data.at(next_node).var >= Integer{-n + 1}, ProofLevel::Current));
                emit_proof_comment_if_enabled("Step 7", options, state);
                proof.emit_proof_line(temp_p_line.str(), ProofLevel::Current);
                temp_p_line.clear();

                proof.emit_rup_proof_line_under_trail(state,
                    WeightedPseudoBooleanSum{} +
                            1_i * ! flag_data[root].greater_than[next_node].flag +
                            1_i * flag_data[next_node].greater_than[middle].flag +
                            1_i * ! shifted_pos_eq[middle][count].flag +
                            1_i * (! shifted_pos_eq[next_node][count].flag) >=
                        1_i,
                    ProofLevel::Current);

                emit_proof_comment_if_enabled("Step 8", options, state);
                proof.emit_rup_proof_line_under_trail(state,
                    WeightedPseudoBooleanSum{} + 1_i * ! flag_data[next_node].greater_than[middle].flag +
                            1_i * ! shifted_pos_eq[middle][count].flag +
                            1_i * (! shifted_pos_eq[next_node][count].flag) >=
                        1_i,
                    ProofLevel::Current);

                succesor_implies_not_mid_line = proof.emit_rup_proof_line_under_trail(state,
                    WeightedPseudoBooleanSum{} + 1_i * ! shifted_pos_eq[middle][count].flag +
                            1_i * (! shifted_pos_eq[next_node][count].flag) >=
                        1_i,
                    ProofLevel::Current);
            }});
        }
        else {
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                succesor_implies_not_mid_line = proof.emit_rup_proof_line_under_trail(state,
                    WeightedPseudoBooleanSum{} +
                            1_i * ! (pos_var_data.at(middle).var == Integer{count}) +
                            1_i * ! (pos_var_data.at(next_node).var == Integer{count}) >=
                        1_i,
                    ProofLevel::Temporary);
            }});
        }

        return succesor_implies_not_mid_line;
    }

    auto prove_exclude_last_based_on_ordering(const OrderingAssumption & ordering, const long & root, const long & count, const Literal & assumption,
        map<long, ShiftedPosDataMaps> & flag_data, const PosVarDataMap & pos_var_data, PosAllDiffData & pos_alldiff_data,
        const vector<IntegerVariableID> & succ, const SCCOptions & options, State & state) -> ProofLine
    {
        // Based on an ordering assumption and the fact we haven't seen
        auto mid = ordering.middle;
        auto last = ordering.last;
        auto exclusion_line = ProofLine{};

        emit_proof_comment_if_enabled("Exclude based on ordering", options, state);

        if (root != 0) {
            auto & shifted_pos_geq = flag_data[root].shifted_pos_geq;
            auto & shifted_pos_eq = flag_data[root].shifted_pos_eq;

            create_shifted_pos(root, mid, count, flag_data[root], pos_var_data, pos_alldiff_data,
                succ, options, state);
            create_shifted_pos(root, last, count, flag_data[root], pos_var_data, pos_alldiff_data,
                succ, options, state);
            PLine p_line;

            p_line.add_and_saturate(shifted_pos_geq[mid][count].forwards_reif_line);
            p_line.add_and_saturate(shifted_pos_geq[last][count].backwards_reif_line);
            p_line.add_and_saturate(flag_data[mid].greater_than[last].backwards_reif_line);

            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                p_line.add_and_saturate(proof.emit_rup_proof_line(
                    WeightedPseudoBooleanSum{} + 1_i * flag_data[root].greater_than[last].flag + 1_i * flag_data[last].greater_than[root].flag >= 1_i,
                    ProofLevel::Current));

                proof.emit_proof_line(p_line.str(), ProofLevel::Temporary);
                exclusion_line = proof.emit_rup_proof_line_under_trail(state,
                    WeightedPseudoBooleanSum{} + 1_i * ! assumption + 1_i * ! ordering.assumption_flag + 1_i * ! shifted_pos_eq[last][count].flag >= 1_i,
                    ProofLevel::Current);
            }});
        }
        else {
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                exclusion_line = proof.emit_rup_proof_line_under_trail(state,
                    WeightedPseudoBooleanSum{} + 1_i * ! assumption + 1_i * ! ordering.assumption_flag + 1_i * ! (pos_var_data.at(last).var == Integer{count}) >= 1_i,
                    ProofLevel::Current);
            }});
        }

        return exclusion_line;
    }

    auto prove_reachable_set_too_small(const vector<IntegerVariableID> & succ, const long & root, SCCProofData & proof_data,
        const SCCOptions & options, State & state,
        const Literal & assumption = TrueLiteral{}, const optional<OrderingAssumption> & ordering = nullopt)
    {
        if (! state.maybe_proof()) return;
        emit_proof_comment_if_enabled("REACHABLE SET  from " + to_string(root), options, state);

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

        auto last_al1_line = prove_root_is_0(root, flag_data_for_root, pos_var_data, pos_alldiff_data, succ, options, state);
        contradiction_line.add_and_saturate(last_al1_line);

        if (ordering) {
            if (ordering.value().first != root) {
                throw UnexpectedException{"SCC Proof Error: First component of ordering assumption must be root of reachability argument."};
            }
            // Mid is not the root, so it must be at least 1
            prove_mid_is_at_least(root, ordering.value(), 1, assumption, flag_data_for_root, pos_var_data, pos_alldiff_data, succ, options, state);
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
                        prove_pos_and_node_implies_next_node(root, node, next_node, count,
                            flag_data_for_root, pos_var_data, pos_alldiff_data, succ, options, state));

                    if (ordering && next_node == ordering.value().last && ! seen_middle) {
                        // Ordering says that since we haven't seen "middle" yet, we can't visit "last"
                        exclude_based_on_ordering = true;
                    }
                    else if (ordering && ! seen_middle && next_node != ordering.value().middle) {
                        // If we see any other node, prove that we can't have middle == count for this
                        // node and pos combination
                        add_for_node_implies_not_mid.add_and_saturate(prove_not_same_val(root, ordering.value().middle, next_node, count,
                            flag_data, pos_var_data, pos_alldiff_data, succ, options, state));
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

                state.infer_true(JustifyExplicitly{
                    [&](Proof & proof) {
                        add_for_node_implies_at_least_1.add_and_saturate(
                            proof.emit_rup_proof_line_under_trail(state,
                                possible_next_nodes_sum + 1_i * ! assumption >= 1_i, ProofLevel::Temporary));

                        add_for_at_least_1.add_and_saturate(
                            proof.emit_proof_line(add_for_node_implies_at_least_1.str(), ProofLevel::Current));

                        if (ordering && ! seen_middle) {
                            if (add_for_node_implies_not_mid.count >= 1) {
                                add_for_not_mid.add_and_saturate(
                                    proof.emit_proof_line(add_for_node_implies_not_mid.str(), ProofLevel::Current));
                            }
                        }
                    }});
            }

            emit_proof_comment_if_enabled("AL1 pos = " + to_string(count), options, state);
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                add_for_at_least_1.divide_by(add_for_at_least_1.count);
                last_al1_line = proof.emit_proof_line(add_for_at_least_1.str(), ProofLevel::Current);
                if (exclude_based_on_ordering) {
                    PLine new_last_al1_line;
                    new_last_al1_line.add_and_saturate(
                        prove_exclude_last_based_on_ordering(ordering.value(), root, count, assumption, flag_data, pos_var_data, pos_alldiff_data,
                            succ, options, state));
                    new_last_al1_line.add_and_saturate(last_al1_line);
                    last_al1_line = proof.emit_proof_line(new_last_al1_line.str(), ProofLevel::Current);
                }
                contradiction_line.add_and_saturate(last_al1_line);
            }});

            if (ordering && ! seen_middle) {
                add_for_not_mid.add_and_saturate(last_al1_line);
                emit_proof_comment_if_enabled("Not mid.", options, state);
                state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                    proof.emit_proof_line(add_for_not_mid.str(), ProofLevel::Current);
                }});
                prove_mid_is_at_least(root, ordering.value(), count + 1, assumption, flag_data_for_root,
                    pos_var_data, pos_alldiff_data, succ, options, state);
            }

            last_reached_nodes = new_reached_nodes;

            // Continue until we've logged more layers than we have reached nodes (Hall violator)
            all_reached_nodes.insert(new_reached_nodes.begin(), new_reached_nodes.end());
            count++;
        }

        // At most one lines
        for (const auto & node : all_reached_nodes) {
            contradiction_line.add_and_saturate(
                prove_at_most_1_pos(node, all_values_seen[node], flag_data_for_root, pos_var_data,
                    using_shifted_pos, options, state));
        }

        emit_proof_comment_if_enabled("Hall violator gives contradiction: ", options, state);
        state.infer_true(JustifyExplicitly{[&](Proof & proof) {
            proof.emit_proof_line(contradiction_line.str(), ProofLevel::Current);
        }});
    }

    auto prove_skipped_subtree(const vector<IntegerVariableID> & succ, const long & node, const long & next_node, const long & root, const long & skipped_subroot,
        SCCProofData & proof_data, const SCCOptions & options, State & state)
    {
        if (! state.maybe_proof()) return;

        auto & flag_data = any_cast<map<long, ShiftedPosDataMaps> &>(state.get_persistent_constraint_state(proof_data.proof_flag_data_handle));
        auto & pos_all_diff_data = any_cast<PosAllDiffData &>(state.get_persistent_constraint_state(proof_data.pos_alldiff_data_handle));
        auto & pos_var_data = proof_data.pos_var_data;

        auto root_gt_next = create_flag_for_greater_than(root, next_node, flag_data[root], pos_var_data, pos_all_diff_data, succ, options, state);
        auto subroot_gt_root = create_flag_for_greater_than(skipped_subroot, root, flag_data[skipped_subroot], pos_var_data, pos_all_diff_data, succ, options, state);
        auto next_gt_subroot = create_flag_for_greater_than(next_node, skipped_subroot, flag_data[next_node], pos_var_data, pos_all_diff_data, succ, options, state);

        auto node_then_subroot_then_root = state.maybe_proof()->create_proof_flag_reifying(
            WeightedPseudoBooleanSum{} + 1_i * ! root_gt_next.flag + 1_i * ! subroot_gt_root.flag + 1_i * ! next_gt_subroot.flag >= 2_i, "ord1", ProofLevel::Current);

        OrderingAssumption ordering1{
            get<0>(node_then_subroot_then_root),
            next_node,
            skipped_subroot,
            root};

        prove_reachable_set_too_small(succ, next_node, proof_data, options, state, succ[node] == Integer{next_node}, ordering1);

        auto subroot_gt_node = create_flag_for_greater_than(
            skipped_subroot, node, flag_data[skipped_subroot], pos_var_data, pos_all_diff_data, succ, options, state);
        auto node_gt_root = create_flag_for_greater_than(
            node, root, flag_data[node], pos_var_data, pos_all_diff_data, succ, options, state);

        auto subroot_then_node_then_root = state.maybe_proof()->create_proof_flag_reifying(
            WeightedPseudoBooleanSum{} + 1_i * ! subroot_gt_node.flag + 1_i * ! node_gt_root.flag + 1_i * subroot_gt_root.flag >= 2_i, "ord2", ProofLevel::Current);

        OrderingAssumption ordering2{
            get<0>(subroot_then_node_then_root),
            skipped_subroot,
            node,
            root};

        prove_reachable_set_too_small(succ, skipped_subroot, proof_data, options, state, succ[node] == Integer{next_node}, ordering2);

        state.infer_true(JustifyExplicitly{[&](Proof & proof) {
            stringstream final_contradiction_p_line;
            final_contradiction_p_line << "p ";
            stringstream temp_p_line;
            temp_p_line << "p ";
            temp_p_line << pos_var_data.at(node).plus_one_lines.at(next_node).geq_line << " ";
            temp_p_line << root_gt_next.forwards_reif_line << " + ";
            proof.emit_proof_line(temp_p_line.str(), ProofLevel::Temporary);
            final_contradiction_p_line << proof.emit_rup_proof_line(
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
            proof.emit_proof_line(temp_p_line.str(), ProofLevel::Temporary);
            final_contradiction_p_line << proof.emit_rup_proof_line(
                                              WeightedPseudoBooleanSum{} + 1_i * (succ[node] != Integer{next_node}) +
                                                      1_i * ! next_gt_subroot.flag + 1_i * ! subroot_gt_node.flag >=
                                                  1_i,
                                              ProofLevel::Current)
                                       << " + ";
            final_contradiction_p_line << get<2>(node_then_subroot_then_root) << " + ";
            final_contradiction_p_line << get<2>(subroot_then_node_then_root) << " + s ";
            proof.emit_proof_line(final_contradiction_p_line.str(), ProofLevel::Current);

            proof.emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * (succ[node] != Integer{next_node}) >= 1_i, ProofLevel::Current);
            // proof.emit_proof_line("fail", ProofLevel::Top);
        }});
    }

    auto explore(const long & node, const vector<IntegerVariableID> & succ, SCCPropagatorData & data, SCCProofData & proof_data,
        const SCCOptions & options, State & state)
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
                auto explore_result = explore(next_node, succ, data, proof_data, options, state);
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
                    if (next_node == data.root) {
                        emit_proof_comment_if_enabled("Pruning edge to the root from a subtree other than the first (" +
                                to_string(node) + ", " + to_string(next_node) + ")",
                            options, state);
                        prove_reachable_set_too_small(succ, data.prev_subroot, proof_data, options, state, succ[node] == w);
                    }
                    else {
                        emit_proof_comment_if_enabled("Pruning edge that would skip subtree (" +
                                to_string(node) + ", " + to_string(next_node) + ")",
                            options, state);
                        // prove_reachable_set_too_small(succ, data.prev_subroot, proof_data, options, state, succ[node] == w);
                        prove_skipped_subtree(succ, node, next_node, data.root, data.prev_subroot, proof_data, options, state);
                    }

                    increase_inference_to(result, state.infer(succ[node] != w, NoJustificationNeeded{}));
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
            state.infer_true(JustifyExplicitly{[&](Proof &) {
                emit_proof_comment_if_enabled("More than one SCC", options, state);
                //                if (node == data.root) {
                //                    int unreachable_node = 0;
                //                    while (data.visit_number[unreachable_node] != -1) {
                //                        unreachable_node++;
                //                    }
                //                    prove_reachable_set_too_small(succ, unreachable_node, proof_data, options, state);
                //                }
                //                else {
                prove_reachable_set_too_small(succ, node, proof_data, options, state);
                //                }
            }});
            return make_pair(Inference::Contradiction, back_edges);
        }
        else
            return make_pair(result, back_edges);
    }

    auto check_sccs(
        const vector<IntegerVariableID> & succ,
        const SCCOptions & options,
        SCCProofData & proof_data,
        State & state)
        -> Inference
    {
        auto result = Inference::NoChange;
        auto data = SCCPropagatorData(succ.size());

        state.for_each_value_while(succ[data.root], [&](Integer v) -> bool {
            auto next_node = v.raw_value;
            if (data.visit_number[next_node] == -1) {
                auto [explore_result, back_edges] = explore(next_node, succ, data, proof_data, options, state);
                increase_inference_to(result, explore_result);
                if (result == Inference::Contradiction) return false;

                if (back_edges.empty()) {
                    emit_proof_comment_if_enabled("No back edges:", options, state);
                    prove_reachable_set_too_small(succ, next_node, proof_data, options, state);
                    increase_inference_to(result, Inference::Contradiction);
                    return false;
                }
                else if (options.fix_req && back_edges.size() == 1) {
                    auto from_node = back_edges[0].first;
                    auto to_node = back_edges[0].second;
                    if (! state.optional_single_value(succ[from_node])) {
                        emit_proof_comment_if_enabled("Fix required back edge (" + to_string(from_node) + ", " + to_string(to_node) + "):",
                            options, state);

                        prove_reachable_set_too_small(succ, from_node, proof_data, options, state, succ[from_node] != Integer{to_node});
                        increase_inference_to(result, state.infer(succ[from_node] == Integer{to_node}, NoJustificationNeeded{}));
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
            emit_proof_comment_if_enabled("Disconnected graph:", options, state);
            prove_reachable_set_too_small(succ, data.root, proof_data, options, state);

            return Inference::Contradiction;
        }

        if (options.prune_root && data.start_prev_subtree > 1) {
            state.for_each_value_while(succ[data.root], [&](Integer v) -> bool {
                if (data.visit_number[v.raw_value] < data.start_prev_subtree) {
                    emit_proof_comment_if_enabled("Prune impossible edges from root node:", options, state);
                    prove_reachable_set_too_small(succ, data.root, proof_data, options, state, succ[data.root] == v);
                    increase_inference_to(result, state.infer(succ[data.root] != v, JustifyUsingRUP{}));
                }
                return true;
            });
        }

        return result;
    }

    auto propagate_circuit_using_scc(const vector<IntegerVariableID> & succ,
        const SCCOptions & scc_options,
        const ConstraintStateHandle & pos_var_data_handle,
        const ConstraintStateHandle & proof_flag_data_handle,
        const ConstraintStateHandle & pos_alldiff_data_handle,
        const ConstraintStateHandle & unassigned_handle,
        State & state)
        -> Inference
    {
        auto & pos_var_data = any_cast<PosVarDataMap &>(state.get_persistent_constraint_state(pos_var_data_handle));
        auto result = propagate_non_gac_alldifferent(unassigned_handle, state);
        if (result == Inference::Contradiction) return result;
        auto proof_data = SCCProofData{pos_var_data, proof_flag_data_handle, pos_alldiff_data_handle};
        increase_inference_to(result, check_sccs(succ, scc_options, proof_data, state));
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
        increase_inference_to(result, prevent_small_cycles(succ, pos_var_data, unassigned_handle, state));
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

auto CircuitSCC::install(Propagators & propagators, State & initial_state) && -> void
{
    auto pos_var_data = CircuitBase::set_up(propagators, initial_state);

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
            options = scc_options](State & state) -> pair<Inference, PropagatorState> {
            auto result = propagate_circuit_using_scc(
                succ, options, pos_var_data_handle, proof_flag_data_handle, pos_alldiff_data_handle, unassigned_handle, state);
            return pair{result, PropagatorState::Enable};
        },
        triggers,
        "circuit");
}