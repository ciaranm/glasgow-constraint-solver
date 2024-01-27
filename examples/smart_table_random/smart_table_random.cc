#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <tuple>
#include <vector>

#include <boost/program_options.hpp>

using namespace gcs;

namespace po = boost::program_options;

using std::cout;
using std::endl;
using std::iota;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::shuffle;
using std::ssize;
using std::stoll;
using std::string;
using std::stringstream;
using std::uniform_int_distribution;
using std::vector;

using namespace innards;

auto index_of(const IntegerVariableID & val, const vector<IntegerVariableID> & vec) -> int
{
    ptrdiff_t pos = distance(vec.begin(), find(vec.begin(), vec.end(), val));
    return (int)pos;
}

auto random_tree_edges(int k, mt19937 & rng, int offset)
{
    vector<pair<int, int>> edges;

    // Generate a random tree using Prüfer sequence
    uniform_int_distribution<> rand0_to_km1(0, k - 1);
    vector<int> prufer_seq;
    vector<int> count_in_prufer(k, 0);

    for (auto i = 0; i < k - 2; i++) {
        auto rand_val = rand0_to_km1(rng);
        prufer_seq.emplace_back(rand_val);
        count_in_prufer[rand_val]++;
    }

    for (const auto & v1 : prufer_seq) {
        for (int v2 = 0; v2 < k; v2++) {
            if (count_in_prufer[v2] == 0) {
                count_in_prufer[v2]--;
                count_in_prufer[v1]--;
                edges.emplace_back(v2 + offset, v1 + offset);
                break;
            }
        }
    }
    auto v1 = -1;
    auto v2 = -1;

    for (int i = 0; i < k; i++) {
        if (count_in_prufer[i] == 0) {
            if (v1 == -1)
                v1 = i;
            else {
                v2 = i;
                break;
            }
        }
    }

    edges.emplace_back(v2 + offset, v1 + offset);
    return edges;
}

auto constraint_type_str(SmartEntryConstraint c) -> string
{
    const vector<string> string_names = {"<", "<=", "==", "!=", ">", ">=", "in", "notin"};
    return string_names[static_cast<int>(c)];
}

auto test_smart_table(const int & n, mt19937 & rng, bool make_string_rep)
{
    stringstream string_rep;
    Problem p;
    uniform_int_distribution<> rand1_to_n(1, n);
    uniform_int_distribution<> randn2_to_n(n / 2, n);
    uniform_int_distribution<> rand0_to_5(0, 5);
    uniform_int_distribution<> rand0_to_7(0, 7);

    auto x = p.create_integer_variable_vector(n, -1_i, Integer{n}, "x");

    SmartTuples tuples;
    auto num_tup = randn2_to_n(rng);

    for (int idx = 0; idx < num_tup; ++idx) {

        vector<SmartEntry> tuple;
        auto copy_x = x;
        shuffle(begin(copy_x), end(copy_x), rng);

        auto num_vars_in_tuple = randn2_to_n(rng);
        uniform_int_distribution<> rand1_to_entries(1, num_vars_in_tuple);
        auto num_trees = rand1_to_entries(rng);
        vector<int> all_points;
        for (int i = 1; i < num_vars_in_tuple; i++) {
            all_points.emplace_back(i);
        }

        shuffle(begin(all_points), end(all_points), rng);
        vector<int> split_points{0};
        for (int i = 0; i < num_trees - 1; i++) {
            split_points.emplace_back(all_points[i]);
        }
        split_points.emplace_back(num_vars_in_tuple);
        sort(split_points.begin(), split_points.end());

        for (int i = 0; i < ssize(split_points) - 1; i++) {
            if (make_string_rep) string_rep << "Tree " << i << "(";
            auto num_nodes_in_tree = split_points[i + 1] - split_points[i];
            if (make_string_rep) string_rep << num_nodes_in_tree << " nodes): ";
            if (num_nodes_in_tree == 1) {
                // Create random unary Smart Entry
                auto constraint_type = static_cast<innards::SmartEntryConstraint>(rand0_to_7(rng));
                if (constraint_type == innards::SmartEntryConstraint::In || constraint_type == innards::SmartEntryConstraint::NotIn) {
                    vector<Integer> random_set{};
                    for (int val = -1; val <= n; val++) {
                        random_set.emplace_back(Integer{val});
                    }
                    shuffle(random_set.begin(), random_set.end(), rng);
                    int how_many = rand1_to_n(rng);
                    if (make_string_rep) {
                        string_rep << "x[" << index_of(copy_x[split_points[i]], x) << "] ";
                        string_rep << constraint_type_str(constraint_type);
                        string_rep << " {";
                        for (int j = 0; j < how_many - 1; j++) {
                            string_rep << random_set[j].raw_value << ", ";
                        }
                        string_rep << random_set[how_many - 1].raw_value << "};  ";
                    }
                    tuple.emplace_back(innards::UnarySetEntry{
                        copy_x[split_points[i]],
                        vector<Integer>(random_set.begin(), random_set.begin() + how_many),
                        constraint_type});
                }
                else {
                    int random_val = rand1_to_n(rng) - 1;
                    if (make_string_rep) {
                        string_rep << "x[" << index_of(copy_x[split_points[i]], x) << "] ";
                        string_rep << constraint_type_str(constraint_type);
                        string_rep << " " << random_val << ";  ";
                    }
                    tuple.emplace_back(innards::UnaryValueEntry{
                        copy_x[split_points[i]],
                        Integer{random_val},
                        constraint_type});
                }
            }
            else if (num_nodes_in_tree == 2) {
                auto constraint_type = static_cast<innards::SmartEntryConstraint>(rand0_to_5(rng));
                if (make_string_rep) {
                    string_rep << "x[" << index_of(copy_x[split_points[i]], x) << "] ";
                    string_rep << constraint_type_str(constraint_type);
                    string_rep << " x[" << index_of(copy_x[split_points[i] + 1], x) << "];  ";
                }
                tuple.emplace_back(innards::BinaryEntry{
                    copy_x[split_points[i]],
                    copy_x[split_points[i] + 1],
                    constraint_type});
            }
            else {
                auto tree_edges = random_tree_edges(num_nodes_in_tree, rng, split_points[i]);
                for (const auto & edge : tree_edges) {
                    // Create binary Smart Entry with specified variables
                    auto constraint_type = static_cast<innards::SmartEntryConstraint>(rand0_to_5(rng));
                    if (make_string_rep) {
                        string_rep << "x[" << index_of(copy_x[edge.first], x) << "] ";
                        string_rep << constraint_type_str(constraint_type);
                        string_rep << " x[" << index_of(copy_x[edge.second], x) << "];  ";
                    }
                    tuple.emplace_back(innards::BinaryEntry{
                        copy_x[edge.first],
                        copy_x[edge.second],
                        constraint_type});
                }
            }
        }

        auto num_extra_unary_entries = rand1_to_entries(rng);
        for (int i = 0; i < num_extra_unary_entries; i++) {
            auto var_idx = rand1_to_n(rng) - 1;
            auto constraint_type = static_cast<innards::SmartEntryConstraint>(rand0_to_7(rng));
            if (constraint_type == innards::SmartEntryConstraint::In || constraint_type == innards::SmartEntryConstraint::NotIn) {
                vector<Integer> random_set{};
                for (int val = -1; val <= n; val++) {
                    random_set.emplace_back(Integer{val});
                }
                shuffle(random_set.begin(), random_set.end(), rng);
                int how_many = rand1_to_n(rng);
                if (make_string_rep) {
                    string_rep << "x[" << index_of(copy_x[var_idx], x) << "] ";
                    string_rep << constraint_type_str(constraint_type);
                    string_rep << " {";
                    for (int j = 0; j < how_many - 1; j++) {
                        string_rep << random_set[j].raw_value << ", ";
                    }
                    string_rep << random_set[how_many - 1].raw_value << "};  ";
                }

                tuple.emplace_back(innards::UnarySetEntry{
                    copy_x[var_idx],
                    vector<Integer>(random_set.begin(), random_set.begin() + how_many),
                    constraint_type});
            }
            else {
                int random_val = rand1_to_n(rng) - 1;
                if (make_string_rep) {
                    string_rep << "x[" << index_of(copy_x[var_idx], x) << "] ";
                    string_rep << constraint_type_str(constraint_type);
                    string_rep << " " << random_val << ";  ";
                }
                tuple.emplace_back(innards::UnaryValueEntry{
                    copy_x[var_idx],
                    Integer{random_val},
                    constraint_type});
            }
        }

        tuples.emplace_back(tuple);
        if (make_string_rep) string_rep << "\n";
    }

    p.post(SmartTable{x, tuples});

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState &) -> bool {
                //                cout << "x = [ ";
                //                for (const auto & var : x) {
                //                    cout << s(var) << " ";
                //                }
                //                cout << "]" << endl;

                return true;
            }},
        ProofOptions{"random_table.opb", "random_table.pbp"});

    if (0 != system("veripb random_table.opb random_table.pbp")) {
        cout << stats;
        cout << "Num solutions: " << stats.solutions << endl;
        if (make_string_rep) cout << string_rep.str() << endl;
        return false;
    }

    return true;
}
auto main(int argc, char * argv[]) -> int
{
    random_device rand_dev;
    auto seed = rand_dev();
    bool use_string_rep = false;
    if (argc >= 2)
        seed = stoll(argv[1]);
    if (argc >= 3)
        use_string_rep = true;

    std::mt19937 rng(seed);
    cout << "Seed for random smart tables: " << seed << endl;
    //    mt19937 rng(0); // Switch to this to have it the same every time.

    for (int n = 3; n < 6; n++) {
        for (int r = 0; r < 20 / n; r++) {
            if (! test_smart_table(n, rng, use_string_rep)) {
                return EXIT_FAILURE;
            }
        }
    }

    return EXIT_SUCCESS;
}
