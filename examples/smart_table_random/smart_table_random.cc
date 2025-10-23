#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cxxopts.hpp>

#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>

using namespace gcs;

using std::cerr;
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

auto constraint_type_str(SmartEntryConstraint c) -> string
{
    const vector<string> string_names = {"<", "<=", "==", "!=", ">", ">=", "in", "notin"};
    return string_names[static_cast<int>(c)];
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

auto random_tuples(int tuple_length, vector<IntegerVariableID> & vars, mt19937 & rng, bool display_table, stringstream & table_as_string) -> SmartTuples
{
    SmartTuples tuples{};

    auto number_of_vars = vars.size();
    for (int tuple_idx = 0; tuple_idx < tuple_length; ++tuple_idx) {

        vector<SmartEntry> tuple;
        vector<IntegerVariableID> shuffled_vars = vars;
        shuffle(shuffled_vars.begin(), shuffled_vars.end(), rng);

        auto num_vars_in_tuple = uniform_int_distribution<>(number_of_vars / 2, number_of_vars)(rng);
        auto num_trees = uniform_int_distribution<>(1, num_vars_in_tuple)(rng);

        vector<int> all_tuple_indices;
        for (int i = 1; i < num_vars_in_tuple; i++) {
            all_tuple_indices.emplace_back(i);
        }
        shuffle(begin(all_tuple_indices), end(all_tuple_indices), rng);

        vector<int> partition_indices{0};
        for (int i = 0; i < num_trees - 1; i++) {
            partition_indices.emplace_back(all_tuple_indices[i]);
        }
        partition_indices.emplace_back(num_vars_in_tuple);
        sort(partition_indices.begin(), partition_indices.end());

        for (size_t i = 0; i < partition_indices.size() - 1; i++) {
            if (display_table) table_as_string << "Tree " << i << "(";
            auto num_nodes_in_tree = partition_indices[i + 1] - partition_indices[i];
            if (display_table) table_as_string << num_nodes_in_tree << " nodes): ";

            if (num_nodes_in_tree == 1) {
                // Create random unary Smart Entry
                auto constraint_type = static_cast<innards::SmartEntryConstraint>(uniform_int_distribution<>(0, 7)(rng));

                if (constraint_type == innards::SmartEntryConstraint::In || constraint_type == innards::SmartEntryConstraint::NotIn) {
                    vector<Integer> random_set{};
                    for (int val = -1; std::cmp_less_equal(val, number_of_vars); val++) {
                        random_set.emplace_back(Integer(val));
                    }
                    shuffle(random_set.begin(), random_set.end(), rng);
                    int how_many = uniform_int_distribution<>(1, number_of_vars - 1)(rng);
                    if (display_table) {
                        table_as_string << "vars[" << index_of(shuffled_vars[partition_indices[i]], vars) << "] ";
                        table_as_string << constraint_type_str(constraint_type);
                        table_as_string << " {";
                        for (int j = 0; j < how_many - 1; j++) {
                            table_as_string << random_set[j].raw_value << ", ";
                        }
                        table_as_string << random_set[how_many - 1].raw_value << "};  ";
                    }
                    tuple.emplace_back(innards::UnarySetEntry{
                        shuffled_vars[partition_indices[i]],
                        vector<Integer>(random_set.begin(), random_set.begin() + how_many),
                        constraint_type});
                }
                else {
                    int random_val = uniform_int_distribution<>(1, number_of_vars)(rng) - 1;
                    if (display_table) {
                        table_as_string << "vars[" << index_of(shuffled_vars[partition_indices[i]], vars) << "] ";
                        table_as_string << constraint_type_str(constraint_type);
                        table_as_string << " " << random_val << ";  ";
                    }
                    tuple.emplace_back(innards::UnaryValueEntry{
                        shuffled_vars[partition_indices[i]],
                        Integer(random_val),
                        constraint_type});
                }
            }
            else if (num_nodes_in_tree == 2) {
                auto constraint_type = static_cast<innards::SmartEntryConstraint>(uniform_int_distribution<>(0, 5)(rng));
                if (display_table) {
                    table_as_string << "vars[" << index_of(shuffled_vars[partition_indices[i]], vars) << "] ";
                    table_as_string << constraint_type_str(constraint_type);
                    table_as_string << " vars[" << index_of(shuffled_vars[partition_indices[i] + 1], vars) << "];  ";
                }
                tuple.emplace_back(innards::BinaryEntry{
                    shuffled_vars[partition_indices[i]],
                    shuffled_vars[partition_indices[i] + 1],
                    constraint_type});
            }
            else {
                auto tree_edges = random_tree_edges(num_nodes_in_tree, rng, partition_indices[i]);
                for (const auto & edge : tree_edges) {
                    // Create binary Smart Entry with specified variables
                    auto constraint_type = static_cast<innards::SmartEntryConstraint>(uniform_int_distribution<>(0, 5)(rng));
                    if (display_table) {
                        table_as_string << "vars[" << index_of(shuffled_vars[edge.first], vars) << "] ";
                        table_as_string << constraint_type_str(constraint_type);
                        table_as_string << " vars[" << index_of(shuffled_vars[edge.second], vars) << "];  ";
                    }
                    tuple.emplace_back(innards::BinaryEntry{
                        shuffled_vars[edge.first],
                        shuffled_vars[edge.second],
                        constraint_type});
                }
            }
        }

        auto num_extra_unary_entries = uniform_int_distribution<>(1, tuple_length)(rng);
        for (int i = 0; i < num_extra_unary_entries; i++) {
            auto var_idx = uniform_int_distribution<>(1, number_of_vars)(rng) - 1;
            auto constraint_type = static_cast<innards::SmartEntryConstraint>(uniform_int_distribution<>(0, 7)(rng));
            if (constraint_type == innards::SmartEntryConstraint::In || constraint_type == innards::SmartEntryConstraint::NotIn) {
                vector<Integer> random_set{};
                for (auto val = -1; std::cmp_less_equal(val, number_of_vars); val++) {
                    random_set.emplace_back(Integer(val));
                }
                shuffle(random_set.begin(), random_set.end(), rng);
                int how_many = uniform_int_distribution<>(1, number_of_vars)(rng);
                if (display_table) {
                    table_as_string << "vars[" << index_of(shuffled_vars[var_idx], vars) << "] ";
                    table_as_string << constraint_type_str(constraint_type);
                    table_as_string << " {";
                    for (int j = 0; j < how_many - 1; j++) {
                        table_as_string << random_set[j].raw_value << ", ";
                    }
                    table_as_string << random_set[how_many - 1].raw_value << "};  ";
                }

                tuple.emplace_back(innards::UnarySetEntry{
                    shuffled_vars[var_idx],
                    vector<Integer>(random_set.begin(), random_set.begin() + how_many),
                    constraint_type});
            }
            else {
                int random_val = uniform_int_distribution<>(1, number_of_vars)(rng) - 1;
                if (display_table) {
                    table_as_string << "vars[" << index_of(shuffled_vars[var_idx], vars) << "] ";
                    table_as_string << constraint_type_str(constraint_type);
                    table_as_string << " " << random_val << ";  ";
                }
                tuple.emplace_back(innards::UnaryValueEntry{
                    shuffled_vars[var_idx],
                    Integer(random_val),
                    constraint_type});
            }
        }

        tuples.emplace_back(tuple);
        if (display_table) table_as_string << "\n";
    }
    return tuples;
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Random Smart Table Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")                                                                           //
            ("help", "Display help information")                                                                         //
            ("prove", "Create a proof")                                                                                  //
            ("seed", "Seed for random table generator (-1 for random seed)", cxxopts::value<int>()->default_value("-1")) //
            ("display", "Display a formatted representation of the table for each instance")                             //
            ("n", "Number of variables", cxxopts::value<int>()->default_value("6"));

        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        cout << "Usage: " << argv[0] << " [options] [size]" << endl;
        cout << endl;
        cout << options.help() << endl;
        return EXIT_SUCCESS;
    }

    auto n = options_vars["n"].as<int>();
    auto seed = options_vars["seed"].as<int>();

    if (seed == -1) {
        random_device rand_dev;
        seed = rand_dev();
    }

    std::mt19937 rng(seed);

    bool display_table = false;

    if (options_vars.contains("display"))
        display_table = true;

    // cout << "Seed for random smart tables: " << seed << endl;
    auto prove = options_vars.contains("prove");

    stringstream table_as_string;
    Problem p;
    auto vars = p.create_integer_variable_vector(n, -1_i, Integer(n), "vars");
    auto tuple_length = uniform_int_distribution<>(n / 2, n)(rng);
    SmartTuples tuples = random_tuples(tuple_length, vars, rng, display_table, table_as_string);

    p.post(SmartTable{vars, tuples});

    solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState &) -> bool {
                //                cout << "vars = [ ";
                //                for (const auto & var : vars) {
                //                    cout << s(var) << " ";
                //                }
                //                cout << "]" << endl;

                return false;
            }},
        prove ? make_optional(ProofOptions{"smart_table_random"}) : nullopt);

    if (display_table) cout << table_as_string.str() << endl;

    return EXIT_SUCCESS;
}
