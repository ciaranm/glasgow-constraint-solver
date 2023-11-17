#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>

#include <boost/program_options.hpp>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/constraints/in.hh>

using namespace gcs;

using std::cerr;
using std::cmp_less;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

namespace po = boost::program_options;

auto post_constraints(Problem & p, vector<IntegerVariableID> & nodes)
{
    vector<vector<int>> domains =
        {
            {1, 4, 5, 6},
            {0, 2, 3},
            {0, 1},
            {1, 2},
            {0, 1, 3},
            {0, 6},
            {0, 3, 5},
            {6, 5, 0, 1}};

    for (int i = 0; cmp_less(i, domains.size()); i++) {
        vector<Integer> int_domain{};
        for (const auto & val : domains[i]) {
            int_domain.emplace_back(val);
        }
        p.post((In{nodes[i], int_domain}));
    }
}

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");         //

    po::options_description all_options{"All options"};

    //    all_options.add_options()(
    //        "n", po::value<int>()->default_value(3), "Integer value n.") //
    //        ;
    all_options.add(display_options);
    po::variables_map options_vars;

    try {
        po::store(po::command_line_parser(argc, argv)
                      .options(all_options)
                      .run(),
            options_vars);
        po::notify(options_vars);
    }
    catch (const po::error & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        cout << "Usage: " << argv[0] << " [options] [size]" << endl;
        cout << endl;
        cout << display_options << endl;
        return EXIT_SUCCESS;
    }

    //    auto n = options_vars["n"].as<int>();

    Problem p;
    auto nodes = p.create_integer_variable_vector(8, 0_i, 7_i);

    post_constraints(p, nodes);

    SCCOptions scc_options;
    scc_options.fix_req = true;
    scc_options.prune_root = false;
    scc_options.prune_within = false;
    scc_options.prune_skip = false;
    p.post(CircuitSCC{nodes, false, scc_options});

    auto stats = solve_with(
        p,
        SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
            for (const auto & v : nodes) {
                cout << s(v) << " ";
            }
            cout << endl;
            cout << 0 << " -> " << s(nodes[0]);
            auto current = s(nodes[0]);
            while (current != 0_i) {
                cout << " -> ";
                cout << s(nodes[current.raw_value]);
                current = s(nodes[current.raw_value]);
            }
            cout << "\n\n";
            return true;
        }},
        make_optional<ProofOptions>("scc_no_backedges.opb", "scc_no_backedges.veripb"));

    // system("veripb --trace --useColor scc_no_backedges.opb scc_no_backedges.veripb");

    cout << stats;

    return EXIT_SUCCESS;
}
