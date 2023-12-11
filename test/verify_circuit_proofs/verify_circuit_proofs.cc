#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <array>
#include <boost/program_options.hpp>
#include <cstdio>
#include <fstream>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/in.hh>
#include <iostream>
#include <memory>
#include <random>
#include <stdexcept>
#include <string>

using namespace gcs;
using std::cerr;
using std::cmp_less;
using std::cout;
using std::endl;
using std::make_optional;
using std::make_pair;
using std::make_tuple;
using std::mt19937;
using std::nullopt;
using std::ofstream;
using std::pair;
using std::random_device;
using std::string;
using std::to_string;
using std::tuple;
using std::uniform_real_distribution;
using std::vector;
using std::chrono::duration_cast;
using std::chrono::microseconds;
using std::chrono::steady_clock;
namespace po = boost::program_options;

auto main(int argc, char * argv[]) -> int
{
    ofstream outputFile("verification_times.csv");
    outputFile.close();
    for (int n = 28; n < 40; n++) {
        for (int r = 0; r < 5; r++) {
            string name = "circui_experiment_" + to_string(n) + "_" + to_string(r);
            ofstream outputFile("verification_times.csv", std::ios::app);
            if (outputFile.is_open()) {
                auto verify_start_time = steady_clock::now();
                const auto command = "gtimeout 300 veripb " + name + ".opb " + name + ".veripb";
                if (0 != system(command.c_str())) {
                    cout << "n: " << n << endl;
                    throw new UnexpectedException{"Verification failed!"};
                }
                auto verification_time = duration_cast<microseconds>(steady_clock::now() - verify_start_time);
                cout << verification_time.count() << endl;
                outputFile << verification_time.count() << "\n";
                outputFile.close();
            }
            else {
                cerr << "Unable to open the file." << std::endl;
            }
        }
    }
}
