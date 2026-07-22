#include <gcs/constraints/equals.hh>
#include <gcs/constraints/multiply.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <iostream>
#include <optional>
#include <random>
#include <string>
#include <vector>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

#include <cxxopts.hpp>

using namespace gcs;

using std::bernoulli_distribution;
using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::max;
using std::mt19937;
using std::nullopt;
using std::string;
using std::uniform_int_distribution;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
#endif

/**
 * \brief The largest instance we accept.
 *
 * The product has a + b digits, and both the digit-sum constraints and the
 * instance generator work in long long, so 10 ^ (a + b) must be representable.
 */
constexpr int max_total_digits = 18;

/**
 * \brief What the skeleton tells us about one digit position.
 *
 * A skeleton puzzle reveals every occurrence of one particular digit (the
 * "known digit"), so ordinarily each position is either known to be that digit
 * or known not to be. The --reveal option additionally allows a position to be
 * left unrevealed, which loosens the model and grows the search tree.
 */
enum class DigitClue
{
    IsKnown,
    IsNotKnown,
    Unrevealed
};

/**
 * \brief What a skeleton instance says about each digit position.
 *
 * partial_product_clues[i] holds a + 1 entries for the i'th partial product
 * row, and product_clues holds a + b entries. Both are written most significant
 * digit first, matching the layout the solution callback prints.
 */
struct Instance
{
    vector<vector<DigitClue>> partial_product_clues;
    vector<DigitClue> product_clues;
};

auto power_of_ten(int n) -> long long
{
    long long result = 1;
    for (int i = 0; i < n; i++)
        result *= 10;
    return result;
}

/**
 * \brief The 7 x 5 instance this example has always shipped with, whose unique
 * solution is 9175144 x 72461 = 664840109384.
 */
auto default_instance() -> Instance
{
    // 1 where the digit is the known digit (zero), 0 where it is not. Most
    // significant digit first, the last row being the product.
    const vector<vector<bool>> is_known = {
        {1, 0, 0, 0, 0, 0, 0, 0},            //
        {0, 0, 1, 0, 1, 0, 0, 0},            //
        {0, 0, 0, 1, 1, 0, 0, 0},            //
        {0, 0, 0, 0, 1, 0, 0, 0},            //
        {0, 0, 0, 0, 0, 1, 1, 0},            //
        {0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0} //
    };

    auto clues_of = [](const vector<bool> & row) {
        vector<DigitClue> clues;
        for (bool known : row)
            clues.push_back(known ? DigitClue::IsKnown : DigitClue::IsNotKnown);
        return clues;
    };

    Instance instance{};
    for (unsigned int i = 0; i + 1 < is_known.size(); i++)
        instance.partial_product_clues.push_back(clues_of(is_known[i]));
    instance.product_clues = clues_of(is_known.back());
    return instance;
}

/**
 * \brief Generate a random instance of the requested shape.
 *
 * The instance is satisfiable by construction. We pick a multiplicand and a
 * multiplier at random, drawing every digit from exactly the set the model
 * allows for a_digits and b_digits (anything but the known digit), and
 * additionally refusing a zero in the leading position so that the instance
 * really is an a by b digit multiplication. We then compute the partial
 * products and the product with exact integer arithmetic, and read the clues
 * off the digits that actually came out. The numbers we started from therefore
 * satisfy every constraint the model posts, so at least one solution exists.
 *
 * The widths the model assumes hold for every input we accept: a partial
 * product is at most 9 * (10 ^ a - 1) < 10 ^ (a + 1), so it always fits in the
 * a + 1 digits it is given, and the product is less than 10 ^ a * 10 ^ b, so it
 * always fits in a + b digits. Both may need leading zeros, which is why the
 * generator writes each number out at a fixed width rather than dropping them.
 */
auto generate_instance(int a, int b, int known_digit, mt19937 & rng) -> Instance
{
    uniform_int_distribution<int> digit_dist{0, 9};
    auto random_digit = [&](bool leading) {
        for (;;) {
            auto digit = digit_dist(rng);
            if (digit != known_digit && ! (leading && 0 == digit))
                return digit;
        }
    };

    auto random_number = [&](int digits) {
        long long value = 0;
        for (int i = 0; i < digits; i++)
            value += power_of_ten(i) * random_digit(i + 1 == digits);
        return value;
    };

    auto clues_of = [&](long long value, int width) {
        vector<DigitClue> clues;
        for (int i = width - 1; i > -1; i--)
            clues.push_back((value / power_of_ten(i)) % 10 == known_digit ? DigitClue::IsKnown : DigitClue::IsNotKnown);
        return clues;
    };

    auto multiplicand = random_number(a), multiplier = random_number(b);

    Instance instance{};
    for (int i = 0; i < b; i++)
        instance.partial_product_clues.push_back(clues_of(multiplicand * ((multiplier / power_of_ten(i)) % 10), a + 1));
    instance.product_clues = clues_of(multiplicand * multiplier, a + b);
    return instance;
}

/**
 * \brief Independently unreveal each clue with probability 1 - reveal.
 *
 * Removing a clue only ever removes constraints, so this cannot make a
 * satisfiable instance unsatisfiable. It does make the puzzle less constrained
 * and typically much harder, which is the point: it grows the search tree
 * without growing the model.
 */
auto unreveal_clues(Instance & instance, double reveal, mt19937 & rng) -> void
{
    bernoulli_distribution reveal_dist{reveal};
    auto maybe_unreveal = [&](DigitClue & clue) {
        if (! reveal_dist(rng))
            clue = DigitClue::Unrevealed;
    };

    for (auto & row : instance.partial_product_clues)
        for (auto & clue : row)
            maybe_unreveal(clue);
    for (auto & clue : instance.product_clues)
        maybe_unreveal(clue);
}

auto constrain_digit_sum(Problem & p, vector<SimpleIntegerVariableID> digits, SimpleIntegerVariableID number) -> void
{
    WeightedSum wsum{};
    for (unsigned int i = 0; i < digits.size(); i++) {
        wsum += Integer{power_of_ten(static_cast<int>(i))} * digits[i];
    }
    wsum += -1_i * number;
    p.post(wsum == 0_i);
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Skeleton_puzzle Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options()                                                              //
            ("help", "Display help information")                                           //
            ("multiplicand-digits", "Number of digits in the multiplicand",                //
                cxxopts::value<int>()->default_value("7"))                                 //
            ("multiplier-digits", "Number of digits in the multiplier",                    //
                cxxopts::value<int>()->default_value("5"))                                 //
            ("known-digit", "The digit whose every occurrence the skeleton reveals",       //
                cxxopts::value<int>()->default_value("0"))                                 //
            ("seed", "Generate a random instance of the requested shape, using this seed", //
                cxxopts::value<int>()->default_value("0"))                                 //
            ("reveal", "Reveal only this fraction of the digit positions",                 //
                cxxopts::value<double>()->default_value("1.0"))                            //
            ("cap", "Stop after this many solutions, 0 for no limit",                      //
                cxxopts::value<long long>()->default_value("0"))                           //
            ("quiet", "Do not print the solutions")                                        //
            ("prove", "Create a proof")                                                    //
            ("proof-files-basename", "Basename for the .opb and .pbp files",               //
                cxxopts::value<string>()->default_value("skeleton_puzzle"))                //
            ("stats", "Print solve statistics")                                            //
            ;

        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        cout << "Usage: " << argv[0] << " [options]" << endl;
        cout << endl;
        cout << options.help() << endl;
        return EXIT_SUCCESS;
    }

    int a = options_vars["multiplicand-digits"].as<int>();
    int b = options_vars["multiplier-digits"].as<int>();
    int known_digit = options_vars["known-digit"].as<int>();
    auto reveal = options_vars["reveal"].as<double>();

    if (a < 1 || b < 1) {
        cerr << "Error: the multiplicand and the multiplier must each have at least one digit" << endl;
        return EXIT_FAILURE;
    }

    if (a + b > max_total_digits) {
        cerr << "Error: the multiplicand and the multiplier may have at most " << max_total_digits << " digits between them" << endl;
        return EXIT_FAILURE;
    }

    if (known_digit < 0 || known_digit > 9) {
        cerr << "Error: the known digit must be between 0 and 9" << endl;
        return EXIT_FAILURE;
    }

    if (reveal < 0.0 || reveal > 1.0) {
        cerr << "Error: the revealed fraction must be between 0 and 1" << endl;
        return EXIT_FAILURE;
    }

    mt19937 rng(static_cast<mt19937::result_type>(options_vars["seed"].as<int>()));

    Instance instance;
    if (options_vars.contains("seed"))
        instance = generate_instance(a, b, known_digit, rng);
    else if (7 == a && 5 == b && 0 == known_digit)
        instance = default_instance();
    else {
        cerr << "Error: the built-in instance is a 7 by 5 multiplication with known digit 0; use --seed "
                "to generate an instance of a different shape"
             << endl;
        return EXIT_FAILURE;
    }

    if (reveal < 1.0)
        unreveal_clues(instance, reveal, rng);

    Problem p;
    IntegerVariableID k_var = constant_variable(Integer{known_digit});

    auto post_clue = [&](SimpleIntegerVariableID digit, DigitClue clue) {
        switch (clue) {
            using enum DigitClue;
        case IsKnown: p.post(Equals(digit, k_var)); break;
        case IsNotKnown: p.post(NotEquals(digit, k_var)); break;
        case Unrevealed: break;
        }
    };

    vector<SimpleIntegerVariableID> a_digits{};
    for (int i = 0; i < a; i++) {
        a_digits.emplace_back(p.create_integer_variable(0_i, 9_i));
        p.post(NotEquals(a_digits[i], k_var));
    }

    SimpleIntegerVariableID a_var = p.create_integer_variable(0_i, Integer{power_of_ten(a)});
    constrain_digit_sum(p, a_digits, a_var);

    vector<SimpleIntegerVariableID> b_digits{};
    for (int i = 0; i < b; i++) {
        b_digits.emplace_back(p.create_integer_variable(0_i, 9_i));
        p.post(NotEquals(b_digits[i], k_var));
    }

    vector<vector<SimpleIntegerVariableID>> partial_product_digits{};
    vector<SimpleIntegerVariableID> partial_product{};
    for (int i = 0; i < b; i++) {
        partial_product_digits.emplace_back();
        partial_product.emplace_back(p.create_integer_variable(0_i, Integer{power_of_ten(a + 1)}));
        for (int j = 0; j < a + 1; j++) {
            partial_product_digits[i].emplace_back(p.create_integer_variable(0_i, 9_i));
            post_clue(partial_product_digits[i][j], instance.partial_product_clues[i][a - j]);
        }
        constrain_digit_sum(p, partial_product_digits[i], partial_product[i]);
        p.post(Multiply{a_var, b_digits[i], partial_product[i]});
    }

    vector<SimpleIntegerVariableID> c_digits{};
    auto c_var = p.create_integer_variable(0_i, Integer{power_of_ten(a + b)});
    for (int i = 0; i < a + b; i++) {
        c_digits.emplace_back(p.create_integer_variable(0_i, 9_i));
        post_clue(c_digits[i], instance.product_clues[a + b - 1 - i]);
    }
    cout << endl;

    constrain_digit_sum(p, c_digits, c_var);
    constrain_digit_sum(p, partial_product, c_var);

    // Everything is printed right aligned in this many columns. The product is
    // a + b digits wide, but for a one digit multiplicand the "x " prefix on
    // the multiplier line is what needs the most room.
    int width = max(a + b, b + 2);

    auto quiet = options_vars.contains("quiet");
    auto cap = options_vars["cap"].as<long long>();
    long long solutions_found = 0;

    auto print_solution = [&](const CurrentState & s) {
        auto spaces = [&](int n) {
            for (int i = 0; i < n; i++)
                cout << " ";
        };
        spaces(width - a);
        for (int i = a - 1; i > -1; i--)
            cout << s(a_digits[i]);
        cout << endl;
        spaces(width - b - 2);
        cout << "x ";
        for (int i = b - 1; i > -1; i--)
            cout << s(b_digits[i]);
        cout << endl;
        for (int i = 0; i < width; i++)
            cout << "-";
        cout << endl;
        for (int i = 0; i < b; i++) {
            // Row i is the multiplicand times the i'th digit of the multiplier,
            // shifted left by i, so it ends i columns short of the right margin.
            spaces(width - (a + 1) - i);
            for (int j = a; j > -1; j--)
                cout << s(partial_product_digits[i][j]);
            cout << endl;
        }
        for (int i = 0; i < width; i++)
            cout << "-";
        cout << endl;
        spaces(width - (a + b));
        for (int i = a + b - 1; i > -1; i--)
            cout << s(c_digits[i]);
        cout << endl << endl;
    };

    auto solution_callback = [&](const CurrentState & s) -> bool {
        if (! quiet)
            print_solution(s);

        // This example has always enumerated every solution, and still does by
        // default. Capping the count is how a benchmark-sized search tree is
        // obtained: a skeleton puzzle small enough to be quick is also loosely
        // enough constrained to have a great many solutions, so shrinking the
        // instance on its own does not shrink the search.
        ++solutions_found;
        return 0 == cap || solutions_found < cap;
    };
    auto stats = solve_with(p, SolveCallbacks{.solution = solution_callback},
        options_vars.contains("prove") ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>()) : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
