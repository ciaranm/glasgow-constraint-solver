#include <gcs/gcs.hh>
#include <gcs/innards/state.hh>
#include <util/enumerate.hh>

#include <XCSP3CoreParser.h>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <csignal>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

#include <boost/program_options.hpp>

using XCSP3Core::ExpressionObjective;
using XCSP3Core::OperandType;
using XCSP3Core::OrderType;
using XCSP3Core::RankType;
using XCSP3Core::XCondition;
using XCSP3Core::XCSP3CoreCallbacks;
using XCSP3Core::XCSP3CoreParser;
using XCSP3Core::XVariable;

using namespace gcs;

using std::atomic;
using std::cerr;
using std::condition_variable;
using std::cout;
using std::cv_status;
using std::endl;
using std::flush;
using std::get;
using std::make_shared;
using std::map;
using std::max;
using std::min;
using std::minmax_element;
using std::mutex;
using std::nullopt;
using std::optional;
using std::signal;
using std::stoll;
using std::string;
using std::thread;
using std::tuple;
using std::unique_lock;
using std::unique_ptr;
using std::vector;

using std::chrono::duration_cast;
using std::chrono::microseconds;
using std::chrono::seconds;
using std::chrono::steady_clock;
using std::chrono::system_clock;

using namespace std::literals::string_literals;

namespace po = boost::program_options;

namespace
{
    static atomic<bool> abort_flag{false}, was_terminated{false};

    auto sig_int_or_term_handler(int) -> void
    {
        abort_flag.store(true);
        was_terminated.store(true);
    }
}

using VarInfo = tuple<optional<IntegerVariableID>, Integer, Integer, optional<vector<int>>>;
using VariableMapping = map<string, VarInfo>;

auto need_variable(Problem & problem, VarInfo & t, const string & s) -> void
{
    if (! get<0>(t)) {
        if (get<3>(t)) {
            vector<Integer> vals;
            for (auto & v : *get<3>(t))
                vals.emplace_back(Integer{v});
            get<0>(t) = problem.create_integer_variable(vals, s);
        }
        else
            get<0>(t) = problem.create_integer_variable(get<1>(t), get<2>(t), s);
    }
}

auto disintentionify_to_intvar(const string & s, string::size_type & pos, Problem & problem,
    VariableMapping & mapping) -> VarInfo
{
    auto epos = s.find_first_of(",()", pos);
    if (string::npos == epos)
        throw UnimplementedException{"parse error"};
    auto tok = s.substr(pos, epos - pos);
    pos = epos;

    if (s.at(epos) == '(') {
        if (tok == "dist" || tok == "eq" || tok == "ne" || tok == "add" || tok == "sub" || tok == "mul" || tok == "mod" || tok == "div") {
            ++pos;
            auto [v1, lower1, upper1, _1] = disintentionify_to_intvar(s, pos, problem, mapping);
            if (s.at(pos) != ',')
                throw UnimplementedException{"parse error"};
            ++pos;
            auto [v2, lower2, upper2, _2] = disintentionify_to_intvar(s, pos, problem, mapping);
            if (s.at(pos) != ')')
                throw UnimplementedException{"parse error"};
            ++pos;

            if (tok == "dist") {
                auto bound = Integer{max(upper1.raw_value, upper2.raw_value) - min(lower1.raw_value, lower2.raw_value) + 1};
                auto r = problem.create_integer_variable(0_i, bound, "distresult");
                auto d = problem.create_integer_variable(-bound, bound, "dist");
                problem.post(LinearEquality{Linear{{1_i, *v1}, {-1_i, *v2}, {-1_i, d}}, 0_i});
                problem.post(Abs{d, r});
                return tuple{r, 0_i, bound, nullopt};
            }
            else if (tok == "add") {
                if (lower2 == upper2) {
                    auto r = *v1 + Integer{lower2};
                    return tuple{r, lower1 + lower2, upper1 + upper2, nullopt};
                }
                else {
                    auto lower_bound = Integer{lower1 + lower2};
                    auto upper_bound = Integer{upper1 + upper2};
                    auto r = problem.create_integer_variable(lower_bound, upper_bound, "addresult");
                    problem.post(LinearEquality{Linear{{1_i, *v1}, {1_i, *v2}, {-1_i, r}}, 0_i});
                    return tuple{r, lower_bound, upper_bound, nullopt};
                }
            }
            else if (tok == "sub") {
                if (lower2 == upper2) {
                    auto r = *v1 - Integer{lower2};
                    return tuple{r, lower1 - lower2, upper1 - upper2, nullopt};
                }
                else {
                    auto lower_bound = min({lower1 - lower2, lower1 - upper2, upper1 - lower2, upper2 - upper2});
                    auto upper_bound = max({lower1 - lower2, lower1 - upper2, upper1 - lower2, upper2 - upper2});
                    auto r = problem.create_integer_variable(lower_bound, upper_bound, "subresult");
                    problem.post(LinearEquality{Linear{{1_i, *v1}, {-1_i, *v2}, {-1_i, r}}, 0_i});
                    return tuple{r, lower_bound, upper_bound, nullopt};
                }
            }
            else if (tok == "mul") {
                auto lower_bound = min({lower1 * lower2, lower1 * upper2, upper1 * lower2, upper2 * upper2});
                auto upper_bound = max({lower1 * lower2, lower1 * upper2, upper1 * lower2, upper2 * upper2});
                auto r = problem.create_integer_variable(lower_bound, upper_bound, "mulresult");
                if (lower2 == upper2)
                    problem.post(LinearEquality{Linear{{lower2, *v1}, {-1_i, r}}, 0_i, false});
                else
                    problem.post(Times{*v1, *v2, r});
                return tuple{r, lower_bound, upper_bound, nullopt};
            }
            else if (tok == "mod") {
                auto bound = max(abs(lower2), abs(upper2));
                auto r = problem.create_integer_variable(-bound, bound, "modresult");
                problem.post(Mod{*v1, *v2, r});
                return tuple{r, -bound, bound, nullopt};
            }
            else if (tok == "div") {
                auto bound = max(abs(lower1), abs(upper1));
                auto r = problem.create_integer_variable(-bound, bound, "modresult");
                problem.post(Div{*v1, *v2, r});
                return tuple{r, -bound, bound, nullopt};
            }
            else if (tok == "eq") {
                auto control = problem.create_integer_variable(0_i, 1_i, "eqresult");
                problem.post(EqualsIff{*v1, *v2, control == 1_i});
                return tuple{control, 0_i, 1_i, nullopt};
            }
            else if (tok == "ne") {
                auto control = problem.create_integer_variable(0_i, 1_i, "neresult");
                problem.post(EqualsIff{*v1, *v2, control == 0_i});
                return tuple{control, 0_i, 1_i, nullopt};
            }
            else
                throw NonExhaustiveSwitch{};
        }
        else if (tok == "or" || tok == "and") {
            ++pos;
            vector<IntegerVariableID> vars;
            while (true) {
                vars.emplace_back(*get<0>(disintentionify_to_intvar(s, pos, problem, mapping)));
                if (pos >= s.size())
                    throw UnimplementedException{"parse error"};
                else if (s.at(pos) == ')') {
                    ++pos;
                    break;
                }
                else if (s.at(pos) == ',')
                    ++pos;
                else {
                    throw UnimplementedException{"parse error"};
                }
            }
            auto control = problem.create_integer_variable(0_i, 1_i, tok + "result");
            if (tok == "or")
                problem.post(Or{vars, control});
            else
                problem.post(And{vars, control});
            return tuple{control, 0_i, 1_i, nullopt};
        }
        else {
            throw UnimplementedException{"unknown token '" + tok + "'"};
        }
    }
    else {
        if (string::npos == tok.find_first_not_of("0123456789") ||
            (tok.starts_with("-") && string::npos == tok.find_first_not_of("0123456789", 1))) {
            Integer val{stoll(tok)};
            return tuple{constant_variable(val), val, val, nullopt};
        }

        auto m = mapping.find(tok);
        if (m == mapping.end())
            throw UnimplementedException{"no mapping for '" + tok + "'"};
        need_variable(problem, m->second, tok);

        return m->second;
    }
}

auto disintentionify_to_set_of_ints(const string & s, string::size_type & pos, Problem &,
    VariableMapping &) -> set<long long>
{
    auto epos = s.find_first_of(",()", pos);
    if (string::npos == epos)
        throw UnimplementedException{"parse error"};
    auto tok = s.substr(pos, epos - pos);
    pos = epos;

    if (s.at(epos) != '(' || tok != "set")
        throw UnimplementedException{"tok is '" + tok + "'"};
    ++pos;

    set<long long> result;
    while (true) {
        auto epos = s.find_first_of(",)", pos);
        if (string::npos == epos)
            throw UnimplementedException{"parse error"};
        auto tok = s.substr(pos, epos - pos);
        if (tok.empty() || string::npos != tok.find_first_not_of("0123456789"))
            throw UnimplementedException{"tok is '" + tok + "'"};
        result.insert(stoll(tok));
        pos = epos + 1;
        if (s.at(epos) == ')')
            break;
    }
    return result;
}

auto disintentionify(const string & s, Problem & problem, VariableMapping & mapping) -> void
{
    if (s.empty())
        return;

    auto pos = s.find('(');
    if (string::npos == pos)
        throw UnimplementedException{"parse error"};

    auto op = s.substr(0, pos);
    if (op == "eq" || op == "or" || op == "le" || op == "lt" || op == "ne" || op == "gt" || op == "ge") {
        ++pos;
        vector<IntegerVariableID> vars;
        while (true) {
            vars.emplace_back(*get<0>(disintentionify_to_intvar(s, pos, problem, mapping)));
            if (pos >= s.size())
                throw UnimplementedException{"parse error"};
            else if (s.at(pos) == ')') {
                ++pos;
                break;
            }
            else if (s.at(pos) == ',')
                ++pos;
            else {
                throw UnimplementedException{"parse error"};
            }
        }

        if (op == "eq") {
            if (vars.size() < 2)
                throw UnimplementedException{"too few values for eq"};
            for (auto i_end = vars.size(), i = 1ul; i != i_end; ++i)
                problem.post(Equals{vars.at(0), vars.at(i)});
        }
        else if (op == "or") {
            problem.post(Or{vars});
        }
        else if (op == "le") {
            if (vars.size() != 2)
                throw UnimplementedException{"didn't get exactly two values for le"};
            problem.post(LessThanEqual{vars.at(0), vars.at(1)});
        }
        else if (op == "ne") {
            if (vars.size() != 2)
                throw UnimplementedException{"didn't get exactly two values for ne"};
            problem.post(NotEquals{vars.at(0), vars.at(1)});
        }
        else if (op == "lt") {
            if (vars.size() != 2)
                throw UnimplementedException{"didn't get exactly two values for lt"};
            problem.post(LessThan{vars.at(0), vars.at(1)});
        }
        else if (op == "gt") {
            if (vars.size() != 2)
                throw UnimplementedException{"didn't get exactly two values for gt"};
            problem.post(GreaterThan{vars.at(0), vars.at(1)});
        }
        else if (op == "ge") {
            if (vars.size() != 2)
                throw UnimplementedException{"didn't get exactly two values for ge"};
            problem.post(GreaterThanEqual{vars.at(0), vars.at(1)});
        }
        else
            throw NonExhaustiveSwitch{};
    }
    else if (op == "in") {
        ++pos;
        auto var = get<0>(disintentionify_to_intvar(s, pos, problem, mapping));
        if (s.at(pos) != ',')
            throw UnimplementedException{"parse error"};
        ++pos;
        auto vals = disintentionify_to_set_of_ints(s, pos, problem, mapping);
        if (s.at(pos) != ')')
            throw UnimplementedException{"parse error"};
        vector<IntegerVariableID> vars{*var};
        vector<vector<Integer>> feasible;
        for (auto & v : vals)
            feasible.emplace_back(vector{Integer{v}});
        problem.post(Table{vars, move(feasible)});
        ++pos;
    }
    else
        throw UnimplementedException{"top level operator '" + op + "'"};

    if (pos != s.size())
        throw UnimplementedException{"trailing text '" + s.substr(pos) + "'"};
}

struct ParserCallbacks : XCSP3CoreCallbacks
{
    Problem & problem;
    VariableMapping mapping;

    shared_ptr<WildcardTuples> most_recent_tuples;
    bool is_optimisation = false;
    optional<IntegerVariableID> objective_variable;

    explicit ParserCallbacks(Problem & p) :
        problem(p)
    {
        intensionUsingString = true;
        recognizeSpecialIntensionCases = false;
    }

    virtual auto buildVariableInteger(string id, int min_value, int max_value) -> void override
    {
        mapping.emplace(id, tuple{nullopt, Integer{min_value}, Integer{max_value}, nullopt});
    }

    virtual auto buildVariableInteger(string id, vector<int> & vals) -> void override
    {
        if (vals.empty())
            throw UnimplementedException{"empty values"};
        auto [min, max] = minmax_element(vals.begin(), vals.end());
        mapping.emplace(id, tuple{nullopt, Integer{*min}, Integer{*max}, vals});
    }

    virtual auto buildConstraintExtension(string, vector<XVariable *> x_vars, vector<vector<int>> & x_tuples, bool is_support, bool) -> void
    {
        vector<IntegerVariableID> vars;
        for (auto & v : x_vars) {
            auto m = mapping.find(v->id);
            need_variable(problem, m->second, v->id);
            vars.emplace_back(*get<0>(m->second));
        }

        most_recent_tuples = make_shared<WildcardTuples>();
        for (auto & t : x_tuples) {
            vector<IntegerOrWildcard> tuple;
            for (auto & v : t)
                if (v == STAR)
                    tuple.emplace_back(Wildcard{});
                else
                    tuple.emplace_back(Integer{v});
            most_recent_tuples->emplace_back(move(tuple));
        }

        if (is_support)
            problem.post(Table{vars, SharedWildcardTuples{most_recent_tuples}});
        else
            problem.post(NegativeTable{vars, SharedWildcardTuples{most_recent_tuples}});
    }

    virtual auto buildConstraintExtensionAs(string, vector<XVariable *> x_vars, bool is_support, bool) -> void
    {
        vector<IntegerVariableID> vars;
        for (auto & v : x_vars) {
            auto m = mapping.find(v->id);
            need_variable(problem, m->second, v->id);
            vars.emplace_back(*get<0>(m->second));
        }

        if (is_support)
            problem.post(Table{vars, SharedWildcardTuples{most_recent_tuples}});
        else
            problem.post(NegativeTable{vars, SharedWildcardTuples{most_recent_tuples}});
    }

    virtual auto buildConstraintExtension(string, XVariable * x_var, vector<int> & x_tuples, bool is_support, bool) -> void
    {
        vector<IntegerVariableID> vars;
        auto m = mapping.find(x_var->id);
        need_variable(problem, m->second, x_var->id);
        vars.emplace_back(*get<0>(m->second));

        most_recent_tuples = make_shared<WildcardTuples>();
        for (auto & t : x_tuples) {
            vector<IntegerOrWildcard> tuple;
            if (t == STAR)
                tuple.emplace_back(Wildcard{});
            else
                tuple.emplace_back(Integer{t});
            most_recent_tuples->emplace_back(move(tuple));
        }

        if (is_support)
            problem.post(Table{vars, SharedWildcardTuples{most_recent_tuples}});
        else
            problem.post(NegativeTable{vars, SharedWildcardTuples{most_recent_tuples}});
    }

    virtual auto buildConstraintAlldifferent(string, vector<XVariable *> & x_vars) -> void override
    {
        vector<IntegerVariableID> vars;
        for (auto & v : x_vars) {
            auto m = mapping.find(v->id);
            need_variable(problem, m->second, v->id);
            vars.emplace_back(*get<0>(m->second));
        }
        problem.post(AllDifferent{vars});
    }

    auto buildConstraintSumCommon(string, vector<XVariable *> & x_vars, const optional<vector<int>> & coeffs, XCondition & cond) -> void
    {
        Linear cvs;
        Integer range = 0_i;
        for (const auto & [idx, x] : enumerate(x_vars)) {
            auto m = mapping.find(x->id);
            need_variable(problem, m->second, x->id);
            cvs.emplace_back(coeffs ? Integer{coeffs->at(idx)} : 1_i, *get<0>(m->second));
            range += abs(cvs.back().first) * max(abs(get<1>(m->second)), abs(get<2>(m->second)));
        }

        Integer bound = 0_i;
        switch (cond.operandType) {
        case OperandType::VARIABLE:
            bound = 0_i;
            {
                auto m = mapping.find(cond.var);
                need_variable(problem, m->second, cond.var);
                cvs.emplace_back(-1_i, *get<0>(mapping.at(cond.var)));
            }
            break;
        case OperandType::INTEGER:
            bound = Integer{cond.val};
            break;
        case OperandType::INTERVAL:
            throw UnimplementedException{"intervals"};
        }

        switch (cond.op) {
        case OrderType::LE:
            problem.post(LinearLessEqual{move(cvs), bound});
            break;
        case OrderType::LT:
            problem.post(LinearLessEqual{move(cvs), bound - 1_i});
            break;
        case OrderType::EQ:
            problem.post(LinearEquality{move(cvs), bound});
            break;
        case OrderType::GT:
            problem.post(LinearGreaterThanEqual{move(cvs), bound + 1_i});
            break;
        case OrderType::GE:
            problem.post(LinearGreaterThanEqual{move(cvs), bound});
            break;
        case OrderType::NE: {
            auto diff = problem.create_integer_variable(-range, range, "ne");
            cvs.emplace_back(1, diff);
            problem.post(LinearEquality{move(cvs), bound});
            problem.post(NotEquals{diff, 0_c});
        } break;
        case OrderType::IN:
            throw UnimplementedException{"order type"};
        }
    }

    virtual auto buildConstraintSum(string id, vector<XVariable *> & x_vars, vector<int> & coeffs, XCondition & cond) -> void override
    {
        buildConstraintSumCommon(id, x_vars, coeffs, cond);
    }

    virtual auto buildConstraintSum(string id, vector<XVariable *> & x_vars, XCondition & cond) -> void override
    {
        buildConstraintSumCommon(id, x_vars, nullopt, cond);
    }

    virtual auto buildConstraintIntension(string, string expr) -> void override
    {
        disintentionify(expr, problem, mapping);
    }

    virtual auto buildConstraintElement(string, vector<XVariable *> & x_vars,
        int startIndex, XVariable * index, RankType rank, int value) -> void override
    {
        if (0 != startIndex)
            throw UnimplementedException{"non-zero start index"};
        if (rank != RankType::ANY)
            throw UnimplementedException{"non-any rank"};

        vector<IntegerVariableID> vars;
        for (auto & v : x_vars) {
            auto m = mapping.find(v->id);
            need_variable(problem, m->second, v->id);
            vars.emplace_back(*get<0>(m->second));
        }

        auto m = mapping.find(index->id);
        need_variable(problem, m->second, index->id);

        problem.post(Element{constant_variable(Integer{value}), *get<0>(m->second), vars});
    }

    virtual auto buildConstraintElement(string, vector<int> & vals,
        int startIndex, XVariable * index, RankType rank, XVariable * value) -> void override
    {
        if (0 != startIndex)
            throw UnimplementedException{"non-zero start index"};
        if (rank != RankType::ANY)
            throw UnimplementedException{"non-any rank"};

        vector<IntegerVariableID> vars;
        for (auto & v : vals)
            vars.emplace_back(constant_variable(Integer{v}));

        auto m = mapping.find(index->id);
        need_variable(problem, m->second, index->id);

        auto n = mapping.find(value->id);
        need_variable(problem, n->second, value->id);

        problem.post(Element{*get<0>(n->second), *get<0>(m->second), vars});
    }

    virtual auto buildObjectiveMinimize(ExpressionObjective type, vector<XVariable *> & x_vars, vector<int> & coeffs) -> void override
    {
        buildObjectiveCommon(type, x_vars, coeffs, false);
    }

    virtual auto buildObjectiveMaximize(ExpressionObjective type, vector<XVariable *> & x_vars, vector<int> & coeffs) -> void override
    {
        buildObjectiveCommon(type, x_vars, coeffs, true);
    }

    auto buildObjectiveCommon(ExpressionObjective type, vector<XVariable *> & x_vars, vector<int> & coeffs, bool is_max) -> void
    {
        is_optimisation = true;

        if (type == ExpressionObjective::MINIMUM_O || type == ExpressionObjective::MAXIMUM_O) {
            optional<Integer> lower, upper;
            vector<IntegerVariableID> vars;
            for (auto & x : x_vars) {
                auto m = mapping.find(x->id);
                need_variable(problem, m->second, x->id);
                auto [var, l, u, _] = m->second;
                if (! lower)
                    lower = l;
                if (! upper)
                    upper = u;
                lower = min(*lower, l);
                upper = max(*upper, u);

                vars.push_back(*var);
            }

            auto obj = problem.create_integer_variable(*lower, *upper, "objective");
            objective_variable = obj;

            if (type == ExpressionObjective::MINIMUM_O)
                problem.post(ArrayMin{vars, obj});
            else
                problem.post(ArrayMax{vars, obj});

            if (is_max)
                problem.maximise(obj);
            else
                problem.minimise(obj);
        }
        else if (type == ExpressionObjective::SUM_O) {
            Integer lower = 0_i, upper = 0_i;
            Linear cvs;
            for (const auto & [idx, x] : enumerate(x_vars)) {
                auto m = mapping.find(x->id);
                need_variable(problem, m->second, x->id);
                auto [var, l, u, _] = m->second;
                cvs.emplace_back(coeffs.at(idx), *var);
                if (coeffs.at(idx) < 0) {
                    lower += Integer{coeffs.at(idx)} * u;
                    upper += Integer{coeffs.at(idx)} * l;
                }
                else {
                    lower += Integer{coeffs.at(idx)} * l;
                    upper += Integer{coeffs.at(idx)} * u;
                }
            }

            auto obj = problem.create_integer_variable(lower, upper, "objective");
            objective_variable = obj;
            cvs.emplace_back(-1, obj);

            problem.post(LinearEquality{move(cvs), 0_i});
            if (is_max)
                problem.maximise(obj);
            else
                problem.minimise(obj);
        }
    }
};

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof")          //
        ("all", "Find all solutions")        //
        ("timeout", po::value<int>(), "Timeout in seconds");

    po::options_description all_options{"All options"};
    all_options.add_options() //
        ("file", po::value<string>(), "Input file in XCSP format");

    po::positional_options_description positional_options;
    positional_options
        .add("file", -1);

    all_options.add(display_options);

    po::variables_map options_vars;

    try {
        po::store(po::command_line_parser(argc, argv)
                      .options(all_options)
                      .positional(positional_options)
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
        cout << "Usage: " << argv[0] << " [options] xcsp-file.xml" << endl;
        cout << endl;
        cout << display_options << endl;
        return EXIT_SUCCESS;
    }

    auto start_time = steady_clock::now();

    Problem problem;
    ParserCallbacks callbacks{problem};
    try {
        XCSP3Core::XCSP3CoreParser parser{&callbacks};
        parser.parse(options_vars["file"].as<string>().c_str());
    }
    catch (const UnimplementedException & e) {
        cout << "s UNSUPPORTED" << endl;
        cout << "c " << e.what() << endl;
        return EXIT_FAILURE;
    }

    auto model_done_duration = duration_cast<microseconds>(steady_clock::now() - start_time);
    cout << "d MODEL BUILD TIME " << (model_done_duration.count() / 1'000'000.0) << "s" << endl;

    optional<CurrentState> saved_solution;

    signal(SIGINT, &sig_int_or_term_handler);
    signal(SIGTERM, &sig_int_or_term_handler);

    thread timeout_thread;
    mutex timeout_mutex;
    condition_variable timeout_cv;
    bool actually_timed_out = false;

    if (options_vars.contains("timeout")) {
        seconds limit{options_vars["timeout"].as<int>()};

        timeout_thread = thread([limit = limit, &timeout_mutex, &timeout_cv, &actually_timed_out] {
            auto abort_time = system_clock::now() + limit;
            {
                /* Sleep until either we've reached the time limit,
                 * or we've finished all the work. */
                unique_lock<mutex> guard(timeout_mutex);
                while (! abort_flag.load()) {
                    if (cv_status::timeout == timeout_cv.wait_until(guard, abort_time)) {
                        /* We've woken up, and it's due to a timeout. */
                        actually_timed_out = true;
                        break;
                    }
                }
            }
            abort_flag.store(true);
        });
    }

    auto stats = solve_with(problem,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                saved_solution.emplace(s.clone());
                if (callbacks.is_optimisation) {
                    cout << "o " << s(*callbacks.objective_variable) << endl;
                    return true;
                }
                else if (options_vars.contains("all"))
                    return true;
                else
                    return false;
            }},
        options_vars.contains("prove") ? make_optional<ProofOptions>("xcsp.opb", "xcsp.veripb") : nullopt,
        &abort_flag);

    if (timeout_thread.joinable()) {
        {
            unique_lock<mutex> guard(timeout_mutex);
            abort_flag.store(true);
            timeout_cv.notify_all();
        }
        timeout_thread.join();
    }

    bool actually_aborted = actually_timed_out || was_terminated.load();

    if (actually_aborted) {
        if (callbacks.is_optimisation && saved_solution)
            cout << "s SATISFIABLE" << endl;
        else
            cout << "s UNKNOWN" << endl;
    }
    else if (! saved_solution) {
        cout << "s UNSATISFIABLE" << endl;
    }
    else if (callbacks.is_optimisation)
        cout << "s OPTIMUM FOUND" << endl;
    else
        cout << "s SATISFIABLE" << endl;

    if (saved_solution) {
        cout << "v <instantiation>" << endl;
        cout << "v   <list>";
        for (const auto & [n, _] : callbacks.mapping)
            cout << " " << n;
        cout << " </list>" << endl;
        cout << "v   <values>";
        for (const auto & [_, v] : callbacks.mapping)
            if (get<0>(v))
                cout << " " << (*saved_solution)(*get<0>(v));
            else
                cout << " *";
        cout << " </values>" << endl;
        cout << "v </instantiation>" << endl;
    }

    cout << "d WRONG DECISIONS " << stats.failures << endl;
    cout << "d PROPAGATIONS " << stats.propagations << endl;
    cout << "d EFFECTFUL PROPAGATIONS " << stats.effectful_propagations << endl;
    cout << "d CONTRADICTING PROPAGATIONS " << stats.contradicting_propagations << endl;
    cout << "d SOLVE TIME " << (stats.solve_time.count() / 1'000'000.0) << "s" << endl;

    if (options_vars.contains("all"))
        cout << "d FOUND SOLUTIONS " << stats.solutions << endl;

    return actually_aborted ? EXIT_FAILURE : EXIT_SUCCESS;
}
