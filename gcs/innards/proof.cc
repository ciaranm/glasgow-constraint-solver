#include <gcs/exception.hh>
#include <gcs/innards/bits_encoding.hh>
#include <gcs/innards/literal_utils.hh>
#include <gcs/innards/opb_utils.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/state.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <iterator>
#include <list>
#include <map>
#include <set>
#include <sstream>
#include <tuple>
#include <unordered_map>
#include <vector>

#include <condition_variable>
#include <iostream>
#include <mutex>
#include <queue>
#include <thread>

using namespace gcs;
using namespace gcs::innards;

using std::condition_variable;
using std::copy;
using std::flush;
using std::fstream;
using std::ios;
using std::istreambuf_iterator;
using std::list;
using std::map;
using std::max;
using std::min;
using std::move;
using std::mutex;
using std::nullopt;
using std::ofstream;
using std::optional;
using std::ostream;
using std::ostreambuf_iterator;
using std::pair;
using std::queue;
using std::set;
using std::string;
using std::stringstream;
using std::thread;
using std::to_string;
using std::tuple;
using std::unique_lock;
using std::unordered_map;
using std::variant;
using std::vector;
using std::visit;

namespace
{
    auto value_name(Integer v) -> string
    {
        return to_string(v.raw_value);
    }
}

auto gcs::innards::sanitise_literals(Literals & lits) -> bool
{
    // if we've got a literal that is definitely true, the clause is always satisfied,
    // so we can discard the clause
    if (lits.end() != find_if(lits.begin(), lits.end(), [](const Literal & lit) -> bool { return is_literally_true(lit); }))
        return false;

    // remove any literals that are definitely false. this might remove everything, in
    // which case we get the empty clause which is false so it's fine.
    lits.erase(remove_if(lits.begin(), lits.end(), [&](const Literal & lit) -> bool { return is_literally_false(lit); }), lits.end());

    // put these in some kind of order
    sort(lits.begin(), lits.end());

    // remove duplicates
    lits.erase(unique(lits.begin(), lits.end()), lits.end());

    return true;
}

namespace
{
    [[nodiscard]] auto is_literally_true_or_false(const ProofFlag &) -> optional<bool>
    {
        return nullopt;
    }

    [[nodiscard]] auto is_literally_true_or_false(const IntegerVariableID &) -> optional<bool>
    {
        return nullopt;
    }

    [[nodiscard]] auto is_literally_true_or_false(const ProofOnlySimpleIntegerVariableID &) -> optional<bool>
    {
        return nullopt;
    }
}

auto gcs::innards::sanitise_pseudoboolean_terms(WeightedPseudoBooleanSum & lits, Integer & val) -> bool
{
    using ::is_literally_true_or_false; // because C++

    // adjust coefficients down for true and false literals
    for (const auto & l : lits.terms) {
        auto t_or_f = visit([&](const auto & t) { return is_literally_true_or_false(t); }, l.variable);
        if (t_or_f && *t_or_f)
            val -= l.coefficient;
        else if (t_or_f && ! *t_or_f)
            val += l.coefficient;
    }

    // now actually remove true and false literals
    lits.terms.erase(remove_if(lits.terms.begin(), lits.terms.end(), [&](const auto & wlit) -> bool {
        return nullopt != visit([&](const auto & t) { return is_literally_true_or_false(t); }, wlit.variable);
    }),
        lits.terms.end());

    return true;
}

ProofError::ProofError(const string & w) :
    _wat("unexpected problem: " + w)
{
}

auto ProofError::what() const noexcept -> const char *
{
    return _wat.c_str();
}

auto gcs::innards::operator!(const ProofFlag & f) -> ProofFlag
{
    return ProofFlag{f.index, ! f.positive};
}

struct Proof::Imp
{
    unsigned long long model_variables = 0;
    ProofLine model_constraints = 0;
    ProofLine proof_line = 0;
    int active_proof_level = 0;

    map<SimpleOrProofOnlyIntegerVariableID, ProofLine> variable_at_least_one_constraints;
    map<LiteralFromIntegerVariable, string> direct_integer_variables;
    map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, vector<pair<Integer, string>>>> integer_variable_bits;
    map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, Integer>> bounds_for_gevars;
    map<SimpleIntegerVariableID, set<Integer>> gevars_that_exist;
    list<IntegerVariableID> solution_variables;
    map<pair<unsigned long long, bool>, string> flags;
    map<unsigned long long, string> proof_only_integer_variables;

    list<map<tuple<bool, SimpleIntegerVariableID, Integer>, variant<ProofLine, string>>> line_for_bound_in_bits;

    string opb_file, proof_file;
    stringstream opb;
    fstream proof;
    bool opb_done = false;

    bool use_friendly_names;
    bool always_use_full_encoding;
    unordered_map<string, string> xification;

    queue<Work> proofWorkQueue;
    condition_variable not_empty_work;
    std::mutex myMutexWork;
    bool finished = false;
    std::thread thread_proof_work;

    // condition_variable not_ful_work;
    // long unsigned int maxSize = 10;
};

Proof::Proof(const ProofOptions & proof_options) :
    _imp(new Imp)
{
    _imp->opb_file = proof_options.opb_file;
    _imp->proof_file = proof_options.proof_file;
    _imp->use_friendly_names = proof_options.use_friendly_names;
    _imp->always_use_full_encoding = proof_options.always_use_full_encoding;
    _imp->line_for_bound_in_bits.emplace_back();
    startWorkThread();
}

Proof::~Proof()
{
    joinThread();
};

void Proof::startWorkThread()
{
    _imp->thread_proof_work = std::thread(&Proof::threadWorkEntry, this);
}

auto Proof::push_work_queue(Work work)
{
    // auto visitor = overloaded{
    //     [&](string & proof_text) { std::cout << "Text pushed : " << proof_text << std::endl; },
    //     [&](JustifyExplicitlyProof & jep) {},
    // };
    // std::visit(visitor, work);

    unique_lock<mutex> lock(_imp->myMutexWork);
    // _imp->not_full.wait(lock, [&] { return _imp->proofWorkQueue.size() < _imp->maxSize; });
    _imp->proofWorkQueue.push(work);
    _imp->not_empty_work.notify_one();
    lock.unlock();
}

auto Proof::output_it(const string & rule, Literal lit, vector<Literal> guesses, vector<Literal> extra_proof_conditions, const std::optional<bool> & work)
{
    string text_pushed;

    if (! is_literally_true(lit)) {
        text_pushed = rule;
        for_each_guess([&](const Literal & lit) {
            if (! is_literally_true(lit)) {
                text_pushed += " 1 " + proof_variable(! lit);
            }
        },
            guesses, extra_proof_conditions);
        if (! is_literally_false(lit)) {
            text_pushed += " 1 " + proof_variable(lit);
        }
        text_pushed += " >= 1 ;\n";
        if (work) {
            _imp->proof << text_pushed;
        }
        else {
            push_work_queue(Work{text_pushed});
        }
        ++_imp->proof_line;
    }
};

auto Proof::for_each_guess(const std::function<auto(Literal)->void> & f, vector<Literal> guesses, vector<Literal> extra_proof_conditions) const -> void
{
    for (auto & g : extra_proof_conditions)
        f(g);
    for (auto & g : guesses)
        f(g);
}

void Proof::threadWorkEntry()
{
    while (true) {
        std::unique_lock<std::mutex> lock(_imp->myMutexWork);
        _imp->not_empty_work.wait(lock, [&] { return (_imp->finished || ! _imp->proofWorkQueue.empty()); });
        if (! _imp->proofWorkQueue.empty()) {
            Work work = _imp->proofWorkQueue.front();

            // std::cout << "proofQueue.size() : " << proofQueue.size() << std::endl;
            _imp->proofWorkQueue.pop();
            lock.unlock();

            auto visitor = overloaded{
                [&](string & proof_text) {
                    // std::unique_lock<std::mutex> lockText(_imp->myMutexText);
                    // _imp->proofTextQueue.push(proof_text);
                    // _imp->not_empty_text.notify_one();
                    // lockText.unlock();

                    // std::cout << "Text written from threadWork: " << proof_text << std::endl;
                    _imp->proof << proof_text;
                },
                [&](const WorkJustifyUsingRUP & w) {
                    need_proof_variable(w.lit, true);
                    output_it("u", w.lit, w.guesses, w.extra_proof_conditions, true);
                    // std::cout << "WorkJustyUsingRUP done\n";
                },
                [&](const WorkJustifyUsingAssertion & w) {
                    need_proof_variable(w.lit, true);
                    output_it("a", w.lit, w.guesses, w.extra_proof_conditions, true);
                },
                [&](const WorkJustifyExplicitly & w) {
                    vector<ProofLine> to_delete;
                    add_proof_steps(w.x, to_delete);
                    // infer(w.state, w.lit, JustifyUsingRUP{});
                    need_proof_variable(w.lit, true);
                    output_it("u", w.lit, w.guesses, w.extra_proof_conditions, true);
                    delete_proof_lines(to_delete);
                },
                [&](const WorkGuess & w) {
                    if (! is_literally_true(w.lit)) {
                        // we need this because it'll show up in the trail later
                        need_proof_variable(w.lit, true);
                        _imp->proof << "* guessing " << proof_variable(w.lit) << ", decision stack is [";
                        for_each_guess([&](const Literal & lit) {
                            if (! is_literally_true(lit)) {
                                _imp->proof << " " << proof_variable(lit);
                            }
                        },
                            w.guesses, w.extra_proof_conditions);
                        _imp->proof << " ]\n";
                    }
                }

            };
            std::visit(visitor, work);

            // _imp->not_full.notify_one();
            // lock.unlock();
        }
        else if (_imp->finished) {
            _imp->proof << flush;
            // std::cout << "Thread proof finished\n";
            break;
        }
    }
}

// void Proof::threadTextEntry()
// {
//     string proof_text;
//     while (true) {
//         std::unique_lock<std::mutex> lock(_imp->myMutexText);
//         _imp->not_empty_text.wait(lock, [&] { return (_imp->work_finished || ! _imp->proofTextQueue.empty()); });
//         if (! _imp->proofTextQueue.empty()) {
//             proof_text = _imp->proofTextQueue.front();

//             // std::cout << "proofQueue.size() : " << proofQueue.size() << std::endl;
//             _imp->proofTextQueue.pop();
//             lock.unlock();
//             _imp->proof << proof_text;
//             std::cout << "Text written from threadText: " << proof_text << std::endl;
//         }
//         else if (_imp->work_finished) {
//             _imp->proof << flush;
//             // std::cout << "Thread proof finished\n";
//             break;
//         }
//     }
// }

void Proof::joinThread()
{
    _imp->thread_proof_work.join();
}

void Proof::Stop()
{
    std::lock_guard<std::mutex> lockWork(_imp->myMutexWork);
    _imp->finished = true;
    _imp->not_empty_work.notify_one();
};

// auto Proof::push_text_queue(string text_proof)
// {
//     unique_lock<mutex> lock(_imp->myMutexText);
//     _imp->proofTextQueue.push(text_proof);
//     // std::cout << "Text pushed : " << text_proof << std::endl;
//     _imp->not_empty_text.notify_one();
//     lock.unlock();
// }

[[nodiscard]] auto Proof::xify(std::string && s) -> std::string
{
    if (_imp->use_friendly_names)
        return s;
    else
        return _imp->xification.try_emplace(s, "x" + to_string(_imp->xification.size() + 1)).first->second;
}

auto Proof::set_up_bits_variable_encoding(SimpleOrProofOnlyIntegerVariableID id, Integer lower, Integer upper, const string & name) -> void
{
    if (_imp->opb_done)
        throw UnexpectedException{"proof has already started"};

    _imp->opb << "* variable " << name << " " << lower.raw_value << " .. " << upper.raw_value << " bits encoding\n";
    auto [highest_bit_shift, highest_bit_coeff, negative_bit_coeff] = get_bits_encoding_coeffs(lower, upper);
    auto & bit_vars = _imp->integer_variable_bits.emplace(id, pair{negative_bit_coeff, vector<pair<Integer, string>>{}}).first->second.second;
    if (0_i != negative_bit_coeff)
        bit_vars.emplace_back(negative_bit_coeff, xify(name + "_bn_" + to_string(highest_bit_shift + 1)));
    for (int b = 0; b <= highest_bit_shift; ++b)
        bit_vars.emplace_back(Integer{1ll << b}, xify(name + "_b_" + to_string(b)));
    _imp->model_variables += bit_vars.size();

    // lower bound
    for (auto & [coeff, var] : bit_vars)
        _imp->opb << coeff << " " << var << " ";
    _imp->opb << ">= " << lower << " ;\n";
    ++_imp->model_constraints;

    overloaded{
        [&](const SimpleIntegerVariableID & id) {
            _imp->line_for_bound_in_bits.back().emplace(tuple{false, id, lower}, ProofLine{_imp->model_constraints});
        },
        [&](const ProofOnlySimpleIntegerVariableID &) {
        }}
        .visit(id);

    // upper bound
    for (auto & [coeff, var] : bit_vars)
        _imp->opb << -coeff << " " << var << " ";
    _imp->opb << ">= " << -upper << " ;\n";
    ++_imp->model_constraints;

    overloaded{
        [&](const SimpleIntegerVariableID & id) {
            _imp->line_for_bound_in_bits.back().emplace(tuple{true, id, upper}, ProofLine{_imp->model_constraints});
        },
        [&](const ProofOnlySimpleIntegerVariableID &) {
        }}
        .visit(id);

    _imp->bounds_for_gevars.emplace(id, pair{lower, upper});

    if (_imp->always_use_full_encoding)
        overloaded{
            [&](const SimpleIntegerVariableID & id) {
                for (; lower <= upper; ++lower)
                    need_direct_encoding_for(id, lower);
            },
            [&](const ProofOnlySimpleIntegerVariableID &) {
            }}
            .visit(id);
}

auto Proof::set_up_direct_only_variable_encoding(SimpleOrProofOnlyIntegerVariableID id, Integer lower, Integer upper, const string & name) -> void
{
    if (_imp->opb_done)
        throw UnexpectedException{"proof has already started"};

    _imp->opb << "* variable " << name << " " << lower.raw_value << " .. " << upper.raw_value << " direct encoding\n";

    if (0_i == lower && 1_i == upper) {
        auto eqvar = xify(name + "_t");
        _imp->opb << "1 " << eqvar << " >= 0 ;\n";
        ++_imp->model_variables;
        ++_imp->model_constraints;

        overloaded{
            [&](const SimpleIntegerVariableID & id) {
                _imp->line_for_bound_in_bits.back().emplace(tuple{false, id, lower}, eqvar);
                _imp->line_for_bound_in_bits.back().emplace(tuple{true, id, upper}, "~" + eqvar);

                _imp->direct_integer_variables.emplace(id == 1_i, eqvar);
                _imp->direct_integer_variables.emplace(id != 1_i, "~" + eqvar);
                _imp->direct_integer_variables.emplace(id == 0_i, "~" + eqvar);
                _imp->direct_integer_variables.emplace(id != 0_i, eqvar);
            },
            [](const ProofOnlySimpleIntegerVariableID &) {
                // currently there's no API for asking for literals for these
            }}
            .visit(id);

        auto & bit_vars = _imp->integer_variable_bits.emplace(id, pair{0_i, vector<pair<Integer, string>>{}}).first->second.second;
        bit_vars.emplace_back(1_i, eqvar);

        overloaded{
            [&](const SimpleIntegerVariableID & id) {
                _imp->direct_integer_variables.emplace(id >= 1_i, eqvar);
                _imp->direct_integer_variables.emplace(id < 1_i, "~" + eqvar);
            },
            [](const ProofOnlySimpleIntegerVariableID &) {
                // currently there's no API for asking for literals for these
            }}
            .visit(id);
    }
    else {
        for (auto v = lower; v <= upper; ++v) {
            auto eqvar = xify(name + "_eq_" + value_name(v));
            _imp->opb << "1 " << eqvar << " ";
            ++_imp->model_variables;

            overloaded{
                [&](const SimpleIntegerVariableID & id) {
                    _imp->direct_integer_variables.emplace(id == v, eqvar);
                    _imp->direct_integer_variables.emplace(id != v, "~" + eqvar);
                },
                [](const ProofOnlySimpleIntegerVariableID &) {
                    // currently there's no API for asking for literals for these
                }}
                .visit(id);
        }
        _imp->opb << ">= 1 ;\n";
        _imp->variable_at_least_one_constraints.emplace(id, ++_imp->model_constraints);

        for (auto v = lower; v <= upper; ++v) {
            auto eqvar = xify(name + "_eq_" + value_name(v));
            _imp->opb << "-1 " << eqvar << " ";
        }
        _imp->opb << ">= -1 ;\n";
        ++_imp->model_constraints;
    }
}

auto Proof::set_up_integer_variable(SimpleIntegerVariableID id, Integer lower, Integer upper,
    const optional<string> & optional_name, const optional<IntegerVariableProofRepresentation> & rep) -> void
{
    string name = "iv" + to_string(id.index);
    if (optional_name)
        name.append("_" + *optional_name);
    if (! rep) {
        if (lower == 0_i && upper == 1_i)
            set_up_direct_only_variable_encoding(id, lower, upper, name);
        else
            set_up_bits_variable_encoding(id, lower, upper, name);
    }
    else {
        switch (*rep) {
        case IntegerVariableProofRepresentation::Bits:
            set_up_bits_variable_encoding(id, lower, upper, name);
            break;
        case IntegerVariableProofRepresentation::DirectOnly:
            set_up_direct_only_variable_encoding(id, lower, upper, name);
            break;
        }
    }
    _imp->solution_variables.push_back(id);
}

auto Proof::create_proof_flag(const string & n) -> ProofFlag
{
    ProofFlag result{_imp->flags.size() / 2, true};

    string name = xify("flag" + to_string(result.index) + "_" + n);
    _imp->flags.emplace(pair{result.index, true}, name);
    _imp->flags.emplace(pair{result.index, false}, "~" + name);
    return result;
}

auto Proof::create_proof_integer_variable(Integer lower, Integer upper, const std::string & s,
    const IntegerVariableProofRepresentation rep) -> ProofOnlySimpleIntegerVariableID
{
    ProofOnlySimpleIntegerVariableID id{_imp->proof_only_integer_variables.size()};
    _imp->proof_only_integer_variables.emplace(id.index, s);
    string name = "poiv" + to_string(id.index) + "_" + s;
    switch (rep) {
    case IntegerVariableProofRepresentation::DirectOnly:
        set_up_direct_only_variable_encoding(id, lower, upper, name);
        break;
    case IntegerVariableProofRepresentation::Bits:
        set_up_bits_variable_encoding(id, lower, upper, name);
        break;
    }

    return id;
}

auto Proof::need_gevar(SimpleIntegerVariableID id, Integer v, const std::optional<bool> & work) -> void
{
    using namespace gcs::innards::opb_utils;

    if (_imp->direct_integer_variables.contains(id >= v))
        return;

    string name = "iv" + to_string(id.index);
    auto gevar = xify(name + "_ge_" + value_name(v));
    _imp->direct_integer_variables.emplace(id >= v, gevar);
    _imp->direct_integer_variables.emplace(id < v, "~" + gevar);
    _imp->gevars_that_exist[id].insert(v);

    if (_imp->opb_done) {
        if (work) {
            _imp->proof << "* need " << gevar << '\n';
        }
        else {
            // _imp->proof << "* need " << gevar << '\n';
            push_work_queue(Work{"* need " + gevar + '\n'});
        }
    }
    else {
        _imp->opb << "* need " << gevar << '\n';
    }

    auto & [_, bit_vars] = _imp->integer_variable_bits.at(id);

    if (_imp->opb_done) {
        if (work) {
            _imp->proof << "# 0\n";
        }
        else {
            // _imp->proof << "# 0\n";
            push_work_queue(Work{"# 0\n"});
        }
    }

    // gevar -> bits
    auto gevar_implies_bits = implied_by(opb_sum(bit_vars) >= v, gevar);
    if (_imp->opb_done) {
        if (work) {
            _imp->proof << "red " << gevar_implies_bits << " ; " << gevar << " 0\n";
        }
        else {
            // _imp->proof << "red " << gevar_implies_bits << " ; " << gevar << " 0\n";
            push_work_queue(Work{"red " + gevar_implies_bits.OPBInequality_to_string() + " ; " + gevar + " 0\n"});
        }
        ++_imp->proof_line;
    }
    else {
        _imp->opb << gevar_implies_bits << " ;\n";
        ++_imp->model_constraints;
        ++_imp->model_variables;
    }

    // !gevar -> bits
    auto not_gevar_implies_bits = implied_by(opb_sum(bit_vars) < v, negate_opb_var_name(gevar));
    if (_imp->opb_done) {
        if (work) {
            _imp->proof << "red " << not_gevar_implies_bits << " ; " << gevar << " 1\n";
        }
        else {
            // _imp->proof << "red " << not_gevar_implies_bits << " ; " << gevar << " 1\n";
            push_work_queue(Work{"red " + not_gevar_implies_bits.OPBInequality_to_string() + " ; " + gevar + " 1\n"});
        }
        ++_imp->proof_line;
    }
    else {
        _imp->opb << not_gevar_implies_bits << " ;\n";
        ++_imp->model_constraints;
    }

    // is it a bound?
    auto bounds = _imp->bounds_for_gevars.find(id);

    // lower?
    if (bounds != _imp->bounds_for_gevars.end() && bounds->second.first == v) {
        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "u 1 " << gevar << " >= 1 ;\n";
            }
            else {
                // _imp->proof << "u 1 " << gevar << " >= 1 ;\n";
                push_work_queue(Work{"u 1 " + gevar + " >= 1 ;\n"});
            }
            ++_imp->proof_line;
        }
        else {
            _imp->opb << "1 " << gevar << " >= 1 ;\n";
            ++_imp->model_constraints;
        }
    }

    // upper?
    if (bounds != _imp->bounds_for_gevars.end() && bounds->second.second < v) {
        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "u 1 ~" << gevar << " >= 1 ;\n";
            }
            else {
                // _imp->proof << "u 1 ~" << gevar << " >= 1 ;\n";
                push_work_queue(Work{"u 1 ~" + gevar + " >= 1 ;\n"});
            }
            ++_imp->proof_line;
        }
        else {
            _imp->opb << "1 ~" << gevar << " >= 1 ;\n";
            ++_imp->model_constraints;
        }
    }

    auto & other_gevars = _imp->gevars_that_exist.at(id);
    auto this_gevar = other_gevars.find(v);
    auto higher_gevar = next(this_gevar);

    // implied by the next highest gevar, if there is one?
    if (higher_gevar != other_gevars.end()) {
        auto implies_higher = implies(opb_var_as_sum(proof_variable(id >= *higher_gevar)), proof_variable(id >= v));
        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "u " << implies_higher << " ;\n";
            }
            else {
                // _imp->proof << "u " << implies_higher << " ;\n";
                push_work_queue(Work{"u " + implies_higher.OPBInequality_to_string() + " ;\n"});
            }
            ++_imp->proof_line;
        }
        else {
            _imp->opb << implies_higher << " ;\n";
            ++_imp->model_constraints;
        }
    }

    // implies the next lowest gevar, if there is one?
    if (this_gevar != other_gevars.begin()) {
        auto implies_lower = implies(opb_var_as_sum(proof_variable(id >= v)), proof_variable(id >= *prev(this_gevar)));
        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "u " << implies_lower << " ;\n";
            }
            else {
                // _imp->proof << "u " << implies_lower << " ;\n";
                push_work_queue(Work{"u " + implies_lower.OPBInequality_to_string() + " ;\n"});
            }
            ++_imp->proof_line;
        }
        else {
            _imp->opb << implies_lower << " ;\n";
            ++_imp->model_constraints;
        }
    }

    if (_imp->opb_done) {
        if (work) {
            _imp->proof << "# " << _imp->active_proof_level << "\n";
        }
        else {
            // _imp->proof << "# " << _imp->active_proof_level << "\n";
            push_work_queue(Work{"# " + to_string(_imp->active_proof_level) + "\n"});
        }
    }
}

auto Proof::need_direct_encoding_for(SimpleIntegerVariableID id, Integer v, const std::optional<bool> & work) -> void
{
    using namespace gcs::innards::opb_utils;

    if (_imp->direct_integer_variables.contains(id == v))
        return;

    string name = "iv" + to_string(id.index);
    auto eqvar = xify(name + "_eq_" + value_name(v));
    _imp->direct_integer_variables.emplace(id == v, eqvar);
    _imp->direct_integer_variables.emplace(id != v, "~" + eqvar);

    auto bounds = _imp->bounds_for_gevars.find(id);
    if (bounds != _imp->bounds_for_gevars.end() && bounds->second.first == v) {
        // it's a lower bound
        need_gevar(id, v + 1_i, work);

        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "* need lower bound " << eqvar << '\n';
            }
            else {
                // _imp->proof << "* need lower bound " << eqvar << '\n';
                push_work_queue(Work{"* need lower bound " + eqvar + '\n'});
            }
        }
        else
            _imp->opb << "* need lower bound " << eqvar << '\n';

        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "# 0\n";
            }
            else {
                // _imp->proof << "# 0\n";
                push_work_queue(Work{"# 0\n"});
            }
        }
        auto not_ge_v_plus_one = opb_sum({pair{1_i, negate_opb_var_name(proof_variable(id >= v + 1_i))}}) >= 1_i;

        // eqvar -> ! ge_v+1
        auto eqvar_true = implied_by(not_ge_v_plus_one, eqvar);

        // ge_v+1 -> eqvar
        auto eqvar_false = implies(not_ge_v_plus_one, eqvar);

        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "red " << eqvar_true << " ; " << eqvar << " 0\n";
                ++_imp->proof_line;
                _imp->proof << "red " << eqvar_false << " ; " << eqvar << " 1\n";
                ++_imp->proof_line;
            }
            else {
                // _imp->proof << "red " << eqvar_true << " ; " << eqvar << " 0\n";
                push_work_queue(Work{"red " + eqvar_true.OPBInequality_to_string() + " ; " + eqvar + " 0\n"});
                ++_imp->proof_line;
                // _imp->proof << "red " << eqvar_false << " ; " << eqvar << " 1\n";
                push_work_queue(Work{"red " + eqvar_false.OPBInequality_to_string() + " ; " + eqvar + " 1\n"});
                ++_imp->proof_line;
            }
        }
        else {
            _imp->opb << eqvar_true << " ;\n";
            _imp->opb << eqvar_false << " ;\n";
            _imp->model_constraints += 2;
            ++_imp->model_variables;
        }

        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "# " << _imp->active_proof_level << "\n";
            }
            else {
                // _imp->proof << "# " << _imp->active_proof_level << "\n";
                push_work_queue(Work{"# " + to_string(_imp->active_proof_level) + "\n"});
            }
        }
    }
    else if (bounds != _imp->bounds_for_gevars.end() && bounds->second.second == v) {
        // it's an upper bound
        need_gevar(id, v, work);

        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "* need upper bound " << eqvar << '\n';
            }
            else {
                // _imp->proof << "* need upper bound " << eqvar << '\n';
                push_work_queue(Work{"* need upper bound " + eqvar + '\n'});
            }
        }
        else {
            _imp->opb << "* need upper bound " << eqvar << '\n';
        }

        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "# 0\n";
            }
            else {
                // _imp->proof << "# 0\n";
                push_work_queue(Work{"# 0\n"});
            }
        }
        auto ge_v = opb_sum({pair{1_i, proof_variable(id >= v)}}) >= 1_i;

        // eqvar -> ge_v
        auto eqvar_true = implied_by(ge_v, eqvar);

        // ge_v -> eqvar
        auto eqvar_false = implies(ge_v, eqvar);

        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "red " << eqvar_true << " ; " << eqvar << " 0\n";
                ++_imp->proof_line;
                _imp->proof << "red " << eqvar_false << " ; " << eqvar << " 1\n";
                ++_imp->proof_line;
            }
            else {
                // _imp->proof << "red " << eqvar_true << " ; " << eqvar << " 0\n";
                push_work_queue(Work{"red " + eqvar_true.OPBInequality_to_string() + " ; " + eqvar + " 0\n"});
                ++_imp->proof_line;
                // _imp->proof << "red " << eqvar_false << " ; " << eqvar << " 1\n";
                push_work_queue(Work{"red " + eqvar_false.OPBInequality_to_string() + " ; " + eqvar + " 1\n"});
                ++_imp->proof_line;
            }
        }
        else {
            _imp->opb << eqvar_true << " ;\n";
            _imp->opb << eqvar_false << " ;\n";
            _imp->model_constraints += 2;
            ++_imp->model_variables;
        }

        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "# " << _imp->active_proof_level << "\n";
            }
            else {
                // _imp->proof << "# " << _imp->active_proof_level << "\n";
                push_work_queue(Work{"# " + to_string(_imp->active_proof_level) + "\n"});
            }
        }
    }
    else {
        // neither a lower nor an upper bound
        need_gevar(id, v, work);
        need_gevar(id, v + 1_i, work);

        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "* need " << eqvar << '\n';
            }
            else {
                // _imp->proof << "* need " << eqvar << '\n';
                push_work_queue(Work{"* need " + eqvar + '\n'});
            }
        }
        else
            _imp->opb << "* need " << eqvar << '\n';

        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "# 0\n";
            }
            else {
                // _imp->proof << "# 0\n";
                push_work_queue(Work{"# 0\n"});
            }
        }

        auto ge_v_but_not_v_plus_one = opb_sum({pair{1_i, proof_variable(id >= v)},
                                           pair{1_i, negate_opb_var_name(proof_variable(id >= v + 1_i))}}) >= 2_i;

        // eqvar -> ge_v && ! ge_v+1
        auto eqvar_true = implied_by(ge_v_but_not_v_plus_one, eqvar);

        // ge_v && ! ge_v+1 -> eqvar
        auto eqvar_false = implies(ge_v_but_not_v_plus_one, eqvar);

        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "red " << eqvar_true << " ; " << eqvar << " 0\n";
                ++_imp->proof_line;
                _imp->proof << "red " << eqvar_false << " ; " << eqvar << " 1\n";
                ++_imp->proof_line;
            }
            else {
                // _imp->proof << "red " << eqvar_true << " ; " << eqvar << " 0\n";
                push_work_queue(Work{"red " + eqvar_true.OPBInequality_to_string() + " ; " + eqvar + " 0\n"});
                ++_imp->proof_line;
                // _imp->proof << "red " << eqvar_false << " ; " << eqvar << " 1\n";
                push_work_queue(Work{"red " + eqvar_false.OPBInequality_to_string() + " ; " + eqvar + " 1\n"});
                ++_imp->proof_line;
            }
        }
        else {
            _imp->opb << eqvar_true << " ;\n";
            _imp->opb << eqvar_false << " ;\n";
            _imp->model_constraints += 2;
            ++_imp->model_variables;
        }

        if (_imp->opb_done) {
            if (work) {
                _imp->proof << "# " << _imp->active_proof_level << "\n";
            }
            else {
                // _imp->proof << "# " << _imp->active_proof_level << "\n";
                push_work_queue(Work{"# " + to_string(_imp->active_proof_level) + '\n'});
            }
        }
    }
}

auto Proof::create_literals_for_introduced_variable_value(
    SimpleIntegerVariableID id, Integer val, const optional<string> & optional_name)
    -> void
{
    string name = "iv" + to_string(id.index);
    if (optional_name)
        name.append("_" + *optional_name);

    auto x = xify(name + "_eq_" + value_name(val));
    _imp->direct_integer_variables.emplace(id == val, x);
    _imp->direct_integer_variables.emplace(id != val, "~" + x);
}

auto Proof::start_proof(State & state) -> void
{
    ofstream full_opb{_imp->opb_file};
    full_opb << "* #variable= " << _imp->model_variables << " #constraint= " << _imp->model_constraints << '\n';

    if (state.optional_minimise_variable()) {
        full_opb << "min: ";
        overloaded{
            [&](const SimpleIntegerVariableID & v) {
                for (auto & [bit_value, bit_name] : _imp->integer_variable_bits.at(v).second)
                    full_opb << bit_value << " " << bit_name << " ";
            },
            [&](const ConstantIntegerVariableID &) {
                throw UnimplementedException{};
            },
            [&](const ViewOfIntegerVariableID & v) {
                // the "then add" bit is irrelevant for the objective function
                for (auto & [bit_value, bit_name] : _imp->integer_variable_bits.at(v.actual_variable).second)
                    full_opb << (v.negate_first ? -bit_value : bit_value) << " " << bit_name << " ";
            }}
            .visit(*state.optional_minimise_variable());

        full_opb << " ;\n";
    }

    copy(istreambuf_iterator<char>{_imp->opb}, istreambuf_iterator<char>{}, ostreambuf_iterator<char>{full_opb});
    _imp->opb = stringstream{};
    _imp->opb_done = true;

    if (! full_opb)
        throw ProofError{"Error writing opb file to '" + _imp->opb_file + "'"};
    full_opb.close();

    _imp->proof.open(_imp->proof_file, ios::out);

    // _imp->proof << "pseudo-Boolean proof version 1.2\n";
    // _imp->proof << "f " << _imp->model_constraints << " 0\n";
    push_work_queue(Work{"pseudo-Boolean proof version 1.2\nf " + to_string(_imp->model_constraints) + " 0\n"});

    _imp->proof_line += _imp->model_constraints;

    if (! _imp->proof)
        throw ProofError{"Error writing proof file to '" + _imp->proof_file + "'"};
}

auto Proof::cnf(const Literals & lits) -> ProofLine
{
    if (_imp->opb_done)
        throw UnexpectedException{"proof has already started"};

    for (const auto & lit : lits)
        need_proof_variable(lit);

    for (const auto & lit : lits) {
        visit([&](const auto & lit) {
            _imp->opb << "1 " << proof_variable(lit) << " ";
        },
            lit);
    }
    _imp->opb << ">= 1 ;\n";
    return ++_imp->model_constraints;
}

auto Proof::at_most_one(const Literals & lits) -> ProofLine
{
    if (_imp->opb_done)
        throw UnexpectedException{"proof has already started"};

    for (const auto & lit : lits)
        need_proof_variable(lit);

    for (const auto & lit : lits) {
        visit([&](const auto & lit) {
            _imp->opb << "-1 " << proof_variable(lit) << " ";
        },
            lit);
    }
    _imp->opb << ">= -1 ;\n";
    return ++_imp->model_constraints;
}

auto Proof::pseudoboolean_ge(const WeightedPseudoBooleanSum & lits, Integer val,
    optional<ReificationTerm> half_reif, bool equality)
    -> ProofLine
{
    if (_imp->opb_done)
        throw UnexpectedException{"proof has already started"};

    for (const auto & [_, lit] : lits.terms)
        overloaded{
            [&](const Literal & lit) { need_proof_variable(lit); },
            [&](const IntegerVariableID &) {},
            [&](const ProofOnlySimpleIntegerVariableID &) {},
            [&](const ProofFlag &) {}}
            .visit(lit);

    if (half_reif)
        overloaded{
            [&](const Literal & lit) { need_proof_variable(lit); },
            [&](const ProofFlag &) {}}
            .visit(*half_reif);

    auto output = [&](Integer multiplier) {
        using namespace gcs::innards::opb_utils;
        OPBExpression expr;
        Integer modified_val = multiplier * val;

        for (const auto & [w, lit] : lits.terms) {
            overloaded{
                [&, w = w](const Literal & lit) {
                    expr.weighted_terms.emplace_back(multiplier * w, proof_variable(lit));
                },
                [&, w = w](const ProofFlag & flag) {
                    expr.weighted_terms.emplace_back(multiplier * w, proof_variable(flag));
                },
                [&, w = w](const ProofOnlySimpleIntegerVariableID & ivar) {
                    auto & [_, bit_vars] = _imp->integer_variable_bits.at(ivar);
                    for (auto & [bit_value, bit_name] : bit_vars)
                        expr.weighted_terms.emplace_back(multiplier * w * bit_value, bit_name);
                },
                [&, w = w](const IntegerVariableID & var) {
                    overloaded{
                        [&](const SimpleIntegerVariableID & ivar) {
                            auto & [_, bit_vars] = _imp->integer_variable_bits.at(ivar);
                            for (auto & [bit_value, bit_name] : bit_vars)
                                expr.weighted_terms.emplace_back(multiplier * w * bit_value, bit_name);
                        },
                        [&](const ConstantIntegerVariableID & cvar) {
                            modified_val -= (multiplier * w * cvar.const_value);
                        },
                        [&](const ViewOfIntegerVariableID & vvar) {
                            auto & [_, bit_vars] = _imp->integer_variable_bits.at(vvar.actual_variable);
                            for (auto & [bit_value, bit_name] : bit_vars)
                                expr.weighted_terms.emplace_back((vvar.negate_first ? -1_i : 1_i) * multiplier * w * bit_value, bit_name);
                            modified_val -= (multiplier * w * vvar.then_add);
                        }}
                        .visit(var);
                }}
                .visit(lit);
        }

        auto opb_ineq = expr >= modified_val;
        if (half_reif)
            visit([&](const auto & h) { opb_ineq = implied_by(opb_ineq, proof_variable(h)); }, *half_reif);

        _imp->opb << opb_ineq << " ;\n";
    };

    if (equality)
        output(-1_i);
    output(1_i);

    auto result = ++_imp->model_constraints;
    if (equality)
        ++_imp->model_constraints;
    return result;
}

auto Proof::integer_linear_le(const State &, const SumOf<Weighted<SimpleIntegerVariableID>> & lin, Integer val,
    optional<ReificationTerm> half_reif, bool equality)
    -> ProofLine
{
    if (_imp->opb_done)
        throw UnexpectedException{"proof has already started"};

    if (half_reif)
        overloaded{
            [&](const Literal & lit) { need_proof_variable(lit); },
            [&](const ProofFlag &) {}}
            .visit(*half_reif);

    _imp->opb << (equality ? "* linear eq" : "* linear le");

    for (const auto & [coeff, var] : lin.terms)
        _imp->opb << " " << coeff << "*" << debug_string(IntegerVariableID{var});
    _imp->opb << " <= " << val << '\n';

    auto output = [&](Integer multiplier) {
        using namespace gcs::innards::opb_utils;

        OPBExpression opb_expr;
        for (const auto & [coeff, var] : lin.terms) {
            auto bits = _imp->integer_variable_bits.find(var);
            if (bits != _imp->integer_variable_bits.end())
                for (auto & [bit_value, bit_name] : bits->second.second)
                    opb_expr.weighted_terms.emplace_back(multiplier * coeff * bit_value, bit_name);
            else {
                stringstream str;
                for (const auto & [coeff, var] : lin.terms)
                    str << " " << coeff << "*" << debug_string(IntegerVariableID{var});
                str << " <= " << val << '\n';
                throw UnexpectedException{"missing bits for " + str.str()};
            }
        }

        auto opb_ineq = opb_expr >= (multiplier * val);
        if (half_reif)
            visit([&](const auto & h) { opb_ineq = implied_by(opb_ineq, proof_variable(h)); }, *half_reif);

        _imp->opb << opb_ineq << " ;\n";
        ++_imp->model_constraints;
    };

    if (equality)
        output(1_i);
    output(-1_i);
    return _imp->model_constraints;
}

auto Proof::proof_variable(const Literal & lit) const -> const string &
{
    // This might need a design rethink: if we get a constant variable, turn it into either
    // true or false based upon its condition
    return overloaded{
        [&](const LiteralFromIntegerVariable & ilit) -> const string & {
            return overloaded{
                [&](const SimpleIntegerVariableID &) -> const string & {
                    auto it = _imp->direct_integer_variables.find(ilit);
                    if (it == _imp->direct_integer_variables.end())
                        throw ProofError("No variable exists for literal " + debug_string(lit));
                    return it->second;
                },
                [&](const ViewOfIntegerVariableID & view) -> const string & {
                    switch (ilit.op) {
                    case LiteralFromIntegerVariable::Operator::NotEqual:
                        return proof_variable(view.actual_variable != (view.negate_first ? -ilit.value + view.then_add : ilit.value - view.then_add));
                    case LiteralFromIntegerVariable::Operator::Equal:
                        return proof_variable(view.actual_variable == (view.negate_first ? -ilit.value + view.then_add : ilit.value - view.then_add));
                    case LiteralFromIntegerVariable::Operator::Less:
                        if (view.negate_first)
                            return proof_variable(view.actual_variable >= ilit.value - view.then_add + 1_i);
                        else
                            return proof_variable(view.actual_variable < (ilit.value - view.then_add));
                    case LiteralFromIntegerVariable::Operator::GreaterEqual:
                        if (view.negate_first)
                            return proof_variable(view.actual_variable < ilit.value - view.then_add + 1_i);
                        else
                            return proof_variable(view.actual_variable >= (ilit.value - view.then_add));
                    }
                    throw NonExhaustiveSwitch{};
                },
                [&](const ConstantIntegerVariableID &) -> const string & {
                    throw UnimplementedException{};
                }}
                .visit(ilit.var);
        },
        [&](const TrueLiteral &) -> const string & {
            throw UnimplementedException{};
        },
        [&](const FalseLiteral &) -> const string & {
            throw UnimplementedException{};
        }}
        .visit(lit);
}

auto Proof::proof_variable(const ProofFlag & flag) const -> const string &
{
    auto it = _imp->flags.find(pair{flag.index, flag.positive});
    if (it == _imp->flags.end())
        throw ProofError("Missing flag");
    return it->second;
}

auto Proof::need_proof_variable(const Literal & lit, const std::optional<bool> & work) -> void
{
    return overloaded{
        [&](const LiteralFromIntegerVariable & ilit) {
            return overloaded{
                [&](const SimpleIntegerVariableID & var) {
                    switch (ilit.op) {
                    case LiteralFromIntegerVariable::Operator::Equal:
                    case LiteralFromIntegerVariable::Operator::NotEqual:
                        need_direct_encoding_for(var, ilit.value, work);
                        break;
                    case LiteralFromIntegerVariable::Operator::Less:
                    case LiteralFromIntegerVariable::Operator::GreaterEqual:
                        need_gevar(var, ilit.value, work);
                        break;
                    }
                },
                [&](const ViewOfIntegerVariableID & view) {
                    switch (ilit.op) {
                    case LiteralFromIntegerVariable::Operator::NotEqual:
                        need_proof_variable(view.actual_variable != (view.negate_first ? -ilit.value + view.then_add : ilit.value - view.then_add), work);
                        break;
                    case LiteralFromIntegerVariable::Operator::Equal:
                        need_proof_variable(view.actual_variable == (view.negate_first ? -ilit.value + view.then_add : ilit.value - view.then_add), work);
                        break;
                    case LiteralFromIntegerVariable::Operator::Less:
                        if (view.negate_first)
                            need_proof_variable(view.actual_variable >= ilit.value - view.then_add + 1_i, work);
                        else
                            need_proof_variable(view.actual_variable < (ilit.value - view.then_add), work);
                        break;
                    case LiteralFromIntegerVariable::Operator::GreaterEqual:
                        if (view.negate_first)
                            need_proof_variable(view.actual_variable < ilit.value - view.then_add + 1_i, work);
                        else
                            need_proof_variable(view.actual_variable >= (ilit.value - view.then_add), work);
                        break;
                    }
                },
                [&](const ConstantIntegerVariableID &) {
                    throw UnimplementedException{};
                }}
                .visit(ilit.var);
        },
        [&](const TrueLiteral &) {
        },
        [&](const FalseLiteral &) {
        }}
        .visit(lit);
}

auto Proof::posting(const std::string & s) -> void
{
    if (_imp->opb_done)
        throw UnexpectedException{"proof has already started"};
    _imp->opb << "* constraint " << s << '\n';
}

auto Proof::solution(const State & state) -> void
{
    // _imp->proof << "* solution\n";
    push_work_queue(Work{"* solution\n"});

    for (auto & var : _imp->solution_variables)
        need_proof_variable(var == state(var));

    if (state.optional_minimise_variable()) {
        Integer obj_val = state(*state.optional_minimise_variable());
        need_proof_variable(*state.optional_minimise_variable() == obj_val);
        need_proof_variable(*state.optional_minimise_variable() < obj_val);
    }

    // _imp->proof << "# 0\n";
    push_work_queue(Work{"# 0\n"});

    // _imp->proof << (state.optional_minimise_variable() ? "o" : "v");
    push_work_queue(Work{state.optional_minimise_variable() ? "o" : "v"});

    for (auto & var : _imp->solution_variables)
        if ((! state.optional_minimise_variable()) || (var != *state.optional_minimise_variable())) {
            // _imp->proof << " " << proof_variable(var == state(var));
            push_work_queue(Work{" " + proof_variable(var == state(var))});
        }

    if (! state.optional_minimise_variable()) {
        // _imp->proof << '\n';
        push_work_queue(Work{"\n"});
        ++_imp->proof_line;
    }
    else {
        auto do_it = [&](const SimpleIntegerVariableID & var, Integer val) {
            // _imp->proof << " " << proof_variable(var == val);
            push_work_queue(Work{" " + proof_variable(var == val)});

            auto & [negative_bit_coeff, bit_vars] = _imp->integer_variable_bits.at(var);
            if (val.raw_value < 0) {
                for (auto & [coeff, var] : bit_vars) {
                    if (coeff < 0_i) {
                        // _imp->proof << " " << var;
                        push_work_queue(Work{" " + var});
                    }

                    else {
                        // _imp->proof << " " << (((val + negative_bit_coeff).raw_value & coeff.raw_value) ? "" : "~") << var;
                        push_work_queue(Work{(((val + negative_bit_coeff).raw_value & coeff.raw_value) ? " " : " ~") + var});
                    }
                }
            }
            else {
                for (auto & [coeff, var] : bit_vars) {
                    if (coeff < 0_i) {
                        // _imp->proof << " ~" << var;
                        push_work_queue(Work{" ~" + var});
                    }

                    else {
                        // _imp->proof << " " << ((val.raw_value & coeff.raw_value) ? "" : "~") << var;
                        push_work_queue(Work{((val.raw_value & coeff.raw_value) ? " " : " ~") + var});
                    }
                }
            }

            // _imp->proof << '\n';
            push_work_queue(Work{"\n"});

            ++_imp->proof_line;
        };

        overloaded{
            [&](const SimpleIntegerVariableID & var) {
                Integer obj_val = state(*state.optional_minimise_variable());
                do_it(var, obj_val);
                need_proof_variable(var < obj_val);
                // _imp->proof << "# 0\n";
                // _imp->proof << "u 1 " << proof_variable(var < obj_val) << " >= 1 ;\n";
                push_work_queue(Work{"# 0\nu 1 " + proof_variable(var < obj_val) + " >= 1 ;\n"});

                ++_imp->proof_line;
            },
            [&](const ConstantIntegerVariableID &) {
                throw UnimplementedException{};
            },
            [&](const ViewOfIntegerVariableID & var) {
                Integer obj_val = state(var.actual_variable);
                do_it(var.actual_variable, obj_val);
                auto lit = var < state(var);
                need_proof_variable(lit);
                // _imp->proof << "# 0\n";
                // _imp->proof << "u 1 " << proof_variable(lit) << " >= 1 ;\n";
                push_work_queue(Work{"# 0\nu 1 " + proof_variable(lit) + " >= 1 ;\n"});

                ++_imp->proof_line;
            }}
            .visit(*state.optional_minimise_variable());
    }

    // _imp->proof << "# " << _imp->active_proof_level << "\n";
    push_work_queue(Work{"# " + to_string(_imp->active_proof_level) + "\n"});
}

auto Proof::backtrack(const State & state) -> void
{
    // _imp->proof << "* backtracking\n";
    // _imp->proof << "u";
    push_work_queue(Work{"* backtracking\nu"});

    state.for_each_guess([&](const Literal & lit) {
        if (! is_literally_true(lit)) {
            // _imp->proof << " 1 " << proof_variable(! lit);
            push_work_queue(Work{" 1 " + proof_variable(! lit)});
        }
    });
    // _imp->proof << " >= 1 ;\n";
    push_work_queue(Work{" >= 1 ;\n"});
    ++_imp->proof_line;
}

auto Proof::assert_contradiction() -> void
{
    // _imp->proof << "* asserting contradiction\n";
    // _imp->proof << "u >= 1 ;\n";
    push_work_queue(Work{"* asserting contradiction\nu >= 1 ;\n"});

    ++_imp->proof_line;
    // _imp->proof << "c " << _imp->proof_line << " 0\n";
    push_work_queue(Work{"c " + to_string(_imp->proof_line) + " 0\n"});

    // this is mostly for tests: we haven't necessarily destroyed the
    // Problem before running the verifier.

    (*this).Stop();
    // (*this).joinThread();

    // _imp->proof << flush;   // doesn't work
}

auto Proof::infer(const State & state, const Literal & lit, const Justification & why) -> void
{
    // auto output_it = [&](const string & rule) {
    //     if (! is_literally_true(lit)) {
    //         // _imp->proof << rule;
    //         push_work_queue(Work{rule});

    //         state.for_each_guess([&](const Literal & lit) {
    //             if (! is_literally_true(lit)) {
    //                 // _imp->proof << " 1 " << proof_variable(! lit);
    //                 push_work_queue(Work{" 1 " + proof_variable(! lit)});
    //             }
    //         });
    //         if (! is_literally_false(lit)) {
    //             // _imp->proof << " 1 " << proof_variable(lit);
    //             push_work_queue(Work{" 1 " + proof_variable(lit)});
    //         }
    //         // _imp->proof << " >= 1 ;\n";
    //         push_work_queue(Work{" >= 1 ;\n"});

    //         ++_imp->proof_line;
    //     }
    // };

    vector<Literal> guesses_copy;
    vector<Literal> guesses = state.get_guesses();
    for (const auto & literal : guesses) {
        guesses_copy.push_back(std::visit([](const auto & value) -> Literal {
            return Literal(value);
        },
            literal));
    }

    vector<Literal> extra_proof_conditions_copy;
    for (const auto & literal : state.get_extra_proof_conditions()) {
        extra_proof_conditions_copy.push_back(std::visit([](const auto & value) -> Literal {
            return Literal(value);
        },
            literal));
    }

    // Literal lit_copy = std::visit(CopyVisitor{}, lit);
    Literal lit_copy = std::visit(
        [](const auto & value) -> Literal {
            return Literal(value);
        },
        lit);

    overloaded{
        [&]([[maybe_unused]] const JustifyUsingRUP & j) {
            std::cout << "JustifyUsingRUP" << std::endl;
        // need_proof_variable(lit_copy);
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            _imp->proof << "* RUP from " << j.where.file_name() << ":"
                        << j.where.line() << " in " << j.where.function_name() << '\n';
#endif
            // Proof::output_it("u", lit_copy, guesses_copy, extra_proof_conditions_copy);
            push_work_queue(Work{WorkJustifyUsingRUP{lit_copy, guesses_copy, extra_proof_conditions_copy}});
        },
        [&](const JustifyUsingAssertion &) {
            std::cout << "JustifyUsingAssertion" << std::endl;
            // need_proof_variable(lit_copy);
            // Proof::output_it("a", lit_copy, guesses_copy, extra_proof_conditions_copy);
            push_work_queue(Work{WorkJustifyUsingAssertion{lit_copy, guesses_copy, extra_proof_conditions_copy}});
        },
        [&](const JustifyExplicitly & x) {
            std::cout << "JustifyExplicitly" << std::endl;
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            _imp->proof << "* explicit from " << x.where.file_name() << ":"
                        << x.where.line() << " in " << x.where.function_name() << '\n';
#endif
            vector<ProofLine> to_delete;
            add_proof_steps(x, to_delete);
            // infer(state, lit_copy, JustifyUsingRUP{});
            need_proof_variable(lit_copy);
            Proof::output_it("u", lit_copy, guesses_copy, extra_proof_conditions_copy);
            delete_proof_lines(to_delete);
            // push_work_queue(Work{WorkJustifyExplicitly{x, lit_copy, guesses_copy, extra_proof_conditions_copy}});
        },
        [&](const Guess &) {
            std::cout << "JustifyGuess" << std::endl;
            if (! is_literally_true(lit_copy)) {
                // we need this because it'll show up in the trail later
                need_proof_variable(lit_copy);
                // _imp->proof << "* guessing " << proof_variable(lit) << ", decision stack is [";
                push_work_queue(Work{"* guessing " + proof_variable(lit_copy) + ", decision stack is ["});
                for_each_guess([&](const Literal & lit) {
                    if (! is_literally_true(lit)) {
                        // _imp->proof << " " << proof_variable(lit);
                        push_work_queue(Work{" " + proof_variable(lit)});
                    }
                },
                    guesses_copy, extra_proof_conditions_copy);
                // _imp->proof << " ]\n";
                push_work_queue(Work{" ]\n"});
            }
            // push_work_queue(Work{WorkGuess{lit_copy, guesses_copy, extra_proof_conditions_copy}});
        },

        [&](const NoJustificationNeeded &) {
        }}
        .visit(why);
}

auto Proof::emit_proof_line(const string & s) -> ProofLine
{
    // _imp->proof << s << '\n';
    push_work_queue(Work{s + "\n"});
    return ++_imp->proof_line;
}

auto Proof::emit_proof_comment(const string & s) -> void
{
    // _imp->proof << "* " << s << '\n';
    push_work_queue(Work{"* " + s + "\n"});
}

auto Proof::need_constraint_saying_variable_takes_at_least_one_value(IntegerVariableID var) -> ProofLine
{
    return overloaded{
        [&](const ConstantIntegerVariableID &) -> ProofLine {
            throw UnimplementedException{};
        },
        [&](const SimpleIntegerVariableID & var) -> ProofLine {
            auto result = _imp->variable_at_least_one_constraints.find(var);
            if (result == _imp->variable_at_least_one_constraints.end()) {
                auto [lower, upper] = _imp->bounds_for_gevars.at(var);
                for (Integer v = lower; v <= upper; ++v)
                    need_proof_variable(var == v);

                // _imp->proof << "# 0\n";
                push_work_queue(Work{"# 0\n"});

                // _imp->proof << "u ";
                push_work_queue(Work{"u "});

                for (Integer v = lower; v <= upper; ++v) {
                    // _imp->proof << "1 " << proof_variable(var == v) << " ";
                    push_work_queue(Work{"1 " + proof_variable(var == v) + " "});
                }

                // _imp->proof << ">= 1 ;\n";
                push_work_queue(Work{">= 1 ;\n"});

                _imp->variable_at_least_one_constraints.emplace(var, ++_imp->proof_line);

                // _imp->proof << "# " << _imp->active_proof_level << "\n";
                push_work_queue(Work{"# " + to_string(_imp->active_proof_level) + "\n"});

                result = _imp->variable_at_least_one_constraints.emplace(var, _imp->proof_line).first;
            }
            return result->second;
        },
        [&](const ViewOfIntegerVariableID & var) -> ProofLine {
            return need_constraint_saying_variable_takes_at_least_one_value(var.actual_variable);
        }}
        .visit(var);
}

auto Proof::enter_proof_level(int depth) -> void
{
    // _imp->proof << "# " << depth << '\n';
    push_work_queue(Work{"# " + to_string(depth) + "\n"});

    _imp->active_proof_level = depth;
}

auto Proof::forget_proof_level(int depth) -> void
{
    // _imp->proof << "w " << depth << '\n';
    push_work_queue(Work{"w " + to_string(depth) + "\n"});
}

auto Proof::trail_variables(const State & state, Integer coeff) -> string
{
    stringstream result;
    state.for_each_guess([&](const Literal & lit) {
        if (! is_literally_true(lit))
            result << " " << coeff << " " << proof_variable(! lit);
    });

    return result.str();
}

auto Proof::add_proof_steps(const JustifyExplicitly & x, vector<ProofLine> & to_delete) -> void
{
    x.add_proof_steps(*this, to_delete);
}

auto Proof::delete_proof_lines(const vector<ProofLine> & to_delete) -> void
{
    if (! to_delete.empty()) {
        stringstream line;
        line << "d";
        for (const auto & l : to_delete)
            line << " " << l;
        // _imp->proof << line.str() << '\n';
        push_work_queue(Work{line.str() + "\n"});
    }
}

auto Proof::has_bit_representation(const SimpleIntegerVariableID & var) const -> bool
{
    return _imp->integer_variable_bits.contains(var);
}

auto Proof::get_or_emit_pol_term_for_bound_in_bits(State & state, bool upper,
    const SimpleIntegerVariableID & var, Integer val)
    -> variant<ProofLine, string>
{
    if (! has_bit_representation(var))
        throw UnexpectedException{"variable does not have a bit representation"};

    auto it = _imp->line_for_bound_in_bits.back().find(tuple{upper, var, val});
    if (it != _imp->line_for_bound_in_bits.back().end())
        return it->second;

    stringstream step;
#ifdef GCS_TRACK_ALL_PROPAGATIONS
    step << "* need line for bound in bits " << (upper ? debug_string(var < val + 1_i) : debug_string(var >= val)) << "\n";
#endif
    step << "u";
    Integer big_number = 0_i;

    auto & [_, bit_vars] = _imp->integer_variable_bits.at(var);
    for (auto & [bit_coeff, bit_name] : bit_vars) {
        step << " " << (upper ? -bit_coeff : bit_coeff) << " " << bit_name;
        big_number += Integer{abs(bit_coeff)};
    }

    big_number += max(1_i, abs(val));
    step << trail_variables(state, big_number);

    if (upper)
        step << " >= " << -val << " ";
    else
        step << " >= " << val << " ";

    step << ";";

    auto line = emit_proof_line(step.str());
    _imp->line_for_bound_in_bits.back().emplace(tuple{upper, var, val}, line);
    return line;
}

auto Proof::new_guess() -> void
{
    _imp->line_for_bound_in_bits.emplace_back(_imp->line_for_bound_in_bits.back());
}

auto Proof::undo_guess() -> void
{
    _imp->line_for_bound_in_bits.pop_back();
}
