#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <algorithm>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <list>
#include <map>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include <nlohmann/json.hpp>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#endif

#include <util/overloaded.hh>

using namespace gcs;
using namespace gcs::innards;

using std::any_of;
using std::fstream;
using std::function;
using std::generator;
using std::ios;
using std::ios_base;
using std::list;
using std::make_unique;
using std::map;
using std::max;
using std::min;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::to_string;
using std::variant;
using std::vector;
using std::visit;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

struct NamesAndIDsTracker::Imp
{
    ProofModel * model = nullptr;
    ProofLogger * logger = nullptr;

    map<SimpleOrProofOnlyIntegerVariableID, ProofLine> variable_at_least_one_constraints;
    map<VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID>, XLiteral> variable_conditions_to_x;
    map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, vector<pair<Integer, XLiteral>>>> integer_variable_bits_to_size_and_proof_vars;
    map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, Integer>> integer_variable_definition_bounds;
    map<SimpleOrProofOnlyIntegerVariableID, map<Integer, pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>>>> gevars_that_exist;
    map<SimpleOrProofOnlyIntegerVariableID, map<Integer, pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>>>> eqvars_that_exist;

    map<ViewOfIntegerVariableID, ProofOnlySimpleIntegerVariableID> view_proof_only_vars;
    map<ProofOnlySimpleIntegerVariableID, ViewOfIntegerVariableID> view_proof_only_to_view;
    // For each registered view, the (LE-half, GE-half) ProofLine IDs of the
    // bit-vector link constraint emitted in need_view. The LE half is
    // `BinEnc(V) - s*BinEnc(X) <= c`, the GE half is `>= c`. Used by need_gevar
    // to pol-derive atom-level links from each V-atom to the corresponding
    // X-atom.
    map<ProofOnlySimpleIntegerVariableID, pair<ProofLine, ProofLine>> view_link_ids;

    // Reverse index: for each underlying variable, the proof-only IDs of
    // all views currently registered over it. Lets need_gevar /
    // need_direct_encoding_for on the X side back-emit the V-side atoms
    // (and thereby the V<->X link) when an X atom is introduced after a
    // view has been registered. When views are registered AFTER an X atom
    // already exists, need_view itself backfills via this map's setup.
    std::map<SimpleIntegerVariableID, std::vector<ProofOnlySimpleIntegerVariableID>> views_of_variable;

    // For each V-form proof line that has a derived deview-form, the
    // corresponding deview-form line. Lookup via deviewed_line_for.
    map<ProofLine, ProofLine> deviewed_line_by_v_form;

    map<ProofFlag, XLiteral> flags;

    map<SimpleOrProofOnlyIntegerVariableID, string> id_names;
    map<XLiteral, string> xlits_to_verbose_names;
    map<ProofFlag, string> flag_names;

    list<function<auto(ProofLogger * const)->void>> delayed_proof_steps;

    bool use_friendly_names = true;
    unsigned model_variables = 0;
    long long next_xliteral_nr = 0;

    optional<fstream> variables_map_file;
    string variables_map_file_name;
    bool first_varmap_entry = true;
    bool finalised = false;
    bool verbose_names;
};

NamesAndIDsTracker::NamesAndIDsTracker(const ProofOptions & proof_options) :
    _imp(make_unique<Imp>())
{
    _imp->verbose_names = proof_options.verbose_names;

    if (proof_options.proof_file_names.variables_map_file) {
        _imp->variables_map_file_name = *proof_options.proof_file_names.variables_map_file;
        _imp->variables_map_file.emplace();
        try {
            _imp->variables_map_file->exceptions(ios::failbit | ios::badbit);
            _imp->variables_map_file->open(_imp->variables_map_file_name, ios::out);
            *_imp->variables_map_file << "{\n";
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }
}

NamesAndIDsTracker::~NamesAndIDsTracker()
{
    if (_imp->variables_map_file && ! _imp->finalised && std::uncaught_exceptions() == 0) {
        print(stderr, "NamesAndIDsTracker destroyed without calling finalise()\n");
        std::abort();
    }
}

auto NamesAndIDsTracker::finalise() -> void
{
    _imp->finalised = true;
    if (_imp->variables_map_file) {
        try {
            *_imp->variables_map_file << "\n}\n";
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }
}

auto NamesAndIDsTracker::emit_proof_line_now_or_at_start(const function<auto(ProofLogger * const)->void> & func) -> void
{
    if (_imp->logger)
        func(_imp->logger);
    else
        _imp->delayed_proof_steps.push_back(func);
}

auto NamesAndIDsTracker::switch_from_model_to_proof(ProofLogger * const logger) -> void
{
    _imp->model = nullptr;
    _imp->logger = logger;
}

auto NamesAndIDsTracker::emit_delayed_proof_steps() -> void
{
    for (const auto & step : _imp->delayed_proof_steps)
        step(_imp->logger);
    _imp->delayed_proof_steps.clear();
}

auto NamesAndIDsTracker::start_writing_model(ProofModel * const model) -> void
{
    _imp->model = model;
}

auto NamesAndIDsTracker::associate_condition_with_xliteral(
    const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond, const XLiteral & x) -> void
{
    _imp->variable_conditions_to_x.emplace(cond, x);
}

auto NamesAndIDsTracker::track_variable_takes_at_least_one_value(const SimpleOrProofOnlyIntegerVariableID & id, ProofLine line) -> void
{
    _imp->variable_at_least_one_constraints.emplace(id, line);
}

auto NamesAndIDsTracker::need_constraint_saying_variable_takes_at_least_one_value(IntegerVariableID var) -> ProofLine
{
    return overloaded{
        [&](const ConstantIntegerVariableID &) -> ProofLine {
            throw UnimplementedException{};
        },
        [&](const SimpleIntegerVariableID & var) -> ProofLine {
            auto result = _imp->variable_at_least_one_constraints.find(var);
            if (result == _imp->variable_at_least_one_constraints.end()) {
                WPBSum al1s;
                auto [lower, upper] = _imp->integer_variable_definition_bounds.at(var);
                for (Integer v = lower; v <= upper; ++v)
                    al1s += 1_i * (var == v);

                auto line = _imp->logger->emit_rup_proof_line(al1s >= 1_i, ProofLevel::Top);
                result = _imp->variable_at_least_one_constraints.emplace(var, line).first;
            }
            return result->second;
        },
        [&](const ViewOfIntegerVariableID & var) -> ProofLine {
            // For a registered view, emit AL1 in V-form so it cancels
            // cleanly against AM1s that already reference V-form atoms
            // (those go through need_pol_item_defining_literal, which
            // returns the V's eqvar when the view is registered). Falling
            // back to the X-form AL1 here used to leave Hall-set proofs in
            // gac_all_different unable to RUP their conclusion: the AL1
            // contributed `+x[eq w]` terms while AM1s contributed
            // `-p_view[eq W]` terms, with no shared atoms to cancel.
            if (auto v_id = find_view(var)) {
                auto result = _imp->variable_at_least_one_constraints.find(*v_id);
                if (result == _imp->variable_at_least_one_constraints.end()) {
                    WPBSum al1s;
                    auto [lower, upper] = _imp->integer_variable_definition_bounds.at(*v_id);
                    for (Integer v = lower; v <= upper; ++v)
                        al1s += 1_i * (*v_id == v);

                    auto line = _imp->logger->emit_rup_proof_line(al1s >= 1_i, ProofLevel::Top);
                    result = _imp->variable_at_least_one_constraints.emplace(*v_id, line).first;
                }
                return result->second;
            }
            return need_constraint_saying_variable_takes_at_least_one_value(var.actual_variable);
        }}
        .visit(var);
}

auto NamesAndIDsTracker::need_pol_item_defining_literal(const IntegerVariableCondition & cond) -> variant<ProofLine, XLiteral>
{
    return overloaded{
        [&](const ConstantIntegerVariableID &) -> variant<ProofLine, XLiteral> {
            throw UnimplementedException{};
        },
        [&](const SimpleIntegerVariableID & var) -> variant<ProofLine, XLiteral> {
            switch (cond.op) {
                using enum VariableConditionOperator;
            case GreaterEqual:
                need_gevar(var, cond.value);
                return _imp->gevars_that_exist.at(var).at(cond.value).first;
            case Less:
                need_gevar(var, cond.value);
                return _imp->gevars_that_exist.at(var).at(cond.value).second;
            case Equal:
                need_direct_encoding_for(var, cond.value);
                return _imp->eqvars_that_exist.at(var).at(cond.value).first;
            case NotEqual:
                need_direct_encoding_for(var, cond.value);
                return _imp->eqvars_that_exist.at(var).at(cond.value).second;
            }
            throw NonExhaustiveSwitch{};
        },
        [&](const ViewOfIntegerVariableID & var) -> variant<ProofLine, XLiteral> {
            // If the view's been registered, V's atoms have proper Defs over
            // BinEnc(V) and the pol-item path looks just like a simple
            // variable's. The Equal/NotEqual throws below only fire on the
            // deview fallback for views first seen during proof logging.
            if (auto v_id = find_view(var)) {
                switch (cond.op) {
                    using enum VariableConditionOperator;
                case GreaterEqual:
                    need_gevar(*v_id, cond.value);
                    return _imp->gevars_that_exist.at(*v_id).at(cond.value).first;
                case Less:
                    need_gevar(*v_id, cond.value);
                    return _imp->gevars_that_exist.at(*v_id).at(cond.value).second;
                case Equal:
                    need_direct_encoding_for(*v_id, cond.value);
                    return _imp->eqvars_that_exist.at(*v_id).at(cond.value).first;
                case NotEqual:
                    need_direct_encoding_for(*v_id, cond.value);
                    return _imp->eqvars_that_exist.at(*v_id).at(cond.value).second;
                }
                throw NonExhaustiveSwitch{};
            }
            switch (cond.op) {
                using enum VariableConditionOperator;
            case GreaterEqual:
                if (var.negate_first)
                    return need_pol_item_defining_literal(var.actual_variable < -(cond.value - var.then_add) + 1_i);
                else
                    return need_pol_item_defining_literal(var.actual_variable >= cond.value - var.then_add);
            case Less:
                if (var.negate_first)
                    return need_pol_item_defining_literal(var.actual_variable >= -(cond.value - var.then_add) + 1_i);
                else
                    return need_pol_item_defining_literal(var.actual_variable < cond.value - var.then_add);
            case Equal:
                throw UnimplementedException{};
            case NotEqual:
                throw UnimplementedException{};
            }
            throw NonExhaustiveSwitch{};
        }}
        .visit(cond.var);
}

auto NamesAndIDsTracker::create_literals_for_introduced_variable_value(
    SimpleIntegerVariableID id, Integer val, const string & name) -> void
{
    track_variable_name(id, to_string(id.index) + "intr_" + name); // hack!
    auto x = allocate_xliteral_meaning(id, EqualsOrGreaterEqual::Equals, val);
    _imp->variable_conditions_to_x.emplace(id == val, x);
    _imp->variable_conditions_to_x.emplace(id != val, ! x);
}

auto NamesAndIDsTracker::need_proof_name(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) -> void
{
    switch (cond.op) {
        using enum VariableConditionOperator;
    case Equal:
    case NotEqual:
        need_direct_encoding_for(cond.var, cond.value);
        break;
    case Less:
    case GreaterEqual:
        need_gevar(cond.var, cond.value);
        break;
    }
}

auto NamesAndIDsTracker::need_all_proof_names_in(const SumOf<Weighted<PseudoBooleanTerm>> & sum) -> void
{
    for (auto & [_, v] : sum.terms)
        overloaded{
            [&](const ProofLiteral & lit) {
                overloaded{
                    [&](const TrueLiteral &) {},
                    [&](const FalseLiteral &) {},
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) {
                        need_proof_name(cond);
                    }}
                    .visit(simplify_literal(*this, lit));
            },
            [&](const ProofFlag &) {},
            [&](const IntegerVariableID & var) {
                // Opportunistically register view bit vectors during model
                // writing. need_view can only introduce a view while the
                // model is being written (it throws during the proof-logging
                // phase), so this is gated on _imp->model.
                if (_imp->model)
                    if (auto view = std::get_if<ViewOfIntegerVariableID>(&var))
                        static_cast<void>(need_view(*view));
            },
            [&](const ProofOnlySimpleIntegerVariableID &) {},
            [&](const ProofBitVariable &) {}}
            .visit(v);
}

auto NamesAndIDsTracker::need_all_proof_names_in(const Literals & lits) -> void
{
    for (auto & lit : lits)
        overloaded{
            [&](const TrueLiteral &) {},
            [&](const FalseLiteral &) {},
            [&]<typename T_>(const VariableConditionFrom<T_> & cond) {
                need_proof_name(cond);
            }}
            .visit(simplify_literal(*this, lit));
}

auto NamesAndIDsTracker::need_all_proof_names_in(const HalfReifyOnConjunctionOf & h) -> void
{
    for (auto & term : h)
        overloaded{
            [&](const ProofLiteral & lit) {
                overloaded{
                    [&](const TrueLiteral &) {},
                    [&](const FalseLiteral &) {},
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) {
                        need_proof_name(cond);
                    }}
                    .visit(simplify_literal(*this, lit));
            },
            [&](const ProofFlag &) {},
            [&](const ProofBitVariable &) {}}
            .visit(term);
}

auto NamesAndIDsTracker::negative_bit_coefficient(const SimpleOrProofOnlyIntegerVariableID & id) -> Integer
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(id);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");
    return it->second.first;
}

auto NamesAndIDsTracker::each_bit(const SimpleOrProofOnlyIntegerVariableID & id)
    -> generator<pair<Integer, XLiteral>>
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(id);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");
    for (auto & [c, n] : it->second.second)
        co_yield pair{c, n};
}

auto NamesAndIDsTracker::get_bit(const gcs::innards::SimpleOrProofOnlyIntegerVariableID & var, Integer position) -> pair<Integer, XLiteral>
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(var);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");

    return it->second.second.at(position.as_index());
}

auto NamesAndIDsTracker::get_bit(const ProofBitVariable & bit) -> pair<Integer, XLiteral>
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(bit.for_var);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");

    auto bit_data = it->second.second.at(bit.position.as_index());

    if (! bit.positive)
        bit_data.second.negated = ! bit_data.second.negated;

    return bit_data;
}

auto NamesAndIDsTracker::num_bits(const gcs::innards::SimpleOrProofOnlyIntegerVariableID & var) -> Integer
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(var);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");

    return Integer(it->second.second.size());
}

auto NamesAndIDsTracker::track_bits(const SimpleOrProofOnlyIntegerVariableID & id, Integer negative_coeff,
    const vector<pair<Integer, XLiteral>> & bit_vars) -> void
{
    _imp->integer_variable_bits_to_size_and_proof_vars.emplace(id, pair{negative_coeff, bit_vars});
}

auto NamesAndIDsTracker::allocate_flag_index() -> unsigned long long
{
    return _imp->flags.size() / 2;
}

auto NamesAndIDsTracker::track_eqvar(SimpleIntegerVariableID id, Integer val,
    const pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>> & names) -> void
{
    _imp->eqvars_that_exist[id].emplace(val, names);
}

auto NamesAndIDsTracker::track_gevar(SimpleIntegerVariableID id, Integer val,
    const pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>> & names) -> void
{
    _imp->gevars_that_exist[id].emplace(val, names);
}

auto NamesAndIDsTracker::need_direct_encoding_for(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> void
{
    if (_imp->variable_conditions_to_x.contains(id == v))
        return;

    auto eqvar = allocate_xliteral_meaning(id, EqualsOrGreaterEqual::Equals, v);
    _imp->variable_conditions_to_x.emplace(id == v, eqvar);
    _imp->variable_conditions_to_x.emplace(id != v, ! eqvar);

    auto bounds = _imp->integer_variable_definition_bounds.find(id);
    ProofLine forwards_line, reverse_line;
    if (bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.first == v) {
        // it's a lower bound
        if (_imp->logger) {
            visit([&](const auto & id) {
                auto [_f_line, _r_line] = _imp->logger->emit_red_proof_lines_reifying(WPBSum{} + 1_i * ! (id >= (v + 1_i)) >= 1_i,
                    id == v, ProofLevel::Top);
                forwards_line = _f_line;
                reverse_line = _r_line;
            },
                id);
        }
        else {
            visit([&](const auto & id) {
                forwards_line = *_imp->model->add_constraint(WPBSum{} + 1_i * ! (id >= (v + 1_i)) >= 1_i, {{id == v}});
                reverse_line = *_imp->model->add_constraint(WPBSum{} + 1_i * (id >= (v + 1_i)) >= 1_i, {{id != v}});
            },
                id);
            ++_imp->model_variables;
        }
    }
    else if (bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.second == v) {
        // it's an upper bound
        if (_imp->logger) {
            visit([&](const auto & id) {
                auto [_f_line, _r_line] = _imp->logger->emit_red_proof_lines_reifying(WPBSum{} + 1_i * (id >= v) >= 1_i, id == v, ProofLevel::Top);
                forwards_line = _f_line;
                reverse_line = _r_line;
            },
                id);
        }
        else {
            visit([&](const auto & id) {
                forwards_line = *_imp->model->add_constraint(WPBSum{} + 1_i * (id >= v) >= 1_i, {{id == v}});
                reverse_line = *_imp->model->add_constraint(WPBSum{} + 1_i * ! (id >= v) >= 1_i, {{id != v}});
            },
                id);
            ++_imp->model_variables;
        }
    }
    else {
        // neither a lower nor an upper bound
        if (_imp->logger)
            visit([&](const auto & id) {
                auto [_f_line, _r_line] = _imp->logger->emit_red_proof_lines_reifying(
                    WPBSum{} + (1_i * (id >= v)) + (1_i * ! (id > v)) >= 2_i,
                    id == v, ProofLevel::Top);
                forwards_line = _f_line;
                reverse_line = _r_line;
            },
                id);
        else {
            visit([&](const auto & id) {
                forwards_line = *_imp->model->add_constraint(WPBSum{} + 1_i * (id >= v) + 1_i * ! (id > v) >= 2_i, {{id == v}});
                reverse_line = *_imp->model->add_constraint(WPBSum{} + 1_i * ! (id >= v) + 1_i * (id > v) >= 1_i, {{id != v}});
            },
                id);
            ++_imp->model_variables;
        }
    }

    _imp->eqvars_that_exist[id].emplace(v, pair{forwards_line, reverse_line});

    // If `id` is a view's proof-only var, eagerly emit the
    // eq-atom-level link `V=v <=> X=k_x` as two RUP lines. The GE-atom
    // links + the V- and X-side eq Defs are already in F at this point
    // (need_gevar(V,v), need_gevar(V,v+1), and need_direct_encoding_for(X,k_x)
    // are all called by this point), so each direction is UP-closable:
    //
    //   ~V=v OR X=k_x:  V=v UP-derives V>=v and ~V>=v+1 (eq fwd),
    //     then x_cond and ~x_cond+1 via GE links, then X=k_x by Def(X=k_x)
    //     reverse fed with both sides forced -- conflict with assumed ~X=k_x.
    //   ~X=k_x OR V=v:  symmetric.
    //
    // Without these eq-atom links, propagator-derived V<->Y lemmas combined
    // with X-atom guesses from search couldn't UP-chain V=v <-> X=k_x, and
    // backtrack-from-guess Bt verifications stalled with several remaining
    // values for Y.
    if (auto pid_ptr = std::get_if<ProofOnlySimpleIntegerVariableID>(&id)) {
        auto view_it = _imp->view_proof_only_to_view.find(*pid_ptr);
        if (view_it != _imp->view_proof_only_to_view.end()) {
            const auto & view = view_it->second;
            // V := s*X + c, V=v <=> X = (v-c)/s.
            //   s=+1: X = v - c.
            //   s=-1: X = c - v.
            Integer x_threshold = view.negate_first ? view.then_add - v : v - view.then_add;
            need_direct_encoding_for(view.actual_variable, x_threshold);

            ProofVariableCondition v_cond{*pid_ptr, VariableConditionOperator::Equal, v};
            IntegerVariableID x_var{view.actual_variable};
            auto x_cond = (x_var == x_threshold);
            emit_proof_line_now_or_at_start([v_cond, x_cond](ProofLogger * const logger) {
                logger->emit_rup_proof_line(WPBSum{} + 1_i * ! v_cond + 1_i * x_cond >= 1_i, ProofLevel::Top);
                logger->emit_rup_proof_line(WPBSum{} + 1_i * ! x_cond + 1_i * v_cond >= 1_i, ProofLevel::Top);
            });
        }
    }

    // Reverse direction: see the matching block in need_gevar above.
    if (auto sid_ptr = std::get_if<SimpleIntegerVariableID>(&id)) {
        if (auto it = _imp->views_of_variable.find(*sid_ptr); it != _imp->views_of_variable.end()) {
            auto views_copy = it->second;
            for (const auto & view_pid : views_copy) {
                const auto & view = _imp->view_proof_only_to_view.at(view_pid);
                Integer v_value = view.negate_first ? view.then_add - v : v + view.then_add;
                need_direct_encoding_for(view_pid, v_value);
            }
        }
    }
}

auto NamesAndIDsTracker::need_gevar(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> void
{
    if (_imp->variable_conditions_to_x.contains(id >= v))
        return;

    auto gevar = allocate_xliteral_meaning(id, EqualsOrGreaterEqual::GreaterEqual, v);
    _imp->variable_conditions_to_x.emplace(id >= v, gevar);
    _imp->variable_conditions_to_x.emplace(id < v, ! gevar);

    // gevar -> bits
    if (_imp->logger) {
        _imp->gevars_that_exist[id].emplace(v, visit([&](const auto & id) {
            return _imp->logger->emit_red_proof_lines_reifying(WPBSum{} + (1_i * id) >= v, id >= v, ProofLevel::Top);
        },
                                                   id));
    }
    else {
        // Label the two halves @i[name][ge<v>][f]/[r] to match cake_pb_cp, but
        // only where it is safe: a real (non-proof-only) variable, a name without
        // `[` (vector names nest brackets the @label parser rejects), and v >= 0
        // (a negative v would put a `-` in the role). The first emitted half (the
        // id>=v reif, carrying ~ge..) is cake's [r]; the second is [f].
        const auto & name = name_of(id);
        bool can_label = std::holds_alternative<SimpleIntegerVariableID>(id) && name.find('[') == string::npos && v >= 0_i;
        string ge_label = can_label ? "i[" + name + "][ge" + to_string(v.raw_value) + "]" : "";
        _imp->gevars_that_exist[id].emplace(v, visit([&](const auto & vid) -> pair<ProofLine, ProofLine> {
            if (can_label)
                return pair{
                    _imp->model->add_labelled_constraint(ge_label + "[r]", WPBSum{} + (1_i * vid) >= v, {{vid >= v}}).value(),
                    _imp->model->add_labelled_constraint(ge_label + "[f]", WPBSum{} + (-1_i * vid) >= -v + 1_i, {{vid < v}}).value()};
            else
                return pair{
                    _imp->model->add_constraint(WPBSum{} + (1_i * vid) >= v, {{vid >= v}}).value(),
                    _imp->model->add_constraint(WPBSum{} + (-1_i * vid) >= -v + 1_i, {{vid < v}}).value()};
        },
                                                   id));
        ++_imp->model_variables;
    }

    // is it a bound?
    auto bounds = _imp->integer_variable_definition_bounds.find(id);

    // lower?
    if (bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.first >= v) {
        if (_imp->logger)
            visit([&](auto id) { _imp->logger->emit_rup_proof_line(WPBSum{} + 1_i * (id >= v) >= 1_i, ProofLevel::Top); }, id);
        else
            visit([&](auto id) { _imp->model->add_constraint(WPBSum{} + 1_i * (id >= v) >= 1_i); }, id);
    }

    // upper?
    if (bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.second < v) {
        if (_imp->logger)
            visit([&](auto id) { _imp->logger->emit_rup_proof_line(WPBSum{} + 1_i * ! (id >= v) >= 1_i, ProofLevel::Top); }, id);
        else
            visit([&](auto id) { _imp->model->add_constraint(WPBSum{} + 1_i * ! (id >= v) >= 1_i); }, id);
    }

    auto & other_gevars = _imp->gevars_that_exist.at(id);
    auto this_gevar = other_gevars.find(v);
    auto higher_gevar = next(this_gevar);

    auto make_pol_chain_line = [&](IntegerVariableCondition cond1, IntegerVariableCondition cond2) -> string {
        PolBuilder b;
        b.add_for_literal(*this, ! cond1)
            .add_for_literal(*this, ! cond2)
            .saturate();
        return b.str();
    };

    // implied by the next highest gevar, if there is one?
    if (higher_gevar != other_gevars.end()) {
        overloaded{
            [&](const ProofOnlySimpleIntegerVariableID & id) {
                auto chain_con = WPBSum{} + (1_i * (id >= v)) + (1_i * ! (id >= higher_gevar->first)) >= 1_i;
                emit_proof_line_now_or_at_start([c = chain_con](ProofLogger * const logger) { logger->emit_rup_proof_line(c, ProofLevel::Top); });
            },
            [&](const SimpleIntegerVariableID & id) {
                auto pol_line = make_pol_chain_line(id >= v, ! (id >= higher_gevar->first));
                emit_proof_line_now_or_at_start([p = pol_line](ProofLogger * const logger) { logger->emit_proof_line(p, ProofLevel::Top); });
            }}
            .visit(id);
    }

    // implies the next lowest gevar, if there is one?
    if (this_gevar != other_gevars.begin()) {
        overloaded{
            [&](const ProofOnlySimpleIntegerVariableID & id) {
                auto chain_con = WPBSum{} + (1_i * (id >= prev(this_gevar)->first)) + (1_i * ! (id >= v)) >= 1_i;
                emit_proof_line_now_or_at_start([c = chain_con](ProofLogger * const logger) { logger->emit_rup_proof_line(c, ProofLevel::Top); });
            },
            [&](const SimpleIntegerVariableID & id) {
                auto pol_line = make_pol_chain_line(id >= prev(this_gevar)->first, ! (id >= v));
                emit_proof_line_now_or_at_start([p = pol_line](ProofLogger * const logger) { logger->emit_proof_line(p, ProofLevel::Top); });
            }}
            .visit(id);
    }

    // If `id` is a view's proof-only var, eagerly pol-derive the
    // atom-level link to the corresponding X-atom so propagator inferences
    // that mix V-atoms (from view literals via simplify_literal) and X-atoms
    // (from search guesses or other propagator inferences) can UP across
    // them without needing to case-split through the bit-vector link
    // alone. Two pol lines per V-atom — one for each direction of the iff:
    //
    //   D1: ~v>=k OR x_cond >= 1   = (v>=k -> x_cond)
    //   D2: ~x_cond OR v>=k >= 1   = (x_cond -> v>=k)
    //
    // where x_cond = (X >= v-c) for s=+1 and x_cond = ~(X >= c-v+1) for s=-1.
    //
    // Both directions sum three constraints whose BinEnc terms cancel
    // exactly, leaving an at-least-one over the two atom literals after
    // saturation. The choice of fwd vs rev for the X-atom Def flips with s:
    //   s=+1: D1 uses Def(v) fwd + LE + Def(x) rev; D2 uses rev + GE + fwd.
    //   s=-1: D1 uses Def(v) fwd + LE + Def(x) fwd; D2 uses rev + GE + rev.
    //
    // Both lines queued via emit_proof_line_now_or_at_start so they land at
    // the top of the proof, alongside the standard order-encoding chain
    // links, rather than as extra OPB axioms.
    if (auto pid_ptr = std::get_if<ProofOnlySimpleIntegerVariableID>(&id)) {
        auto view_it = _imp->view_proof_only_to_view.find(*pid_ptr);
        if (view_it != _imp->view_proof_only_to_view.end()) {
            const auto & view = view_it->second;
            Integer x_threshold = view.negate_first ? view.then_add - v + 1_i : v - view.then_add;
            need_gevar(view.actual_variable, x_threshold);

            auto v_defs = _imp->gevars_that_exist[id].at(v);
            auto x_defs = _imp->gevars_that_exist[SimpleOrProofOnlyIntegerVariableID{view.actual_variable}].at(x_threshold);
            auto link = _imp->view_link_ids.at(*pid_ptr);
            auto * v_fwd_line = std::get_if<ProofLine>(&v_defs.first);
            auto * v_rev_line = std::get_if<ProofLine>(&v_defs.second);
            auto * x_fwd_line = std::get_if<ProofLine>(&x_defs.first);
            auto * x_rev_line = std::get_if<ProofLine>(&x_defs.second);
            if (v_fwd_line && v_rev_line && x_fwd_line && x_rev_line) {
                bool neg = view.negate_first;
                ProofLine d1_x = neg ? *x_fwd_line : *x_rev_line;
                ProofLine d2_x = neg ? *x_rev_line : *x_fwd_line;
                PolBuilder b1;
                b1.add(*v_fwd_line).add(link.first).add(d1_x).saturate();
                PolBuilder b2;
                b2.add(*v_rev_line).add(link.second).add(d2_x).saturate();
                auto pol1 = b1.str();
                auto pol2 = b2.str();
                emit_proof_line_now_or_at_start([pol1, pol2](ProofLogger * const logger) {
                    logger->emit_proof_line(pol1, ProofLevel::Top);
                    logger->emit_proof_line(pol2, ProofLevel::Top);
                });
            }
        }
    }

    // Reverse direction: if `id` is a bare underlying variable that has
    // views registered over it, recursively trigger the matching V_ge
    // atom for each view. The V-side need_gevar then runs the link
    // emission above. Without this, an X atom introduced before any V
    // atom of the same value would never get a link in F.
    if (auto sid_ptr = std::get_if<SimpleIntegerVariableID>(&id)) {
        if (auto it = _imp->views_of_variable.find(*sid_ptr); it != _imp->views_of_variable.end()) {
            auto views_copy = it->second;
            for (const auto & view_pid : views_copy) {
                const auto & view = _imp->view_proof_only_to_view.at(view_pid);
                Integer v_value = view.negate_first ? view.then_add - v + 1_i : v + view.then_add;
                need_gevar(view_pid, v_value);
            }
        }
    }
}

auto NamesAndIDsTracker::need_view(const ViewOfIntegerVariableID & view) -> ProofOnlySimpleIntegerVariableID
{
    if (auto it = _imp->view_proof_only_vars.find(view); it != _imp->view_proof_only_vars.end())
        return it->second;

    if (! _imp->model)
        throw UnimplementedException{
            "need_view: view introduction during proof-logging phase is not yet supported"};

    auto bounds_it = _imp->integer_variable_definition_bounds.find(view.actual_variable);
    if (bounds_it == _imp->integer_variable_definition_bounds.end())
        throw ProofError{"need_view: underlying variable's bounds are not registered"};
    auto [x_lo, x_hi] = bounds_it->second;

    auto [v_lo, v_hi] = view.negate_first
        ? pair{-x_hi + view.then_add, -x_lo + view.then_add}
        : pair{x_lo + view.then_add, x_hi + view.then_add};

    string name = "view_of_" + name_of(view.actual_variable);
    if (view.negate_first)
        name = "neg_" + name;
    if (view.then_add != 0_i)
        name += "_plus_" + to_string(view.then_add.raw_value);

    auto v_id = _imp->model->create_proof_only_integer_variable(
        v_lo, v_hi, name, IntegerVariableProofRepresentation::Bits);

    Integer s_coeff = view.negate_first ? -1_i : 1_i;
    auto [link_le, link_ge] = _imp->model->add_constraint(StringLiteral{"view link"}, StringLiteral{"definitional"},
        WPBSum{} + 1_i * v_id + (-s_coeff) * view.actual_variable == view.then_add);

    _imp->view_proof_only_vars.emplace(view, v_id);
    _imp->view_proof_only_to_view.emplace(v_id, view);
    _imp->view_link_ids.emplace(v_id, pair{link_le.value(), link_ge.value()});
    _imp->views_of_variable[view.actual_variable].push_back(v_id);

    // Backfill: if X atoms already exist when this view is registered,
    // trigger the matching V atoms now so the V<->X link is emitted for
    // them. (Atoms introduced later go via the X-side hook in need_gevar /
    // need_direct_encoding_for.) Copy the X-side maps before iterating
    // because the V-side need_* calls add entries to other maps and may
    // recurse back through need_gevar(X, ...), which is a no-op for
    // already-existing atoms but would invalidate iterators if it weren't.
    SimpleOrProofOnlyIntegerVariableID x_key{view.actual_variable};
    if (auto it = _imp->gevars_that_exist.find(x_key); it != _imp->gevars_that_exist.end()) {
        auto x_atoms = it->second;
        for (const auto & [k, _] : x_atoms) {
            Integer v_value = view.negate_first ? view.then_add - k + 1_i : k + view.then_add;
            need_gevar(v_id, v_value);
        }
    }
    if (auto it = _imp->eqvars_that_exist.find(x_key); it != _imp->eqvars_that_exist.end()) {
        auto x_atoms = it->second;
        for (const auto & [k, _] : x_atoms) {
            Integer v_value = view.negate_first ? view.then_add - k : k + view.then_add;
            need_direct_encoding_for(v_id, v_value);
        }
    }

    return v_id;
}

auto NamesAndIDsTracker::find_view(const ViewOfIntegerVariableID & view) const -> optional<ProofOnlySimpleIntegerVariableID>
{
    if (auto it = _imp->view_proof_only_vars.find(view); it != _imp->view_proof_only_vars.end())
        return it->second;
    return std::nullopt;
}

auto NamesAndIDsTracker::register_deviewed_line(const ProofLine & v_form_line, const ProofLine & deviewed_line) -> void
{
    _imp->deviewed_line_by_v_form.emplace(v_form_line, deviewed_line);
}

auto NamesAndIDsTracker::deviewed_line_for(const ProofLine & line) const -> ProofLine
{
    if (auto it = _imp->deviewed_line_by_v_form.find(line); it != _imp->deviewed_line_by_v_form.end())
        return it->second;
    return line;
}

auto NamesAndIDsTracker::view_link_lines_for(const ProofOnlySimpleIntegerVariableID & view_proof_id) const -> pair<ProofLine, ProofLine>
{
    auto it = _imp->view_link_ids.find(view_proof_id);
    if (it == _imp->view_link_ids.end())
        throw ProofError{"view_link_lines_for: no link recorded for this proof-only var"};
    return it->second;
}

auto NamesAndIDsTracker::derive_deviewed_form_for(const ProofLine & v_form_line,
    const SumOf<Weighted<PseudoBooleanTerm>> & lhs,
    bool le_half) -> void
{
    // Walk the lhs terms and collect, for each view appearance, the
    // (opb_form_coefficient, view_proof_id) pair. opb_form_coefficient is
    // the WPBSum coefficient with sign flipped if le_half is true (since
    // emit_inequality_to negates the LE half on emission to land in
    // PB >= normal form).
    struct ViewContribution
    {
        ProofOnlySimpleIntegerVariableID view_proof_id;
        Integer opb_form_coefficient;
    };
    vector<ViewContribution> view_contributions;

    for (const auto & [w, v] : lhs.terms) {
        if (0_i == w)
            continue;
        if (auto var = std::get_if<IntegerVariableID>(&v)) {
            // Path 1: propagator-passed `IntegerVariableID` holding a view.
            if (auto view = std::get_if<ViewOfIntegerVariableID>(var)) {
                if (auto v_proof_id = find_view(*view)) {
                    Integer opb_coeff = le_half ? -w : w;
                    view_contributions.push_back({*v_proof_id, opb_coeff});
                }
            }
        }
        else if (auto proof_only = std::get_if<ProofOnlySimpleIntegerVariableID>(&v)) {
            // Path 2: framework-emitted constraint over a view's proof-only
            // var (e.g. Def(v>=k) in `need_gevar`). Treat the proof-only var
            // term the same way as a view-bearing term so propagators that
            // reference Def lines via `need_pol_item_defining_literal` get a
            // deview-form that puts the Def in X-form.
            if (_imp->view_proof_only_to_view.contains(*proof_only)) {
                Integer opb_coeff = le_half ? -w : w;
                view_contributions.push_back({*proof_only, opb_coeff});
            }
        }
    }

    if (view_contributions.empty())
        return;

    // Build the pol expression. For each view contribution:
    //   opb_form_coefficient > 0 (positive V in OPB):  add `|coeff| * link_le`.
    //   opb_form_coefficient < 0 (negative V in OPB):  add `|coeff| * link_ge`.
    // Reasoning: link_le contributes `-BinEnc(V) + ...` so it cancels
    // positive V; link_ge contributes `+BinEnc(V) + ...` so it cancels
    // negative V.
    //
    // This is a plain PolBuilder, NOT a deview-mode one: it pushes the raw
    // V-form `v_form_line` and link lines. A deview-mode builder would call
    // back into `deviewed_line_for(v_form_line)` while we are mid-way through
    // deriving that very line, so plain mode is both correct and avoids that
    // self-reference.
    //
    // We deliberately do NOT saturate. Downstream consumers (PolBuilder in
    // deview mode) use this line as the starting constraint in their own
    // pol + divide chains. Saturating here would clip bit-level coefficients
    // on wide-range variables (those encoded with a sign bit + magnitude bits),
    // which then leaks an uncancelled residual into the consumer's pol when
    // it adds a reif on the same variable. The unsaturated form has the full
    // bit-level coefficient mass needed for clean cancellation.
    PolBuilder pol;
    pol.add(v_form_line);
    for (const auto & vc : view_contributions) {
        auto [link_le, link_ge] = view_link_lines_for(vc.view_proof_id);
        Integer mult = vc.opb_form_coefficient > 0_i ? vc.opb_form_coefficient : -vc.opb_form_coefficient;
        const ProofLine & link_to_use = vc.opb_form_coefficient > 0_i ? link_le : link_ge;
        pol.add(link_to_use, mult);
    }
    auto pol_str = pol.str();

    emit_proof_line_now_or_at_start([this, v_form_line, pol_str](ProofLogger * const logger) {
        auto deview_line = logger->emit_proof_line(pol_str, ProofLevel::Top);
        register_deviewed_line(v_form_line, deview_line);
    });
}

auto NamesAndIDsTracker::track_bounds(const SimpleOrProofOnlyIntegerVariableID & id, Integer lower, Integer upper) -> void
{
    _imp->integer_variable_definition_bounds.emplace(id, pair{lower, upper});
}

auto NamesAndIDsTracker::create_proof_flag(const string & name) -> ProofFlag
{
    ProofFlag result{allocate_flag_index(), true};
    track_variable_name(result, name);
    auto flagvar = allocate_xliteral_meaning(result);
    _imp->flags.emplace(result, flagvar);
    _imp->flags.emplace(! result, ! flagvar);
    return result;
}

auto NamesAndIDsTracker::pb_file_string_for(const XLiteral & lit) const -> string
{
    if (_imp->verbose_names) {
        auto it = _imp->xlits_to_verbose_names.find(lit);
        if (it == _imp->xlits_to_verbose_names.end())
            throw ProofError("missing verbose name for xliteral " + to_string(lit.id) + " " + to_string(lit.negated));
        return it->second;
    }
    else {
        if (lit.negated)
            return "~x" + to_string(lit.id);
        else
            return "x" + to_string(lit.id);
    }
}

auto NamesAndIDsTracker::pb_file_string_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) const -> string
{
    return pb_file_string_for(xliteral_for(cond));
}

auto NamesAndIDsTracker::xliteral_for(const ProofFlag & flag) const -> const XLiteral
{
    auto f = _imp->flags.find(flag);
    if (f == _imp->flags.end())
        throw ProofError{"can't find literals for flag"};
    return f->second;
}

auto NamesAndIDsTracker::xliteral_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) const -> const XLiteral
{
    auto f = _imp->variable_conditions_to_x.find(cond);
    if (f == _imp->variable_conditions_to_x.end())
        throw ProofError{"can't find literals for cond"};
    return f->second;
}

auto NamesAndIDsTracker::pb_file_string_for(const ProofFlag & flag) const -> string
{
    return pb_file_string_for(xliteral_for(flag));
}

namespace
{
    auto write_vardata(fstream & stream, bool & first, const string & name, const nlohmann::json & json) -> void
    {
        if (! first)
            stream << ",\n";
        else
            first = false;

        nlohmann::json name_json = name;
        stream << name_json << ": " << json;
    }
}

auto NamesAndIDsTracker::allocate_xliteral_meaning(SimpleOrProofOnlyIntegerVariableID id,
    const EqualsOrGreaterEqual & op, Integer value) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        string value_name;
        if (value < 0_i)
            value_name = "minus" + abs(value).to_string();
        else
            value_name = value.to_string();

        overloaded{
            [&](const SimpleIntegerVariableID & id) -> void {
                string name = format("i[{}][{}{}]", name_of(id), (op == EqualsOrGreaterEqual::Equals ? "eq" : "ge"), value_name);
                _imp->xlits_to_verbose_names.emplace(result, name);
                _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
            },
            [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                string name = format("p[{}_{}][{}{}]", id.index, name_of(id),
                    (op == EqualsOrGreaterEqual::Equals ? "eq" : "ge"), value_name);
                _imp->xlits_to_verbose_names.emplace(result, name);
                _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
            }}
            .visit(id);
    }

    if (_imp->variables_map_file) {
        try {
            nlohmann::json data;
            data["type"] = "condition";
            overloaded{
                [&](const SimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "intvar";
                    data["cpvarid"] = id.index;
                },
                [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "proofintvar";
                    data["cpvarid"] = id.index;
                }}
                .visit(id);

            data["name"] = name_of(id);
            data["operator"] = (op == EqualsOrGreaterEqual::Equals ? "=" : ">=");
            data["value"] = value.raw_value;

            write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }

    return result;
}

auto NamesAndIDsTracker::allocate_xliteral_meaning(ProofFlag flag) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        string name = format("f[{}][{}]", flag.index, name_of(flag));
        _imp->xlits_to_verbose_names.emplace(result, name);
        _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
    }

    if (_imp->variables_map_file) {
        try {
            nlohmann::json data;
            data["type"] = "proofflag";
            data["name"] = name_of(flag);

            write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }

    return result;
}

auto NamesAndIDsTracker::allocate_xliteral_meaning_negative_bit_of(SimpleOrProofOnlyIntegerVariableID id, Integer power) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        overloaded{
            [&](const SimpleIntegerVariableID & id) -> void {
                string name = format("i[{}][sign]", name_of(id));
                _imp->xlits_to_verbose_names.emplace(result, name);
                _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
            },
            [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                string name = format("p[{}_{}][sign]", id.index, name_of(id));
                _imp->xlits_to_verbose_names.emplace(result, name);
                _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
            }}
            .visit(id);
    }

    if (_imp->variables_map_file) {
        try {
            nlohmann::json data;
            data["type"] = "intvarnegbit";
            overloaded{
                [&](const SimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "intvar";
                    data["cpvarid"] = id.index;
                },
                [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "proofintvar";
                    data["cpvarid"] = id.index;
                }}
                .visit(id);
            data["name"] = name_of(id);
            data["power"] = power.raw_value;

            write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }

    return result;
}

auto NamesAndIDsTracker::allocate_xliteral_meaning_bit_of(SimpleOrProofOnlyIntegerVariableID id, Integer power) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        overloaded{
            [&](const SimpleIntegerVariableID & id) -> void {
                string name = format("i[{}][b{}]", name_of(id), power);
                _imp->xlits_to_verbose_names.emplace(result, name);
                _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
            },
            [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                string name = format("p[{}_{}][b{}]", id.index, name_of(id), power);
                _imp->xlits_to_verbose_names.emplace(result, name);
                _imp->xlits_to_verbose_names.emplace(! result, "~" + name);
            }}
            .visit(id);
    }

    if (_imp->variables_map_file) {
        try {
            nlohmann::json data;
            data["type"] = "intvarbit";
            overloaded{
                [&](const SimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "intvar";
                    data["cpvarid"] = id.index;
                },
                [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "proofintvar";
                    data["cpvarid"] = id.index;
                }}
                .visit(id);

            data["name"] = name_of(id);
            data["power"] = power.raw_value;

            write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }

    return result;
}

auto NamesAndIDsTracker::track_variable_name(SimpleOrProofOnlyIntegerVariableID id, const string & name) -> void
{
    _imp->id_names.emplace(id, name);
}

auto NamesAndIDsTracker::track_variable_name(ProofFlag id, const string & name) -> void
{
    _imp->flag_names.emplace(id, name);
}

auto NamesAndIDsTracker::name_of(SimpleOrProofOnlyIntegerVariableID id) const -> const string &
{
    return _imp->id_names.at(id);
}

auto NamesAndIDsTracker::name_of(ProofFlag id) const -> const string &
{
    return _imp->flag_names.at(id);
}

auto NamesAndIDsTracker::s_expr_name_of(IntegerVariableID id) const -> string
{
    return overloaded{
        [&](const ConstantIntegerVariableID & c) -> string { return c.const_value.to_string(); },
        [&](const SimpleIntegerVariableID & v) -> string { return name_of(v); },
        [&](const ViewOfIntegerVariableID & vv) -> string {
            stringstream name;
            name << "(";
            name << (vv.negate_first ? "-" : "");
            name << name_of(vv.actual_variable) << " + " << vv.then_add << ")";
            return name.str();
        }}
        .visit(id);
}

auto NamesAndIDsTracker::s_expr_name_of(Literal lit) const -> string
{
    return overloaded{
        [](const TrueLiteral &) -> string { return "1"; },
        [](const FalseLiteral &) -> string { return "0"; },
        [&](const VariableConditionFrom<SimpleIntegerVariableID> & cond) -> string {
            return s_expr_name_of(cond.var);
        },
        [](const VariableConditionFrom<ProofOnlySimpleIntegerVariableID> &) -> string {
            throw UnimplementedException{};
        }}
        .visit(simplify_literal(*this, lit));
}

auto NamesAndIDsTracker::s_expr_name_of(ReificationCondition cond) const -> string
{
    return overloaded{
        [](const reif::MustHold &) -> string { return ""; },
        [](const reif::MustNotHold &) -> string { return ""; },
        [&](const auto & reif) -> string { // This is safe, right?
            return "(" + s_expr_name_of(reif.cond.var) + " " + s_expr_name_of(reif.cond.op) + " " + reif.cond.value.to_string() + ")";
        }}
        .visit(cond);

    return "COND";
}

auto NamesAndIDsTracker::s_expr_name_of(VariableConditionOperator op) const -> string
{
    switch (op) {
        using enum VariableConditionOperator;
        // cake_pb_cp's reification-condition operators are symbols, not words.
    case Equal: return "=";
    case NotEqual: return "!=";
    case GreaterEqual: return ">=";
    case Less: return "<";
    }

    throw NonExhaustiveSwitch{};
}

auto NamesAndIDsTracker::s_expr_render_of(IntegerVariableID id) const -> string
{
    return overloaded{
        [&](const ConstantIntegerVariableID & c) -> string { return "(minimize " + c.const_value.to_string() + ")"; },
        [&](const SimpleIntegerVariableID & v) -> string { return "(minimize " + name_of(v) + ")"; },
        [&](const ViewOfIntegerVariableID & vv) -> string {
            return "(" + string{vv.negate_first ? "maximize" : "minimize"} + " " + name_of(vv.actual_variable) + ")";
        }}
        .visit(id);
}

auto NamesAndIDsTracker::s_expr_term_of(IntegerVariableID id) const -> SExpr
{
    // A variable / literal name is always a single, non-empty s-expression term
    // (a bare atom like `_1`, or a list like a view `(-_1 + 17)`), so parsing it
    // can't fail or be empty.
    return parse_s_expr(s_expr_name_of(id));
}

auto NamesAndIDsTracker::s_expr_term_of(ReificationCondition cond) const -> optional<SExpr>
{
    // s_expr_name_of(ReificationCondition) returns "" for the unconditional
    // cases (MustHold / MustNotHold); surface that as nullopt so callers don't
    // have to know about the empty-string sentinel.
    auto name = s_expr_name_of(cond);
    if (name.empty())
        return nullopt;
    return parse_s_expr(name);
}

auto NamesAndIDsTracker::reify(const WPBSumLE & ineq, const HalfReifyOnConjunctionOf & half_reif) -> WPBSumLE
{
    // so what happens if there's a false literal in the left hand term? conceptually,
    // this means the constraint will always hold, but it's probably useful to have
    // something that syntactically contains all the right variables. so, we can just
    // make the degree of falsity be very low so the constraint always holds.
    bool contains_false_literal = any_of(half_reif.begin(), half_reif.end(),
        [&](const auto & flag) {
            return overloaded{
                [&](const ProofFlag &) { return false; },
                [&](const ProofLiteral & pl) {
                    return overloaded{
                        [&](Literal lit) { return is_literally_false(lit); },
                        [&](const ProofVariableCondition &) { return false; },
                    }
                        .visit(pl);
                },
                [&](const ProofBitVariable &) { return false; }}
                .visit(flag);
        });

    // work out how big the reification constant needs to be, by adding together
    // positive terms in the inequality and negating
    Integer max_contribution_from_positive_terms = 0_i;

    for (auto & [w, v] : ineq.lhs.terms) {
        overloaded{
            [&, w = w](const ProofLiteral &) {
                max_contribution_from_positive_terms += max(0_i, w);
            },
            [&, w = w](const ProofFlag &) {
                max_contribution_from_positive_terms += max(0_i, w);
            },
            [&, w = w](const IntegerVariableID & var) {
                overloaded{
                    [&](const SimpleIntegerVariableID & var) {
                        for (const auto & [bit_value, bit_lit] : each_bit(var))
                            max_contribution_from_positive_terms += max(0_i, w * bit_value);
                    },
                    [&](const ViewOfIntegerVariableID & view) {
                        // A registered view is *emitted* over its own proof-only
                        // bit-vector (BinEnc(V) directly encodes the view value),
                        // so the reification constant must be sized from those
                        // bits too. Sizing it from the underlying variable's bits
                        // + then_add (the X representation) instead gives a span
                        // matching the view's value range but smaller than its
                        // bit-vector's, leaving the reified line valid only modulo
                        // V's domain bound -- which RUP can't fold in.
                        if (auto v_proof_id = find_view(view)) {
                            for (const auto & [bit_value, bit_lit] : each_bit(*v_proof_id))
                                max_contribution_from_positive_terms += max(0_i, w * bit_value);
                        }
                        // The term is w * view = w * ((negate_first ? -actual : actual) + then_add).
                        // The variable part w * (negate_first ? -actual : actual) has per-bit max
                        // contribution max(0, ±w * bit_value), with the sign flip depending on
                        // negate_first. The constant part w * then_add applies regardless and is
                        // not affected by negate_first.
                        else if (! view.negate_first) {
                            for (const auto & [bit_value, bit_lit] : each_bit(view.actual_variable))
                                max_contribution_from_positive_terms += max(0_i, w * bit_value);
                            max_contribution_from_positive_terms += max(0_i, w * view.then_add);
                        }
                        else {
                            for (const auto & [bit_value, bit_lit] : each_bit(view.actual_variable))
                                max_contribution_from_positive_terms += max(0_i, -w * bit_value);
                            max_contribution_from_positive_terms += max(0_i, w * view.then_add);
                        }
                    },
                    [&](const ConstantIntegerVariableID & cvar) {
                        max_contribution_from_positive_terms += max(0_i, w * cvar.const_value);
                    }}
                    .visit(var);
            },
            [&, w = w](const ProofOnlySimpleIntegerVariableID & var) {
                for (const auto & [bit_value, bit_lit] : each_bit(var))
                    max_contribution_from_positive_terms += max(0_i, w * bit_value);
            },
            [&, w = w](const ProofBitVariable &) {
                max_contribution_from_positive_terms += max(0_i, w);
            },
        }
            .visit(v);
    }

    // Usually it would be fine to say 0_i rather than -1_i here, because if a constraint
    // is trivially true, it doesn't really matter whether the implication is there or
    // not. However, for syntactic wrangling reasons, we probably want the implication
    // to always be there.
    auto clamped_reif_const = min(-max_contribution_from_positive_terms + ineq.rhs, -1_i);

    WPBSum new_lhs = ineq.lhs;
    for (auto & r : half_reif)
        overloaded{
            [&](const ProofFlag & f) {
                new_lhs += clamped_reif_const * ! f;
            },
            [&](const ProofLiteral & lit) {
                new_lhs += clamped_reif_const * ! lit;
            },
            [&](const ProofBitVariable & bit) {
                new_lhs += clamped_reif_const * ! bit;
            }}
            .visit(r);

    // if we have a false literal on the left hand side, adjusting the degree of falsity
    // up by the sum of positive terms is enough that it will be trivially true.
    if (contains_false_literal)
        return new_lhs <= ineq.rhs + max_contribution_from_positive_terms;
    else
        return new_lhs <= ineq.rhs;
}
