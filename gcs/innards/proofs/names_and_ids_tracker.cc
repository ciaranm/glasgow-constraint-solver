#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/interval_tree.hh>
#include <gcs/innards/proofs/hints.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_line-fwd.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/proof_only_variables-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <algorithm>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <gcs/proof.hh>
#include <list>
#include <map>
#include <set>
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
using std::make_shared;
using std::make_unique;
using std::map;
using std::max;
using std::min;
using std::nullopt;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::string;
using std::stringstream;
using std::to_string;
using std::unordered_map;
using std::variant;
using std::vector;
using std::visit;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

namespace
{
    // These three tables are read on every literal rendered into every proof
    // line, so they are hashed rather than tree-ordered. Nothing iterates
    // them. The hashes just have to spread structured small integers; the
    // magic constant is the usual 64-bit golden-ratio mix.
    constexpr auto hash_combine(std::size_t seed, std::size_t v) -> std::size_t
    {
        return seed ^ (v + 0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2));
    }

    struct HashSimpleOrProofOnlyVariable
    {
        [[nodiscard]] auto operator()(const SimpleOrProofOnlyIntegerVariableID & id) const -> std::size_t
        {
            return visit(overloaded{//
                             [&](const SimpleIntegerVariableID & v) { return hash_combine(1, v.index); },
                             [&](const ProofOnlySimpleIntegerVariableID & v) { return hash_combine(2, v.index); }},
                id);
        }
    };

    struct HashVariableCondition
    {
        [[nodiscard]] auto operator()(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) const -> std::size_t
        {
            auto h = HashSimpleOrProofOnlyVariable{}(cond.var);
            h = hash_combine(h, static_cast<std::size_t>(cond.op));
            h = hash_combine(h, static_cast<std::size_t>(cond.value.raw_value));
            return hash_combine(h, static_cast<std::size_t>(cond.upper_value.raw_value));
        }
    };

    struct HashView
    {
        [[nodiscard]] auto operator()(const ViewOfIntegerVariableID & view) const -> std::size_t
        {
            auto h = hash_combine(view.negate_first ? 3 : 4, view.actual_variable.index);
            return hash_combine(h, static_cast<std::size_t>(view.then_add.raw_value));
        }
    };

    struct HashProofFlag
    {
        [[nodiscard]] auto operator()(const ProofFlag & flag) const -> std::size_t
        {
            return hash_combine(flag.positive ? 5 : 6, flag.index);
        }
    };
}

struct NamesAndIDsTracker::Imp
{
    ProofModel * model = nullptr;
    ProofLogger * logger = nullptr;

    unordered_map<SimpleOrProofOnlyIntegerVariableID, ProofLine, HashSimpleOrProofOnlyVariable> variable_at_least_one_constraints;
    unordered_map<VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID>, XLiteral, HashVariableCondition> variable_conditions_to_x;
    unordered_map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, vector<pair<Integer, XLiteral>>>, HashSimpleOrProofOnlyVariable>
        integer_variable_bits_to_size_and_proof_vars;
    unordered_map<SimpleOrProofOnlyIntegerVariableID, pair<Integer, Integer>, HashSimpleOrProofOnlyVariable> integer_variable_definition_bounds;
    // Variables (e.g. ArgSort's cake-named free-bit-sum sorted values) whose [lo, hi]
    // domain is NOT a trivial consequence of the OPB -- cake emits no bound line for
    // them and the bounds are only entailed through conditional channels -- so
    // need_gevar's fix_bound must not pin their boundary order literals; those bounds
    // are instead established once, explicitly, by the owning constraint's proof.
    std::set<SimpleOrProofOnlyIntegerVariableID> bounds_not_trivially_derivable;
    // Variables whose order-encoding (ge) atom definitions carry @i[..][ge] labels that
    // a cake_pb_cp OPB does not create (it reifies each atom per value under its own
    // @c[peq..] labels). need_gevar recovers those labels in-proof for these variables:
    // it re-declares each half's reification via an `ia` line under our @i label at
    // proof start, so the order-chain pols resolve against them in both the solver's own
    // OPB (workflow 1) and cake's re-derived OPB (workflow 2). Used for ArgSort's
    // permutation variables, whose eq atoms are OPB constraint terms/guards (matching
    // cake) and so are forced model-time under @i labels.
    std::set<SimpleOrProofOnlyIntegerVariableID> vars_recover_labels;
    unordered_map<SimpleOrProofOnlyIntegerVariableID, map<Integer, pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>>>,
        HashSimpleOrProofOnlyVariable>
        gevars_that_exist;
    unordered_map<SimpleOrProofOnlyIntegerVariableID, map<Integer, pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>>>,
        HashSimpleOrProofOnlyVariable>
        eqvars_that_exist;
    // Range ("in") literals [lo, hi], keyed by (lo, hi): the forward and reverse
    // lines of the reification against the variable's two order cuts. The literal
    // itself lives in variable_conditions_to_x, keyed by the InRange / NotInRange
    // conditions, just like the eq and order atoms. A width-1 interval is its eq
    // atom and is never entered here.
    unordered_map<SimpleOrProofOnlyIntegerVariableID, map<pair<Integer, Integer>, pair<ProofLine, ProofLine>>, HashSimpleOrProofOnlyVariable>
        invars_that_exist;

    // Every range and eq literal on each variable, as intervals, for finding a new
    // literal's immediate neighbours in the containment order.
    map<SimpleOrProofOnlyIntegerVariableID, IntervalTree> containment_trees;

    // The always-covered partition for each variable with interval literals: the
    // sorted cell start points, always containing the definition lower bound and
    // ub+1 as a sentinel, so the cells are the intervals between consecutive
    // boundaries. Every cell has a literal, every eq atom on a partitioned
    // variable is a singleton cell, and every requested interval is a union of
    // adjacent cells. Absent until the first interval request.
    map<SimpleOrProofOnlyIntegerVariableID, std::set<Integer>> interval_partitions;

    unordered_map<ViewOfIntegerVariableID, ProofOnlySimpleIntegerVariableID, HashView> view_proof_only_vars;
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

    unordered_map<ProofFlag, XLiteral, HashProofFlag> flags;

    map<SimpleOrProofOnlyIntegerVariableID, string> id_names;
    // The PB-file rendering of every allocated XLiteral, indexed 2 * id +
    // negated (ids are allocated sequentially from 1). Populated in both
    // naming modes, so rendering a literal is an index, not a lookup.
    vector<string> xlit_names;
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
    bool use_compact_boolean_encoding = false;
    AssertionLevel assertion_level = AssertionLevel::Off;
};

NamesAndIDsTracker::NamesAndIDsTracker(const ProofOptions & proof_options) : _imp(make_unique<Imp>())
{
    _imp->verbose_names = proof_options.verbose_names;
    _imp->use_compact_boolean_encoding = proof_options.use_compact_boolean_encoding;
    _imp->assertion_level = proof_options.assertion_level;

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

auto NamesAndIDsTracker::associate_condition_with_xliteral(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond, const XLiteral & x)
    -> void
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
        [&](const ConstantIntegerVariableID &) -> ProofLine { throw UnimplementedException{}; }, //
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
        }, //
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
        } //
    }
        .visit(var);
}

auto NamesAndIDsTracker::need_pol_item_defining_literal(const IntegerVariableCondition & cond) -> variant<ProofLine, XLiteral>
{
    return overloaded{
        [&](const ConstantIntegerVariableID &) -> variant<ProofLine,                              //
                                                   XLiteral> { throw UnimplementedException{}; }, //
        [&](const SimpleIntegerVariableID & var) -> variant<ProofLine, XLiteral> {
            switch (cond.op) {
                using enum VariableConditionOperator;
            case GreaterEqual: need_gevar(var, cond.value); return _imp->gevars_that_exist.at(var).at(cond.value).first;
            case Less: need_gevar(var, cond.value); return _imp->gevars_that_exist.at(var).at(cond.value).second;
            case Equal: need_direct_encoding_for(var, cond.value); return _imp->eqvars_that_exist.at(var).at(cond.value).first;
            case NotEqual: need_direct_encoding_for(var, cond.value); return _imp->eqvars_that_exist.at(var).at(cond.value).second;
            case InRange:
                static_cast<void>(need_invar(var, cond.value, cond.upper_value));
                return _imp->invars_that_exist.at(var).at(pair{cond.value, cond.upper_value}).first;
            case NotInRange:
                static_cast<void>(need_invar(var, cond.value, cond.upper_value));
                return _imp->invars_that_exist.at(var).at(pair{cond.value, cond.upper_value}).second;
            }
            throw NonExhaustiveSwitch{};
        }, //
        [&](const ViewOfIntegerVariableID & var) -> variant<ProofLine, XLiteral> {
            // If the view's been registered, V's atoms have proper Defs over
            // BinEnc(V) and the pol-item path looks just like a simple
            // variable's. The Equal/NotEqual throws below only fire on the
            // deview fallback for views first seen during proof logging.
            if (auto v_id = find_view(var)) {
                switch (cond.op) {
                    using enum VariableConditionOperator;
                case GreaterEqual: need_gevar(*v_id, cond.value); return _imp->gevars_that_exist.at(*v_id).at(cond.value).first;
                case Less: need_gevar(*v_id, cond.value); return _imp->gevars_that_exist.at(*v_id).at(cond.value).second;
                case Equal: need_direct_encoding_for(*v_id, cond.value); return _imp->eqvars_that_exist.at(*v_id).at(cond.value).first;
                case NotEqual: need_direct_encoding_for(*v_id, cond.value); return _imp->eqvars_that_exist.at(*v_id).at(cond.value).second;
                case InRange:
                case NotInRange: throw UnimplementedException{};
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
            case Equal: throw UnimplementedException{};
            case NotEqual: throw UnimplementedException{};
            case InRange:
            case NotInRange: throw UnimplementedException{};
            }
            throw NonExhaustiveSwitch{};
        } //
    }
        .visit(cond.var);
}

auto NamesAndIDsTracker::create_literals_for_introduced_variable_value(SimpleIntegerVariableID id, Integer val, const string & name) -> void
{
    // These literals bypass eqvars_that_exist and the containment structures, which
    // is safe because an introduced variable has no bits encoding, so no range
    // literal can ever be defined over it.
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
    case NotEqual: need_direct_encoding_for(cond.var, cond.value); break;
    case Less:
    case GreaterEqual: need_gevar(cond.var, cond.value); break;
    case InRange:
    case NotInRange:
        if (! _imp->variable_conditions_to_x.contains(cond))
            static_cast<void>(need_invar(cond.var, cond.value, cond.upper_value));
        break;
    }
}

auto NamesAndIDsTracker::need_all_proof_names_in(const SumOf<Weighted<PseudoBooleanTerm>> & sum) -> void
{
    for (auto & [_, v] : sum.terms)
        overloaded{
            [&](const ProofLiteral & lit) {
                overloaded{
                    [&](const TrueLiteral &) {},                                                        //
                    [&](const FalseLiteral &) {},                                                       //
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) { need_proof_name(cond); } //
                }
                    .visit(simplify_literal(*this, lit));
            },                         //
            [&](const ProofFlag &) {}, //
            [&](const IntegerVariableID & var) {
                // Opportunistically register view bit vectors during model
                // writing. need_view can only introduce a view while the
                // model is being written (it throws during the proof-logging
                // phase), so this is gated on _imp->model.
                if (_imp->model)
                    if (auto view = std::get_if<ViewOfIntegerVariableID>(&var))
                        static_cast<void>(need_view(*view));
            },                                                //
            [&](const ProofOnlySimpleIntegerVariableID &) {}, //
            [&](const ProofBitVariable &) {}                  //
        }
            .visit(v);
}

auto NamesAndIDsTracker::need_all_proof_names_in(const Literals & lits) -> void
{
    for (auto & lit : lits)
        overloaded{
            [&](const TrueLiteral &) {},                                                        //
            [&](const FalseLiteral &) {},                                                       //
            [&]<typename T_>(const VariableConditionFrom<T_> & cond) { need_proof_name(cond); } //
        }
            .visit(simplify_literal(*this, lit));
}

auto NamesAndIDsTracker::need_all_proof_names_in(const HalfReifyOnConjunctionOf & h) -> void
{
    for (auto & term : h)
        overloaded{
            [&](const ProofLiteral & lit) {
                overloaded{
                    [&](const TrueLiteral &) {},                                                        //
                    [&](const FalseLiteral &) {},                                                       //
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) { need_proof_name(cond); } //
                }
                    .visit(simplify_literal(*this, lit));
            },                               //
            [&](const ProofFlag &) {},       //
            [&](const ProofBitVariable &) {} //
        }
            .visit(term);
}

auto NamesAndIDsTracker::negative_bit_coefficient(const SimpleOrProofOnlyIntegerVariableID & id) -> Integer
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(id);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");
    return it->second.first;
}

auto NamesAndIDsTracker::each_bit(const SimpleOrProofOnlyIntegerVariableID & id) -> generator<pair<Integer, XLiteral>>
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

auto NamesAndIDsTracker::track_bits(
    const SimpleOrProofOnlyIntegerVariableID & id, Integer negative_coeff, const vector<pair<Integer, XLiteral>> & bit_vars) -> void
{
    _imp->integer_variable_bits_to_size_and_proof_vars.emplace(id, pair{negative_coeff, bit_vars});
}

auto NamesAndIDsTracker::allocate_flag_index() -> unsigned long long
{
    return _imp->flags.size() / 2;
}

auto NamesAndIDsTracker::track_eqvar(
    SimpleIntegerVariableID id, Integer val, const pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>> & names) -> void
{
    _imp->eqvars_that_exist[id].emplace(val, names);
}

auto NamesAndIDsTracker::track_gevar(
    SimpleIntegerVariableID id, Integer val, const pair<variant<ProofLine, XLiteral>, variant<ProofLine, XLiteral>> & names) -> void
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

    // Model-path eq-atom definitions are labelled @<base>[eq<v>][r]/[f] (see
    // definitional_label_base): @i[name] for a real variable, @po[index] for a
    // proof-only one, so they are referenced (e.g. in a view's deview-form) by
    // name rather than line number. A bracket-nesting real-variable name has no
    // valid label and falls back to the unlabelled definitional form.
    auto eq_base = definitional_label_base(id);
    auto add_eq = [&](const char * role, const WPBSumLE & ineq, const HalfReifyOnConjunctionOf & reif) -> ProofLine {
        return _imp->model->add_labelled_constraint(eq_base + "[eq" + to_string(v.raw_value) + "][" + role + "]", ineq, reif);
    };

    // The compact boolean encoding defines an eq atom at a bound using only the
    // one non-trivial order literal (eq(lower) <=> ~ge(lower+1), since ge(lower)
    // is always true; eq(upper) <=> ge(upper), since ge(upper+1) is always
    // false). With it off (the default), every eq atom -- including those at the
    // bounds -- is the full eq(v) <=> ge(v) & ~ge(v+1), so the trivial ge(lower)
    // and ge(upper+1) literals are materialised (need_gevar emits and fixes
    // them), matching cake_pb_cp's eager encoding.
    if (_imp->use_compact_boolean_encoding && bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.first == v) {
        // it's a lower bound
        if (_imp->logger && _imp->assertion_level <= AssertionLevel::Links) {
            visit(
                [&](const auto & id) {
                    auto [_f_line, _r_line] =
                        _imp->logger->emit_red_proof_lines_reifying(WPBSum{} + 1_i * ! (id >= (v + 1_i)) >= 1_i, id == v, ProofLevel::Top);
                    forwards_line = _f_line;
                    reverse_line = _r_line;
                },
                id);
        }
        else if (! _imp->logger) {
            visit(
                [&](const auto & id) {
                    forwards_line = add_eq("r", WPBSum{} + 1_i * ! (id >= (v + 1_i)) >= 1_i, {{id == v}});
                    reverse_line = add_eq("f", WPBSum{} + 1_i * (id >= (v + 1_i)) >= 1_i, {{id != v}});
                },
                id);
            ++_imp->model_variables;
        }
    }
    else if (_imp->use_compact_boolean_encoding && bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.second == v) {
        // it's an upper bound
        if (_imp->logger && _imp->assertion_level <= AssertionLevel::Links) {
            visit(
                [&](const auto & id) {
                    auto [_f_line, _r_line] =
                        _imp->logger->emit_red_proof_lines_reifying(WPBSum{} + 1_i * (id >= v) >= 1_i, id == v, ProofLevel::Top);
                    forwards_line = _f_line;
                    reverse_line = _r_line;
                },
                id);
        }
        else if (! _imp->logger) {
            visit(
                [&](const auto & id) {
                    forwards_line = add_eq("r", WPBSum{} + 1_i * (id >= v) >= 1_i, {{id == v}});
                    reverse_line = add_eq("f", WPBSum{} + 1_i * ! (id >= v) >= 1_i, {{id != v}});
                },
                id);
            ++_imp->model_variables;
        }
    }
    else {
        // neither a lower nor an upper bound
        if (_imp->logger && _imp->assertion_level <= AssertionLevel::Links)
            visit(
                [&](const auto & id) {
                    auto [_f_line, _r_line] = _imp->logger->emit_red_proof_lines_reifying(
                        WPBSum{} + (1_i * (id >= v)) + (1_i * ! (id > v)) >= 2_i, id == v, ProofLevel::Top);
                    forwards_line = _f_line;
                    reverse_line = _r_line;
                },
                id);
        else if (! _imp->logger) {
            visit(
                [&](const auto & id) {
                    forwards_line = add_eq("r", WPBSum{} + 1_i * (id >= v) + 1_i * ! (id > v) >= 2_i, {{id == v}});
                    reverse_line = add_eq("f", WPBSum{} + 1_i * ! (id >= v) + 1_i * (id > v) >= 1_i, {{id != v}});
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
            // Always queue this (it delays to proof start when the logger
            // isn't attached yet during model building); decide whether to
            // emit based on using_assertions() *inside* the lambda, when the
            // logger definitely exists. Guarding on _imp->logger out here
            // drops the step entirely during model building, losing the
            // channelling between the proof-only encoding and the actual
            // variable. See the matching pattern in need_gevar's bound links.
            emit_proof_line_now_or_at_start([v_cond, x_cond](ProofLogger * const logger) {
                if (logger->get_assertion_level() > AssertionLevel::Links)
                    return;

                auto assert_or_rup =
                    logger->get_assertion_level() == AssertionLevel::Links ? ProofRule(AssertProofRule{}) : ProofRule(RUPProofRule{});
                logger->emit(assert_or_rup, WPBSum{} + 1_i * ! v_cond + 1_i * x_cond >= 1_i, ProofLevel::Top);
                logger->emit(assert_or_rup, WPBSum{} + 1_i * ! x_cond + 1_i * v_cond >= 1_i, ProofLevel::Top);
            });
        }
    }

    // Nothing beyond this point needs to be emmitted at AssertionLevel::Links
    if (_imp->assertion_level > AssertionLevel::Links)
        return;

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

    // Link this new eq atom (a singleton [v, v]) to its immediate range containers,
    // so a rejected container propagates ~(id == v). Most variables never have any
    // range literals, so the containment tree is only maintained once one exists.
    link_immediate_containment(id, v, v);
    if (auto tree = _imp->containment_trees.find(id); tree != _imp->containment_trees.end())
        tree->second.insert(v, v);

    // On a partitioned variable, every eq atom is a singleton cell: split the
    // containing cell, so that interval coverings reach the atoms that per-value
    // conclusions are logged over.
    if (_imp->interval_partitions.contains(id)) {
        auto [lb, ub] = _imp->integer_variable_definition_bounds.at(id);
        if (lb <= v && v <= ub) {
            ensure_partition_cut(id, v);
            ensure_partition_cut(id, v + 1_i);
        }
    }
}

auto NamesAndIDsTracker::definitional_label_base(const SimpleOrProofOnlyIntegerVariableID & id) const -> string
{
    return visit(overloaded{                                                                              //
                     [&](const SimpleIntegerVariableID &) -> string { return "i[" + name_of(id) + "]"; }, //
                     [&](const ProofOnlySimpleIntegerVariableID & pid) -> string { return "po[" + to_string(pid.index) + "]"; }},
        id);
}

auto NamesAndIDsTracker::need_gevar(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> void
{
    if (_imp->variable_conditions_to_x.contains(id >= v))
        return;

    auto gevar = allocate_xliteral_meaning(id, EqualsOrGreaterEqual::GreaterEqual, v);
    _imp->variable_conditions_to_x.emplace(id >= v, gevar);
    _imp->variable_conditions_to_x.emplace(id < v, ! gevar);

    // gevar -> bits
    if (_imp->logger && _imp->assertion_level > AssertionLevel::Definitions) {
        _imp->gevars_that_exist[id].emplace(v, make_pair(ProofLine{}, ProofLine{})); // Don't output geqvar definitions if using assertions
    }
    else if (_imp->logger) {
        auto def_lines = visit(
            [&](const auto & id) { return _imp->logger->emit_red_proof_lines_reifying(WPBSum{} + (1_i * id) >= v, id >= v, ProofLevel::Top); }, id);
        _imp->gevars_that_exist[id].emplace(v, def_lines);
    }
    else {
        // Label the two halves @<base>[ge<v>][r]/[f]: the base is @i[name] for a
        // real variable (matching cake_pb_cp) or @po[index] for a proof-only one
        // (cake never sees it). The first emitted half (the id>=v reif, carrying
        // ~ge..) is cake's [r]; the second is [f]. v may be negative -- veripb
        // 3.0.2 allows `-` in @labels.
        string ge_label = definitional_label_base(id) + "[ge" + to_string(v.raw_value) + "]";
        _imp->gevars_that_exist[id].emplace(v,
            visit(
                [&](const auto & vid) -> pair<ProofLine, ProofLine> {
                    return pair{_imp->model->add_labelled_constraint(ge_label + "[r]", WPBSum{} + (1_i * vid) >= v, {{vid >= v}}),
                        _imp->model->add_labelled_constraint(ge_label + "[f]", WPBSum{} + (-1_i * vid) >= -v + 1_i, {{vid < v}})};
                },
                id));
        ++_imp->model_variables;

        // For a variable whose @i[..][ge] labels a cake_pb_cp OPB will not create (see
        // vars_recover_labels), recover the labels in-proof: re-declare each half's
        // reification via `ia` (implies-add) under our @i label at proof start, checked
        // implied against whatever reifies the atom in the OPB -- our own @i line in
        // workflow-1, cake's per-value @c[peq..] in workflow-2. The order-chain pols
        // then resolve against the recovered labels in either. Queued here, before this
        // call emits its chain links below, so the recovery lands ahead of them in the
        // proof; the reification is reconstructed via reify() so nothing is remembered.
        if (_imp->vars_recover_labels.contains(id))
            emit_proof_line_now_or_at_start([this, id, v, ge_label](ProofLogger * const logger) {
                visit(
                    [&](const auto & vid) {
                        logger->emit(ImpliesProofRule{}, reify(WPBSum{} + (1_i * vid) >= v, {{vid >= v}}), ProofLevel::Top, std::nullopt,
                            ProofLineLabel{ge_label + "[r]"});
                        logger->emit(ImpliesProofRule{}, reify(WPBSum{} + (-1_i * vid) >= -v + 1_i, {{vid < v}}), ProofLevel::Top, std::nullopt,
                            ProofLineLabel{ge_label + "[f]"});
                    },
                    id);
            });
    }

    // is it a bound?
    auto bounds = _imp->integer_variable_definition_bounds.find(id);

    auto fix_bound = [&](bool negated) {
        // Pin a trivial boundary order literal -- ge(lower) (always true) or
        // ge(ub+1) (always false) -- in the PROOF, never as an OPB axiom. The fact
        // is a consequence of the variable's bound constraints, not a definition,
        // so it does not belong in the OPB; cake_pb_cp likewise derives it rather
        // than pinning it, so an OPB axiom would make our OPB diverge from cake's,
        // and -- worse -- a pin re-derived per use does not survive VeriPB's
        // post-solx enumeration restriction. Emitting it once as a persistent
        // top-of-proof line (RUP-derivable from the bound constraints, or asserted
        // at AssertionLevel::Links) keeps the OPB byte-clean and the pin available
        // throughout both enumeration and refutation. emit_proof_line_now_or_at_start
        // queues it to proof start when the logger is not yet attached (model
        // building) and emits it immediately otherwise.
        emit_proof_line_now_or_at_start([id, v, negated](ProofLogger * const logger) {
            if (logger->get_assertion_level() > AssertionLevel::Links)
                return;
            ProofRule assert_or_rup =
                logger->get_assertion_level() == AssertionLevel::Links ? ProofRule(AssertProofRule{}) : ProofRule(RUPProofRule{});
            auto annotation = AssertionAnnotation{.hint_name = hints::InitialBound::hint_name};
            visit(
                [&](auto vid) {
                    logger->emit(assert_or_rup, WPBSum{} + 1_i * (negated ? ! (vid >= v) : (vid >= v)) >= 1_i, ProofLevel::Top, annotation);
                },
                id);
        });
    };

    // A variable whose bounds are not a trivial OPB consequence (see
    // bounds_not_trivially_derivable) gets no boundary pin -- pinning it would emit a
    // top-of-proof RUP line that is not actually reverse-unit-propagatable; its owner
    // derives the bounds explicitly instead.
    bool trivial_boundary = ! _imp->bounds_not_trivially_derivable.contains(id);

    // lower?
    if (trivial_boundary && bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.first >= v) {
        fix_bound(false);
    }

    // upper?
    if (trivial_boundary && bounds != _imp->integer_variable_definition_bounds.end() && bounds->second.second < v) {
        fix_bound(true);
    }

    auto & other_gevars = _imp->gevars_that_exist.at(id);
    auto this_gevar = other_gevars.find(v);
    auto higher_gevar = next(this_gevar);

    // Returns a shared PolBuilder (rather than a rendered string) so the line
    // references resolve to *relative* indices at emit time -- a workflow-2
    // requirement: under cake_pb_cp the OPB has a different constraint count, so
    // an absolute `pol 50 ...` would point at the wrong (or deleted) constraint.
    // emit_proof_line_now_or_at_start may defer the lambda to proof start, hence
    // the shared_ptr capture (the std::function it stores must stay copyable).
    auto make_pol_chain_line = [&](IntegerVariableCondition cond1, IntegerVariableCondition cond2) -> shared_ptr<PolBuilder> {
        auto b = make_shared<PolBuilder>();
        b->add_for_literal(*this, ! cond1).add_for_literal(*this, ! cond2).saturate();
        return b;
    };

    // implied by the next highest gevar, if there is one?
    auto link_hint = AssertionAnnotation{.hint_name = hints::BoundLink::hint_name};
    if (higher_gevar != other_gevars.end()) {
        overloaded{
            [&](const ProofOnlySimpleIntegerVariableID & id) {
                auto chain_con = WPBSum{} + (1_i * (id >= v)) + (1_i * ! (id >= higher_gevar->first)) >= 1_i;
                emit_proof_line_now_or_at_start([c = chain_con, link_hint](ProofLogger * const logger) {
                    if (logger->get_assertion_level() > AssertionLevel::Links)
                        return;
                    ProofRule assert_or_rup =
                        logger->get_assertion_level() == AssertionLevel::Links ? ProofRule(AssertProofRule{}) : ProofRule(RUPProofRule{});
                    logger->emit(assert_or_rup, c, ProofLevel::Top, link_hint);
                });
            }, //
            [&](const SimpleIntegerVariableID & id) {
                if (_imp->assertion_level > AssertionLevel::Links) {
                    return;
                }
                else if (_imp->assertion_level == AssertionLevel::Links) {
                    auto chain_con = WPBSum{} + (1_i * (id >= v)) + (1_i * ! (id >= higher_gevar->first)) >= 1_i;
                    emit_proof_line_now_or_at_start(
                        [c = chain_con, link_hint](ProofLogger * const logger) { logger->emit(AssertProofRule{}, c, ProofLevel::Top, link_hint); });
                }
                else {
                    auto pol = make_pol_chain_line(id >= v, ! (id >= higher_gevar->first));
                    emit_proof_line_now_or_at_start([pol](ProofLogger * const logger) { pol->emit(*logger, ProofLevel::Top); });
                }
            } //
        }
            .visit(id);
    }

    // implies the next lowest gevar, if there is one?
    if (this_gevar != other_gevars.begin()) {
        overloaded{
            [&](const ProofOnlySimpleIntegerVariableID & id) {
                auto chain_con = WPBSum{} + (1_i * (id >= prev(this_gevar)->first)) + (1_i * ! (id >= v)) >= 1_i;
                emit_proof_line_now_or_at_start([c = chain_con, link_hint = link_hint](ProofLogger * const logger) {
                    if (logger->get_assertion_level() > AssertionLevel::Links)
                        return;
                    ProofRule assert_or_rup =
                        logger->get_assertion_level() == AssertionLevel::Links ? ProofRule(AssertProofRule{}) : ProofRule(RUPProofRule{});
                    logger->emit(assert_or_rup, c, ProofLevel::Top, link_hint);
                });
            }, //
            [&](const SimpleIntegerVariableID & id) {
                if (_imp->assertion_level > AssertionLevel::Links) {
                    return;
                }
                else if (_imp->assertion_level == AssertionLevel::Links) {
                    auto chain_con = WPBSum{} + (1_i * (id >= prev(this_gevar)->first)) + (1_i * ! (id >= v)) >= 1_i;
                    emit_proof_line_now_or_at_start([c = chain_con, link_hint = link_hint](ProofLogger * const logger) {
                        logger->emit(AssertProofRule{}, c, ProofLevel::Top, link_hint);
                    });
                }
                else {
                    auto pol = make_pol_chain_line(id >= prev(this_gevar)->first, ! (id >= v));
                    emit_proof_line_now_or_at_start([pol](ProofLogger * const logger) { pol->emit(*logger, ProofLevel::Top); });
                }
            } //
        }
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
    if (_imp->assertion_level > AssertionLevel::Links)
        return;

    if (auto pid_ptr = std::get_if<ProofOnlySimpleIntegerVariableID>(&id)) {
        auto view_it = _imp->view_proof_only_to_view.find(*pid_ptr);
        if (view_it != _imp->view_proof_only_to_view.end()) {
            const auto & view = view_it->second;
            Integer x_threshold = view.negate_first ? view.then_add - v + 1_i : v - view.then_add;
            need_gevar(view.actual_variable, x_threshold);
            if (_imp->assertion_level == AssertionLevel::Links) {
                // Definitions are omitted at this level, instead assert the view links that the
                // pol lines below would derive.
                auto v_atom = (*pid_ptr >= v);
                auto x_atom = (view.actual_variable >= x_threshold);
                auto x_cond = view.negate_first ? ! x_atom : x_atom;
                auto d1 = WPBSum{} + 1_i * ! v_atom + 1_i * x_cond >= 1_i;
                auto d2 = WPBSum{} + 1_i * ! x_cond + 1_i * v_atom >= 1_i;
                emit_proof_line_now_or_at_start([d1, d2, link_hint](ProofLogger * const logger) {
                    logger->emit(AssertProofRule{}, d1, ProofLevel::Top, link_hint);
                    logger->emit(AssertProofRule{}, d2, ProofLevel::Top, link_hint);
                });
                return;
            }

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
                // Shared PolBuilders (not rendered strings) so the line refs emit
                // as relative indices -- see make_pol_chain_line above for why.
                auto b1 = make_shared<PolBuilder>();
                b1->add(*v_fwd_line).add(link.first).add(d1_x).saturate();
                auto b2 = make_shared<PolBuilder>();
                b2->add(*v_rev_line).add(link.second).add(d2_x).saturate();
                emit_proof_line_now_or_at_start([b1, b2](ProofLogger * const logger) {
                    b1->emit(*logger, ProofLevel::Top);
                    b2->emit(*logger, ProofLevel::Top);
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

auto NamesAndIDsTracker::link_immediate_containment(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> void
{
    if (! _imp->logger || _imp->logger->get_assertion_level() > AssertionLevel::Links) // Should be unreachable at AssertionLevel::Links anyway
        return;

    auto tree_it = _imp->containment_trees.find(id);
    if (tree_it == _imp->containment_trees.end())
        return;
    const auto & tree = tree_it->second;

    // A child -> parent containment edge (~child OR parent) as a rup line. A width-1
    // literal is its eq atom; nothing fits strictly inside a width-1 literal, so a
    // parent is always a range.
    auto emit_edge = [&](Integer clo, Integer chi, Integer plo, Integer phi) {
        visit(
            [&](const auto & id) {
                WPBSum edge;
                if (clo == chi)
                    edge += 1_i * (id != clo);
                else
                    edge += 1_i * not_in_range(id, clo, chi);
                edge += 1_i * in_range(id, plo, phi);
                _imp->logger->emit_rup_proof_line(move(edge) >= 1_i, ProofLevel::Top);
            },
            id);
    };

    // self -> minimal containers: walking candidates by decreasing lo (ties:
    // increasing hi), a candidate is minimal exactly when its hi is strictly below
    // every hi seen so far, since everything seen so far has a lo at least as big.
    vector<pair<Integer, Integer>> found;
    tree.for_each_containing(lo, hi, [&](Integer c, Integer d) {
        if (c != lo || d != hi)
            found.emplace_back(c, d);
    });
    sort(found, [](const pair<Integer, Integer> & x, const pair<Integer, Integer> & y) {
        return x.first == y.first ? x.second < y.second : x.first > y.first;
    });
    optional<Integer> least_hi;
    for (const auto & [c, d] : found)
        if (! least_hi || d < *least_hi) {
            emit_edge(lo, hi, c, d);
            least_hi = d;
        }

    // maximal contained literals -> self, by the mirrored argument.
    if (lo != hi) {
        found.clear();
        tree.for_each_contained_in(lo, hi, [&](Integer c, Integer d) {
            if (c != lo || d != hi)
                found.emplace_back(c, d);
        });
        sort(found, [](const pair<Integer, Integer> & x, const pair<Integer, Integer> & y) {
            return x.first == y.first ? x.second > y.second : x.first < y.first;
        });
        optional<Integer> greatest_hi;
        for (const auto & [c, d] : found)
            if (! greatest_hi || d > *greatest_hi) {
                emit_edge(c, d, lo, hi);
                greatest_hi = d;
            }
    }
}

auto NamesAndIDsTracker::define_plain_invar(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> void
{
    // Both order-encoding cuts; need_gevar threads them into the order chain, and
    // emits the bound-axiom units for any cut outside the definition bounds.
    need_gevar(id, lo);
    need_gevar(id, hi + 1_i);

    auto x = allocate_xliteral_meaning(id, lo, hi);
    _imp->variable_conditions_to_x.emplace(in_range(id, lo, hi), x);
    _imp->variable_conditions_to_x.emplace(not_in_range(id, lo, hi), ! x);

    auto will_define = _imp->logger->get_assertion_level() <= AssertionLevel::Links;
    // Struggling to get clang-format to behave here...
    auto lines = will_define //
        ? visit(
              [&](const auto & id) {
                  return _imp->logger->emit_red_proof_lines_reifying(
                      WPBSum{} + (1_i * (id >= lo)) + (1_i * ! (id > hi)) >= 2_i, in_range(id, lo, hi), ProofLevel::Top);
              },
              id)
        : make_pair(ProofLine{}, ProofLine{});

    _imp->invars_that_exist[id].emplace(pair{lo, hi}, lines);

    // No containment tree apparatus needed at higher assertion levels.
    if (_imp->logger->get_assertion_level() > AssertionLevel::Links)
        return;

    // Containment edges let a rejected literal propagate down to the literals a
    // conflict is written over; the order chain alone does not give this. The
    // variable's first range literal creates its containment tree, seeded with
    // the eq atoms that already exist.
    if (! _imp->containment_trees.contains(id)) {
        auto & tree = _imp->containment_trees[id];
        if (auto eqit = _imp->eqvars_that_exist.find(id); eqit != _imp->eqvars_that_exist.end())
            for (const auto & [v, _] : eqit->second)
                tree.insert(v, v);
    }
    link_immediate_containment(id, lo, hi);
    _imp->containment_trees[id].insert(lo, hi);
}

auto NamesAndIDsTracker::append_cell_literal_to(WPBSum & sum, SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> void
{
    visit(
        [&](const auto & id) {
            if (lo == hi)
                sum += 1_i * (id == lo);
            else
                sum += 1_i * in_range(id, lo, hi);
        },
        id);
}

auto NamesAndIDsTracker::ensure_partition_cut(SimpleOrProofOnlyIntegerVariableID id, Integer p) -> void
{
    if (_imp->logger->get_assertion_level() > AssertionLevel::Links)
        return;

    auto & boundaries = _imp->interval_partitions.at(id);
    if (boundaries.contains(p))
        return;

    // p falls strictly inside the cell [a, b].
    auto above = boundaries.upper_bound(p);
    auto a = *prev(above), b = *above - 1_i;

    // Insert the boundary before defining the halves: a width-1 half goes through
    // need_direct_encoding_for, whose partition maintenance re-enters here and must
    // see both of its cuts already present (making the re-entry a no-op).
    boundaries.insert(p);

    auto define_cell = [&](Integer cell_lo, Integer cell_hi) {
        if (cell_lo == cell_hi)
            need_direct_encoding_for(id, cell_lo);
        else
            define_plain_invar(id, cell_lo, cell_hi);
    };
    define_cell(a, p - 1_i);
    define_cell(p, b);

    // The split covering: the split cell is no longer a leaf, so unit propagation
    // falsifies it through its two halves. Coverings compose across refinements, so
    // the split cell's appearances in earlier coverings are never revisited.
    WPBSum covering;
    visit([&](const auto & id) { covering += 1_i * not_in_range(id, a, b); }, id);
    append_cell_literal_to(covering, id, a, p - 1_i);
    append_cell_literal_to(covering, id, p, b);
    _imp->logger->emit_rup_proof_line(move(covering) >= 1_i, ProofLevel::Top);
}

auto NamesAndIDsTracker::init_interval_partition(SimpleOrProofOnlyIntegerVariableID id, Integer request_lo, Integer request_hi) -> void
{
    if (_imp->logger->get_assertion_level() > AssertionLevel::Links)
        return;

    auto [lb, ub] = _imp->integer_variable_definition_bounds.at(id);
    auto & boundaries = _imp->interval_partitions[id];
    boundaries.insert(lb);
    boundaries.insert(ub + 1_i);

    // Every pre-existing eq atom becomes a singleton cell, so that coverings can
    // reach conclusions already logged over those atoms.
    if (auto eqit = _imp->eqvars_that_exist.find(id); eqit != _imp->eqvars_that_exist.end())
        for (const auto & [v, _] : eqit->second)
            if (lb <= v && v <= ub) {
                boundaries.insert(v);
                boundaries.insert(v + 1_i);
            }

    boundaries.insert(request_lo);
    boundaries.insert(request_hi + 1_i);

    // Define a literal for every cell, then emit the at-least-one clause over the
    // top-level partition, which gives wipeout detection at the literal level. It is
    // RUP from the bound axioms via the cells' reverse reifications and the order
    // chain.
    WPBSum root_covering;
    for (auto it = boundaries.begin(); next(it) != boundaries.end(); ++it) {
        auto cell_lo = *it, cell_hi = *next(it) - 1_i;
        if (cell_lo == cell_hi)
            need_direct_encoding_for(id, cell_lo);
        else
            define_plain_invar(id, cell_lo, cell_hi);
        append_cell_literal_to(root_covering, id, cell_lo, cell_hi);
    }
    _imp->logger->emit_rup_proof_line(move(root_covering) >= 1_i, ProofLevel::Top);
}

auto NamesAndIDsTracker::need_invar(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> ProofLiteral
{
    if (lo > hi)
        return FalseLiteral{};

    if (lo == hi) {
        need_direct_encoding_for(id, lo);
        return visit([&](const auto & id) -> ProofLiteral { return id == lo; }, id);
    }

    auto as_literal = [&]() { return visit([&](const auto & id) -> ProofLiteral { return in_range(id, lo, hi); }, id); };

    auto & for_this_var = _imp->invars_that_exist[id];
    if (for_this_var.contains(pair{lo, hi}))
        return as_literal();

    if (! _imp->logger)
        throw UnimplementedException{"range literals during model writing are not yet supported"};
    if (! has_bit_representation(id))
        throw ProofError{"range literal requested for a variable without a bits encoding"};

    // The literal is defined over its own two cuts even when they lie outside the
    // definition bounds; the bound-axiom units falsify the out-of-bounds part by
    // unit propagation. The partition only spans the definition range, so the
    // covering is over the cells of the in-bounds intersection.
    auto [lb, ub] = _imp->integer_variable_definition_bounds.at(id);
    auto span_lo = max(lo, lb), span_hi = min(hi, ub);

    if (span_lo > span_hi || _imp->assertion_level > AssertionLevel::Links) {
        // Entirely outside: the reification plus the bound axioms already falsify
        // it, so there is nothing to cover;
        // ...OR we are at a higher assertion level that doesn't need covering apparatus in the first place.
        define_plain_invar(id, lo, hi);
        return as_literal();
    }

    if (! _imp->interval_partitions.contains(id)) {
        init_interval_partition(id, span_lo, span_hi);
    }
    else {
        ensure_partition_cut(id, span_lo);
        ensure_partition_cut(id, span_hi + 1_i);
    }

    // If the request is exactly one cell, it was defined just now.
    const auto & boundaries = _imp->interval_partitions.at(id);
    if (lo == span_lo && hi == span_hi && *next(boundaries.find(span_lo)) == span_hi + 1_i)
        return as_literal();

    // Otherwise define it, with a covering over the in-bounds cells it spans, so
    // that falsifying those pieces falsifies it by unit propagation.
    define_plain_invar(id, lo, hi);
    WPBSum covering;
    visit([&](const auto & id) { covering += 1_i * not_in_range(id, lo, hi); }, id);
    for (auto it = boundaries.find(span_lo); *it != span_hi + 1_i; ++it)
        append_cell_literal_to(covering, id, *it, *next(it) - 1_i);
    _imp->logger->emit_rup_proof_line(move(covering) >= 1_i, ProofLevel::Top);
    return as_literal();
}

auto NamesAndIDsTracker::has_bit_representation(const SimpleOrProofOnlyIntegerVariableID & id) const -> bool
{
    return _imp->integer_variable_bits_to_size_and_proof_vars.contains(id);
}

auto NamesAndIDsTracker::need_view(const ViewOfIntegerVariableID & view) -> ProofOnlySimpleIntegerVariableID
{
    if (auto it = _imp->view_proof_only_vars.find(view); it != _imp->view_proof_only_vars.end())
        return it->second;

    if (! _imp->model)
        throw UnimplementedException{"need_view: view introduction during proof-logging phase is not yet supported"};

    auto bounds_it = _imp->integer_variable_definition_bounds.find(view.actual_variable);
    if (bounds_it == _imp->integer_variable_definition_bounds.end())
        throw ProofError{"need_view: underlying variable's bounds are not registered"};
    auto [x_lo, x_hi] = bounds_it->second;

    auto [v_lo, v_hi] = view.negate_first ? pair{-x_hi + view.then_add, -x_lo + view.then_add} : pair{x_lo + view.then_add, x_hi + view.then_add};

    string name = "view_of_" + name_of(view.actual_variable);
    if (view.negate_first)
        name = "neg_" + name;
    if (view.then_add != 0_i)
        name += "_plus_" + to_string(view.then_add.raw_value);

    auto v_id = _imp->model->create_proof_only_integer_variable(v_lo, v_hi, name, IntegerVariableProofRepresentation::Bits);

    Integer s_coeff = view.negate_first ? -1_i : 1_i;

    // Views must be defined properly in the model. Cake has no view variables, so
    // there is no cake label to match: invent one named after the view, referenced
    // by label rather than line number.
    auto [link_le, link_ge] = _imp->model->add_labelled_constraint(
        "c[" + name + "][viewle]", "c[" + name + "][viewge]", WPBSum{} + 1_i * v_id + (-s_coeff) * view.actual_variable == view.then_add);

    _imp->view_proof_only_vars.emplace(view, v_id);
    _imp->view_proof_only_to_view.emplace(v_id, view);
    _imp->view_link_ids.emplace(v_id, pair{link_le, link_ge});
    _imp->views_of_variable[view.actual_variable].push_back(v_id);

    if (_imp->assertion_level > AssertionLevel::Links) // No further linking needed at higher assertion levels.
        return v_id;

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

auto NamesAndIDsTracker::derive_deviewed_form_for(const ProofLine & v_form_line, const SumOf<Weighted<PseudoBooleanTerm>> & lhs, bool le_half) -> void
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

    if (_imp->assertion_level > AssertionLevel::Links)
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
    // Shared PolBuilder (not a rendered string) so the line refs emit as
    // relative indices -- see make_pol_chain_line above for why.
    auto pol = make_shared<PolBuilder>();
    pol->add(v_form_line);
    for (const auto & vc : view_contributions) {
        auto [link_le, link_ge] = view_link_lines_for(vc.view_proof_id);
        Integer mult = vc.opb_form_coefficient > 0_i ? vc.opb_form_coefficient : -vc.opb_form_coefficient;
        const ProofLine & link_to_use = vc.opb_form_coefficient > 0_i ? link_le : link_ge;
        pol->add(link_to_use, mult);
    }

    emit_proof_line_now_or_at_start([this, v_form_line, pol](ProofLogger * const logger) {
        auto deview_line = pol->emit(*logger, ProofLevel::Top);
        register_deviewed_line(v_form_line, deview_line);
    });
}

auto NamesAndIDsTracker::track_bounds(const SimpleOrProofOnlyIntegerVariableID & id, Integer lower, Integer upper) -> void
{
    _imp->integer_variable_definition_bounds.emplace(id, pair{lower, upper});
}

auto NamesAndIDsTracker::tracked_bounds(const SimpleOrProofOnlyIntegerVariableID & id) const -> pair<Integer, Integer>
{
    return _imp->integer_variable_definition_bounds.at(id);
}

auto NamesAndIDsTracker::note_bounds_not_trivially_derivable(const SimpleOrProofOnlyIntegerVariableID & id) -> void
{
    _imp->bounds_not_trivially_derivable.insert(id);
}

auto NamesAndIDsTracker::note_recover_atom_labels_in_proof(const SimpleOrProofOnlyIntegerVariableID & id) -> void
{
    _imp->vars_recover_labels.insert(id);
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

auto NamesAndIDsTracker::create_proof_flag(const ConstraintID & id, const vector<long long> & indices, const optional<string> & annotation)
    -> ProofFlag
{
    // Mirror cake_pb_cp's Indices flag rendering (cp_to_ilpScript.sml format_flag):
    // x[id][i1_i2..][annotation?] -- the index list joined by '_', the optional
    // annotation in its own brackets.
    string name = "x[" + as_string(id) + "][";
    for (size_t k = 0; k < indices.size(); ++k) {
        if (k != 0)
            name += "_";
        name += to_string(indices[k]);
    }
    name += "]";
    if (annotation)
        name += "[" + *annotation + "]";
    return make_proof_flag_named(name);
}

auto NamesAndIDsTracker::create_proof_flag(const ConstraintID & id, const string & annotation) -> ProofFlag
{
    // Mirror cake_pb_cp's Flag rendering (cp_to_ilpScript.sml format_flag):
    // b[id][annotation] -- a scalar flag carrying only an annotation, no index
    // list. Used where the auxiliary is per-constraint rather than per-position,
    // e.g. not_equals' single `ne` selector b[id][ne]. See #354.
    return make_proof_flag_named("b[" + as_string(id) + "][" + annotation + "]");
}

auto NamesAndIDsTracker::create_proof_flag_values(const ConstraintID & id, const vector<long long> & values, const optional<string> & annotation)
    -> ProofFlag
{
    // Mirror cake_pb_cp's Values flag rendering (cp_to_ilpScript.sml format_flag):
    // v[id][v1_v2..][annotation?] -- the value list joined by '_', the optional
    // annotation in its own brackets. The values are domain values, in contrast
    // to the array positions of the x[...] overload; nvalue's per-value
    // occurrence flag is create_proof_flag_values(id, {v}) -> v[id][v]. See #354.
    string name = "v[" + as_string(id) + "][";
    for (size_t k = 0; k < values.size(); ++k) {
        if (k != 0)
            name += "_";
        // Negative values are rendered `-N`, matching cake's format_int_list and
        // the solver's eq/ge literals (i[X][eq-N]). VeriPB allows '-' in both
        // variable names and @labels (VeriPB-dev #191), so this is legal in the
        // labelled flag definitions too and byte-matches cake over negative
        // domains.
        name += to_string(values[k]);
    }
    name += "]";
    if (annotation)
        name += "[" + *annotation + "]";
    return make_proof_flag_named(name);
}

auto NamesAndIDsTracker::create_proof_flag_for_constant(Integer k, const string & atom) -> ProofFlag
{
    // Mirror cake_pb_cp's constant-atom rendering (cp_encScript.sml format_var,
    // Ge/Eq over a constant): n[<k>][<atom>], the constant rendered with a
    // leading '-' when negative, exactly like the eq/ge literal values.
    return make_proof_flag_named("n[" + to_string(k.raw_value) + "][" + atom + "]");
}

auto NamesAndIDsTracker::make_proof_flag_named(const string & full_name) -> ProofFlag
{
    // The supplied name is used verbatim as the PB-file variable name (rather
    // than wrapped in `f[index][...]`), so the same string is both the tracked
    // name and the verbose rendering. See the header for why.
    ProofFlag result{allocate_flag_index(), true};
    track_variable_name(result, full_name);
    auto flagvar = allocate_flag_xliteral(result, full_name);
    _imp->flags.emplace(result, flagvar);
    _imp->flags.emplace(! result, ! flagvar);
    return result;
}

auto NamesAndIDsTracker::store_xlit_names(const XLiteral & lit, string name) -> void
{
    // `name` renders the positive polarity; the negation is always `~name`.
    auto idx = static_cast<vector<string>::size_type>(lit.id) * 2;
    if (_imp->xlit_names.size() < idx + 2)
        _imp->xlit_names.resize(idx + 2);
    _imp->xlit_names[idx + 1] = "~" + name;
    _imp->xlit_names[idx] = move(name);
}

auto NamesAndIDsTracker::pb_file_string_for(const XLiteral & lit) const -> const string &
{
    auto idx = static_cast<vector<string>::size_type>(lit.id) * 2 + (lit.negated ? 1 : 0);
    if (idx >= _imp->xlit_names.size() || _imp->xlit_names[idx].empty())
        throw ProofError("missing name for xliteral " + to_string(lit.id) + " " + to_string(lit.negated));
    return _imp->xlit_names[idx];
}

auto NamesAndIDsTracker::pb_file_string_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) const -> const string &
{
    return pb_file_string_for(xliteral_for(cond));
}

auto NamesAndIDsTracker::bit_assignment_string_for(const SimpleOrProofOnlyIntegerVariableID & var, const Integer & value) const -> string
{
    auto it = _imp->integer_variable_bits_to_size_and_proof_vars.find(var);
    if (it == _imp->integer_variable_bits_to_size_and_proof_vars.end())
        throw ProofError("missing bits");

    const auto & [negative_coeff, bits] = it->second;

    bool sign_bit_set = (negative_coeff != 0_i) && (value < 0_i);
    Integer remainder = sign_bit_set ? value - negative_coeff : value;

    string result;
    for (const auto & [coeff, lit] : bits) {
        bool bit_is_one = (coeff < 0_i) ? sign_bit_set : ((remainder / coeff) % 2_i == 1_i);
        if (! result.empty())
            result += " ";
        result += pb_file_string_for(bit_is_one ? lit : ! lit);
    }

    return result;
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

auto NamesAndIDsTracker::pb_file_string_for(const ProofFlag & flag) const -> const string &
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

auto NamesAndIDsTracker::allocate_xliteral_meaning(SimpleOrProofOnlyIntegerVariableID id, const EqualsOrGreaterEqual & op, Integer value) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        // Negative values render as `-N` (matching cake); '-' is legal in both
        // VeriPB variable names and @labels (VeriPB-dev #191).
        string value_name = value.to_string();

        overloaded{
            [&](const SimpleIntegerVariableID & id) -> void {
                string name = format("i[{}][{}{}]", name_of(id), (op == EqualsOrGreaterEqual::Equals ? "eq" : "ge"), value_name);
                store_xlit_names(result, name);
            }, //
            [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                string name = format("p[{}_{}][{}{}]", id.index, name_of(id), (op == EqualsOrGreaterEqual::Equals ? "eq" : "ge"), value_name);
                store_xlit_names(result, name);
            } //
        }
            .visit(id);
    }
    else
        store_xlit_names(result, "x" + to_string(result.id));

    if (_imp->variables_map_file) {
        try {
            nlohmann::json data;
            data["type"] = "condition";
            overloaded{
                [&](const SimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "intvar";
                    data["cpvarid"] = id.index;
                }, //
                [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "proofintvar";
                    data["cpvarid"] = id.index;
                } //
            }
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

auto NamesAndIDsTracker::allocate_xliteral_meaning(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        // Negative values render as `-N` (matching cake); '-' is legal in both
        // VeriPB variable names and @labels (VeriPB-dev #191).
        auto value_name = [](Integer v) { return v.to_string(); };

        overloaded{
            [&](const SimpleIntegerVariableID & id) -> void {
                string name = format("i[{}][in{}_{}]", name_of(id), value_name(lo), value_name(hi));
                store_xlit_names(result, name);
            }, //
            [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                string name = format("p[{}_{}][in{}_{}]", id.index, name_of(id), value_name(lo), value_name(hi));
                store_xlit_names(result, name);
            } //
        }
            .visit(id);
    }
    else
        store_xlit_names(result, "x" + to_string(result.id));

    if (_imp->variables_map_file) {
        try {
            nlohmann::json data;
            data["type"] = "condition";
            overloaded{
                [&](const SimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "intvar";
                    data["cpvarid"] = id.index;
                }, //
                [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "proofintvar";
                    data["cpvarid"] = id.index;
                } //
            }
                .visit(id);

            data["name"] = name_of(id);
            data["operator"] = "in";
            data["value"] = lo.raw_value;
            data["upper_value"] = hi.raw_value;

            write_vardata(*_imp->variables_map_file, _imp->first_varmap_entry, pb_file_string_for(result), data);
        }
        catch (const ios_base::failure &) {
            throw ProofError{"Error writing proof variables mapping file to '" + _imp->variables_map_file_name + "'"};
        }
    }

    return result;
}

auto NamesAndIDsTracker::allocate_flag_xliteral(ProofFlag flag, const string & verbose_name) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        store_xlit_names(result, verbose_name);
    }
    else
        store_xlit_names(result, "x" + to_string(result.id));

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

auto NamesAndIDsTracker::allocate_xliteral_meaning(ProofFlag flag) -> XLiteral
{
    return allocate_flag_xliteral(flag, format("f[{}][{}]", flag.index, name_of(flag)));
}

auto NamesAndIDsTracker::allocate_xliteral_meaning_negative_bit_of(
    SimpleOrProofOnlyIntegerVariableID id, Integer power, const optional<string> & name_override) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        string name = name_override
            ? *name_override
            : visit(overloaded{                                                                                 //
                        [&](const SimpleIntegerVariableID & id) { return format("i[{}][sign]", name_of(id)); }, //
                        [&](const ProofOnlySimpleIntegerVariableID & id) { return format("p[{}_{}][sign]", id.index, name_of(id)); }},
                  id);
        store_xlit_names(result, name);
    }
    else
        store_xlit_names(result, "x" + to_string(result.id));

    if (_imp->variables_map_file) {
        try {
            nlohmann::json data;
            data["type"] = "intvarnegbit";
            overloaded{
                [&](const SimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "intvar";
                    data["cpvarid"] = id.index;
                }, //
                [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "proofintvar";
                    data["cpvarid"] = id.index;
                } //
            }
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

auto NamesAndIDsTracker::allocate_xliteral_meaning_bit_of(
    SimpleOrProofOnlyIntegerVariableID id, Integer power, const optional<string> & name_override) -> XLiteral
{
    auto result = XLiteral{++_imp->next_xliteral_nr, false};

    if (_imp->verbose_names) {
        // name_override lets a proof-only variable's bits be named in a caller-chosen
        // scheme (cake_pb_cp's value flags) rather than the default p[index_name][b];
        // the literal is still the variable's bit, only named.
        string name = name_override
            ? *name_override
            : visit(overloaded{                                                                                       //
                        [&](const SimpleIntegerVariableID & id) { return format("i[{}][b{}]", name_of(id), power); }, //
                        [&](const ProofOnlySimpleIntegerVariableID & id) { return format("p[{}_{}][b{}]", id.index, name_of(id), power); }},
                  id);
        store_xlit_names(result, name);
    }
    else
        store_xlit_names(result, "x" + to_string(result.id));

    if (_imp->variables_map_file) {
        try {
            nlohmann::json data;
            data["type"] = "intvarbit";
            overloaded{
                [&](const SimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "intvar";
                    data["cpvarid"] = id.index;
                }, //
                [&](const ProofOnlySimpleIntegerVariableID & id) -> void {
                    data["cpvartype"] = "proofintvar";
                    data["cpvarid"] = id.index;
                } //
            }
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
        [&](const ConstantIntegerVariableID & c) -> string { return c.const_value.to_string(); }, //
        [&](const SimpleIntegerVariableID & v) -> string { return name_of(v); },                  //
        [&](const ViewOfIntegerVariableID & vv) -> string {
            stringstream name;
            name << "(";
            name << (vv.negate_first ? "-" : "");
            name << name_of(vv.actual_variable) << " + " << vv.then_add << ")";
            return name.str();
        } //
    }
        .visit(id);
}

auto NamesAndIDsTracker::s_expr_name_of(Literal lit) const -> string
{
    return overloaded{
        [](const TrueLiteral &) -> string { return "1"; },                                                                //
        [](const FalseLiteral &) -> string { return "0"; },                                                               //
        [&](const VariableConditionFrom<SimpleIntegerVariableID> & cond) -> string { return s_expr_name_of(cond.var); },  //
        [](const VariableConditionFrom<ProofOnlySimpleIntegerVariableID> &) -> string { throw UnimplementedException{}; } //
    }
        .visit(simplify_literal(*this, lit));
}

auto NamesAndIDsTracker::s_expr_name_of(ReificationCondition cond) const -> string
{
    return overloaded{
        [](const reif::MustHold &) -> string { return ""; },    //
        [](const reif::MustNotHold &) -> string { return ""; }, //
        [&](const auto & reif) -> string {                      // This is safe, right?
            return "(" + s_expr_name_of(reif.cond.var) + " " + s_expr_name_of(reif.cond.op) + " " + reif.cond.value.to_string() + ")";
        } //
    }
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
    case InRange:
    case NotInRange:
        // cake_pb_cp has no range-condition spelling yet, and range conditions
        // cannot appear in reified constraints (model-phase need_invar throws)
        throw UnimplementedException{};
    }

    throw NonExhaustiveSwitch{};
}

auto NamesAndIDsTracker::s_expr_render_of(IntegerVariableID id) const -> string
{
    return overloaded{
        [&](const ConstantIntegerVariableID & c) -> string { return "(minimize " + c.const_value.to_string() + ")"; }, //
        [&](const SimpleIntegerVariableID & v) -> string { return "(minimize " + name_of(v) + ")"; },                  //
        [&](const ViewOfIntegerVariableID & vv) -> string {
            return "(" + string{vv.negate_first ? "maximize" : "minimize"} + " " + name_of(vv.actual_variable) + ")";
        } //
    }
        .visit(id);
}

auto NamesAndIDsTracker::s_expr_term_of(IntegerVariableID id) const -> SExpr
{
    // A variable / literal name is always a single, non-empty s-expression term
    // (a bare atom like `_1`, or a list like a view `(-_1 + 17)`), so parsing it
    // can't fail or be empty.
    return parse_s_expr(s_expr_name_of(id));
}

auto NamesAndIDsTracker::s_expr_term_of(Literal lit) const -> SExpr
{
    // As for the variable overload: s_expr_name_of(Literal) is always a single,
    // non-empty term (a bare atom for a condition/True/False, or a view list).
    return parse_s_expr(s_expr_name_of(lit));
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
    WPBSumLE result{{}, 0_i};
    reify_into(ineq, half_reif, result);
    return result;
}

auto NamesAndIDsTracker::reify_into(const WPBSumLE & ineq, const HalfReifyOnConjunctionOf & half_reif, WPBSumLE & out) -> void
{
    // so what happens if there's a false literal in the left hand term? conceptually,
    // this means the constraint will always hold, but it's probably useful to have
    // something that syntactically contains all the right variables. so, we can just
    // make the degree of falsity be very low so the constraint always holds.
    bool contains_false_literal = any_of(half_reif.begin(), half_reif.end(), [&](const auto & flag) {
        return overloaded{
            [&](const ProofFlag &) { return false; }, //
            [&](const ProofLiteral & pl) {
                return overloaded{
                    [&](Literal lit) { return is_literally_false(lit); },  //
                    [&](const ProofVariableCondition &) { return false; }, //
                }
                    .visit(pl);
            },                                              //
            [&](const ProofBitVariable &) { return false; } //
        }
            .visit(flag);
    });

    // work out how big the reification constant needs to be, by adding together
    // positive terms in the inequality and negating
    Integer max_contribution_from_positive_terms = 0_i;

    for (auto & [w, v] : ineq.lhs.terms) {
        overloaded{
            [&, w = w](const ProofLiteral &) { max_contribution_from_positive_terms += max(0_i, w); }, //
            [&, w = w](const ProofFlag &) { max_contribution_from_positive_terms += max(0_i, w); },    //
            [&, w = w](const IntegerVariableID & var) {
                overloaded{
                    [&](const SimpleIntegerVariableID & var) {
                        for (const auto & [bit_value, bit_lit] : each_bit(var))
                            max_contribution_from_positive_terms += max(0_i, w * bit_value);
                    }, //
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
                    },                                                                                                                      //
                    [&](const ConstantIntegerVariableID & cvar) { max_contribution_from_positive_terms += max(0_i, w * cvar.const_value); } //
                }
                    .visit(var);
            }, //
            [&, w = w](const ProofOnlySimpleIntegerVariableID & var) {
                for (const auto & [bit_value, bit_lit] : each_bit(var))
                    max_contribution_from_positive_terms += max(0_i, w * bit_value);
            },                                                                                             //
            [&, w = w](const ProofBitVariable &) { max_contribution_from_positive_terms += max(0_i, w); }, //
        }
            .visit(v);
    }

    // Usually it would be fine to say 0_i rather than -1_i here, because if a constraint
    // is trivially true, it doesn't really matter whether the implication is there or
    // not. However, for syntactic wrangling reasons, we probably want the implication
    // to always be there.
    auto clamped_reif_const = min(-max_contribution_from_positive_terms + ineq.rhs, -1_i);

    auto & new_lhs = out.lhs;
    new_lhs.terms.clear();
    new_lhs.terms.reserve(ineq.lhs.terms.size() + half_reif.size());
    new_lhs.terms.insert(new_lhs.terms.end(), ineq.lhs.terms.begin(), ineq.lhs.terms.end());
    for (auto & r : half_reif)
        overloaded{
            [&](const ProofFlag & f) { new_lhs += clamped_reif_const * ! f; },           //
            [&](const ProofLiteral & lit) { new_lhs += clamped_reif_const * ! lit; },    //
            [&](const ProofBitVariable & bit) { new_lhs += clamped_reif_const * ! bit; } //
        }
            .visit(r);

    // if we have a false literal on the left hand side, adjusting the degree of falsity
    // up by the sum of positive terms is enough that it will be trivially true.
    if (contains_false_literal)
        out.rhs = ineq.rhs + max_contribution_from_positive_terms;
    else
        out.rhs = ineq.rhs;
}
