/* Published constraint rows: does a role a constraint publishes actually name a
 * row the .opb contains, and can a proof step cite it?
 *
 * This is the contract behind Problem::each_constraint_of_type_with_proof_data.
 * It has two halves, and each is only worth having because the other exists:
 *
 *   - ConstraintProofModelData<C>::primary_row_role says which row of C's OPB
 *     output a citer means. It is a second visit over the same reification
 *     condition define_proof_model visits, so the two can drift apart --- and if
 *     they do, a presolver builds a pol on a row that says something else, or on
 *     a row that is not there.
 *
 *   - NamesAndIDsTracker::constraint_row_label says whether a row was emitted
 *     under that (id, role). It reads the set ProofModel::claim_labels claims
 *     into, so it is exactly as truthful as the emission path.
 *
 * The tests below post one constraint of each reification kind of both
 * published families, resolve the label through the real API, and then check the
 * answer against the .opb text: a resolved label must appear in the file, and a
 * nullopt must mean no row under that name is in it. Nothing here trusts the
 * roles to be right by inspection; the file is the oracle.
 */

#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/innards/proofs/constraint_proof_model_data.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/presolver.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <catch2/catch_test_macros.hpp>
#include <catch2/catch_tostring.hpp>

#include <cstdio>
#include <fstream>
#include <iterator>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace std::string_literals;

using gcs::innards::ConstraintProofModelData;
using gcs::innards::ProofLineLabel;

using std::ifstream;
using std::istreambuf_iterator;
using std::make_optional;
using std::make_unique;
using std::nullopt;
using std::optional;
using std::string;
using std::unique_ptr;
using std::vector;

namespace
{
    // What one enumerated constraint looked like to a citer: the role it
    // published, and the label that role resolved to.
    struct Resolved final
    {
        string id;
        optional<string> role;
        optional<string> label;
    };

    // A presolver exists purely so that this test runs at the point a real
    // presolver runs: after define_proof_model has emitted every row and
    // claimed every label, with a ProofLogger and no ProofModel. Resolving a
    // label anywhere else would be testing a different question.
    template <typename Constraint_>
    struct CapturingPresolver final : Presolver
    {
        vector<Resolved> * out;

        explicit CapturingPresolver(vector<Resolved> * o) : out(o)
        {
        }

        auto run(Problem & problem, innards::Propagators &, innards::State &, innards::ProofLogger * const logger) -> bool override
        {
            for (const auto & [c, label] : problem.each_constraint_of_type_with_proof_data<Constraint_>(logger))
                out->push_back(Resolved{as_string(c.constraint_id()), ConstraintProofModelData<Constraint_>::primary_row_role(c),
                    label.transform([](const ProofLineLabel & l) { return l.label; })});
            return true;
        }

        [[nodiscard]] auto clone() const -> unique_ptr<Presolver> override
        {
            return make_unique<CapturingPresolver>(out);
        }
    };

    [[nodiscard]] auto read_file(const string & name) -> string
    {
        ifstream f{name, std::ios::binary};
        REQUIRE(f);
        return string{istreambuf_iterator<char>{f}, istreambuf_iterator<char>{}};
    }

    // Does the .opb contain a row emitted under this label? A label is written
    // as the first token of its row, so anchoring on "@<label> " avoids
    // "@c[_1]" matching a row actually labelled "@c[_1][r]".
    [[nodiscard]] auto opb_has_row_labelled(const string & opb, const string & label) -> bool
    {
        auto needle = "@" + label + " ";
        for (size_t pos = 0; pos != string::npos;) {
            if (opb.compare(pos, needle.size(), needle) == 0)
                return true;
            auto line_end = opb.find('\n', pos);
            pos = line_end == string::npos ? string::npos : line_end + 1;
        }
        return false;
    }

    // Solve with proofs on, running a CapturingPresolver over Constraint_, and
    // return what it saw together with the .opb it saw it against.
    template <typename Constraint_>
    struct Run final
    {
        vector<Resolved> resolved;
        string opb;
    };

    template <typename Constraint_, typename Post_>
    [[nodiscard]] auto run_with_proof(const string & basename, Post_ && post) -> Run<Constraint_>
    {
        Run<Constraint_> result;
        Problem p;
        post(p);
        p.add_presolver(CapturingPresolver<Constraint_>{&result.resolved});
        // No .scp: s_expr() throws on the MustNotHold and NotIf forms of both
        // families, which have no cake_pb_cp spelling --- and those are exactly
        // the forms this has to cover, since they are the ones whose row states
        // something other than what its label suggests. The .opb is written
        // either way, and the .opb is the oracle here.
        ProofFileNames names{basename};
        names.s_expr_file = nullopt;
        static_cast<void>(
            solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; }}, make_optional<ProofOptions>(names)));
        result.opb = read_file(basename + ".opb");
        for (const auto & suffix : {".opb"s, ".pbp"s, ".scp"s, ".varmap"s})
            std::remove((basename + suffix).c_str());
        return result;
    }

    // The check both families share: a published role that resolved must name a
    // row the file contains, and a role that resolved to nothing must not.
    template <typename Constraint_>
    auto check_labels_against_opb(const Run<Constraint_> & run) -> void
    {
        for (const auto & r : run.resolved) {
            CAPTURE(r.id);
            CAPTURE(r.role.value_or("<none published>"));
            CAPTURE(r.label.value_or("<unresolved>"));

            if (r.label) {
                // Resolving is a claim about the file, so check the file.
                CHECK(opb_has_row_labelled(run.opb, *r.label));
                // And a label only ever comes from a published role.
                CHECK(r.role.has_value());
            }
            else if (r.role) {
                // A role published but nothing emitted under it: then the file
                // must really not contain that row, or the tracker is lying.
                auto expected = "c[" + r.id + "]" + (r.role->empty() ? "" : "[" + *r.role + "]");
                CHECK_FALSE(opb_has_row_labelled(run.opb, expected));
            }
        }
    }
}

TEST_CASE("a linear's published role resolves to a row the .opb contains")
{
    auto run = run_with_proof<ReifiedLinearInequality>("constraint_row_test_linear", [](Problem & p) {
        auto x = p.create_integer_variable(0_i, 10_i, "x"s);
        auto y = p.create_integer_variable(0_i, 10_i, "y"s);
        auto b = p.create_integer_variable(0_i, 1_i, "b"s);
        p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x + -1_i * y, 3_i});
        p.post(LinearLessThanEqualIf{WeightedSum{} + 1_i * y + -1_i * x, 4_i, b == 1_i});
        p.post(LinearLessThanEqualIff{WeightedSum{} + 1_i * x + 1_i * y, 12_i, b == 0_i});
        // No derived class reaches these two, so they are posted directly.
        p.post(ReifiedLinearInequality{WeightedSum{} + 1_i * x + 1_i * y, 4_i, reif::MustNotHold{}});
        p.post(ReifiedLinearInequality{WeightedSum{} + 1_i * x + -1_i * y, 2_i, reif::NotIf{b == 1_i}});
    });

    // Five posted, five enumerated: the enumeration is the same one the
    // presolver uses, so a shortfall here would be a different bug.
    REQUIRE(run.resolved.size() == 5);
    check_labels_against_opb(run);

    // MustHold and If publish the empty role and resolve; the other three
    // publish nothing, because none of their rows is the `sum <= value` a citer
    // means. Iff's r and f halves say the two directions of the equivalence, and
    // MustNotHold's and NotIf's rows both state the integer negation --- which
    // is the thing those forms enforce, so it is the right row for them to have
    // and the wrong one to hand a citer.
    CHECK(run.resolved[0].role == make_optional(""s));
    CHECK(run.resolved[0].label.has_value());
    CHECK(run.resolved[1].role == make_optional(""s));
    CHECK(run.resolved[1].label.has_value());
    for (auto i : {2u, 3u, 4u}) {
        CAPTURE(i);
        CHECK_FALSE(run.resolved[i].role.has_value());
        CHECK_FALSE(run.resolved[i].label.has_value());
    }

    // The three non-publishing donors really did emit rows --- publishing no
    // role is not the same as having emitted nothing. Without this the previous
    // check would pass just as well against a constraint that emitted no model
    // at all. MustNotHold's goes out under the empty role, exactly the label a
    // build-it-yourself citer would construct; publishing is what keeps it out
    // of a pol.
    CHECK(opb_has_row_labelled(run.opb, "c[" + run.resolved[2].id + "][r]"));
    CHECK(opb_has_row_labelled(run.opb, "c[" + run.resolved[2].id + "][f]"));
    CHECK(opb_has_row_labelled(run.opb, "c[" + run.resolved[3].id + "]"));
    CHECK(opb_has_row_labelled(run.opb, "c[" + run.resolved[4].id + "][ltn]"));
}

TEST_CASE("a comparison's published role resolves to a row the .opb contains")
{
    auto run = run_with_proof<ReifiedCompareLessThanOrMaybeEqual>("constraint_row_test_comparison", [](Problem & p) {
        auto x = p.create_integer_variable(0_i, 10_i, "x"s);
        auto y = p.create_integer_variable(0_i, 10_i, "y"s);
        auto z = p.create_integer_variable(0_i, 10_i, "z"s);
        auto b = p.create_integer_variable(0_i, 1_i, "b"s);
        p.post(LessThanEqual{x, y});
        p.post(LessThan{y, z});
        p.post(LessThanEqualIf{z, x + 6_i, b == 1_i});
        p.post(ReifiedCompareLessThanOrMaybeEqual{x, z, reif::Iff{b == 0_i}, true});
        p.post(ReifiedCompareLessThanOrMaybeEqual{y, x, reif::NotIf{b == 1_i}, true});
    });

    REQUIRE(run.resolved.size() == 5);
    check_labels_against_opb(run);

    // MustHold (twice) and If publish the empty role.
    for (auto i : {0u, 1u, 2u}) {
        CAPTURE(i);
        CHECK(run.resolved[i].role == make_optional(""s));
        CHECK(run.resolved[i].label.has_value());
    }

    // Iff publishes nothing (r and f halves), and NotIf publishes nothing even
    // though its row *is* under the empty role: that row states the negated
    // inequality with the operands the other way round, so it is not the row a
    // citer asking for `left <= right` means. This is the case a
    // build-the-label-yourself citer gets wrong, and it is the reason the role
    // is published rather than constructed.
    CHECK_FALSE(run.resolved[3].role.has_value());
    CHECK_FALSE(run.resolved[3].label.has_value());
    CHECK_FALSE(run.resolved[4].role.has_value());
    CHECK_FALSE(run.resolved[4].label.has_value());

    // The NotIf donor did emit a row, under exactly the label a naive citer
    // would have built. Publishing is what keeps it out of a pol.
    CHECK(opb_has_row_labelled(run.opb, "c[" + run.resolved[4].id + "]"));
}

TEST_CASE("no label resolves when proofs are off")
{
    // The same posting, with no ProofOptions. Nothing is emitted, so nothing is
    // citable, and a caller must see that rather than a label it could not have
    // cited. This is what stops a presolver behaving differently under --prove.
    vector<Resolved> resolved;
    Problem p;
    auto x = p.create_integer_variable(0_i, 10_i, "x"s);
    auto y = p.create_integer_variable(0_i, 10_i, "y"s);
    p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x + -1_i * y, 3_i});
    p.add_presolver(CapturingPresolver<ReifiedLinearInequality>{&resolved});
    static_cast<void>(solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; }}));

    REQUIRE(resolved.size() == 1);
    // The role is still published --- it is a property of the constraint, not of
    // whether a proof is being written --- but there is no row to resolve to.
    CHECK(resolved[0].role == make_optional(""s));
    CHECK_FALSE(resolved[0].label.has_value());
}

TEST_CASE("a role that names no emitted row does not resolve")
{
    // The tracker's half, on its own: ask for a role nothing was emitted under
    // and get nullopt rather than a constructed label. Uses a role no
    // constraint uses, on a constraint id that does exist, so the only thing
    // wrong with it is that no row carries it.
    vector<Resolved> resolved;
    Problem p;
    auto x = p.create_integer_variable(0_i, 10_i, "x"s);
    auto y = p.create_integer_variable(0_i, 10_i, "y"s);
    p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x + -1_i * y, 3_i});

    struct AskingPresolver final : Presolver
    {
        optional<ProofLineLabel> * real;
        optional<ProofLineLabel> * invented;

        AskingPresolver(optional<ProofLineLabel> * r, optional<ProofLineLabel> * i) : real(r), invented(i)
        {
        }

        auto run(Problem & problem, innards::Propagators &, innards::State &, innards::ProofLogger * const logger) -> bool override
        {
            for (const auto & c : problem.each_constraint_of_type<ReifiedLinearInequality>()) {
                *real = innards::constraint_row_label_from(*logger, c.constraint_id(), ""s);
                *invented = innards::constraint_row_label_from(*logger, c.constraint_id(), "no_such_role"s);
            }
            return true;
        }

        [[nodiscard]] auto clone() const -> unique_ptr<Presolver> override
        {
            return make_unique<AskingPresolver>(real, invented);
        }
    };

    optional<ProofLineLabel> real, invented;
    p.add_presolver(AskingPresolver{&real, &invented});
    static_cast<void>(solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; }},
        make_optional<ProofOptions>(ProofFileNames{"constraint_row_test_missing_role"})));
    for (const auto & suffix : {".opb"s, ".pbp"s, ".scp"s, ".varmap"s})
        std::remove(("constraint_row_test_missing_role"s + suffix).c_str());

    CHECK(real.has_value());
    CHECK_FALSE(invented.has_value());
}
