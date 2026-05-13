#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/integer.hh>

#include <catch2/catch_test_macros.hpp>

using namespace gcs;
using namespace gcs::innards;

TEST_CASE("PolBuilder: empty")
{
    PolBuilder b;
    CHECK(b.empty());
    CHECK(b.str() == "pol ;");
}

TEST_CASE("PolBuilder: single line")
{
    PolBuilder b;
    b.add(ProofLineNumber{7});
    CHECK_FALSE(b.empty());
    CHECK(b.str() == "pol 7 ;");
}

TEST_CASE("PolBuilder: two-line sum")
{
    PolBuilder b;
    b.add(ProofLineNumber{3}).add(ProofLineNumber{5});
    CHECK(b.str() == "pol 3 5 + ;");
}

TEST_CASE("PolBuilder: three-line sum")
{
    PolBuilder b;
    b.add(ProofLineNumber{1}).add(ProofLineNumber{2}).add(ProofLineNumber{3});
    CHECK(b.str() == "pol 1 2 + 3 + ;");
}

TEST_CASE("PolBuilder: sum then saturate")
{
    PolBuilder b;
    b.add(ProofLineNumber{1}).add(ProofLineNumber{2}).saturate();
    CHECK(b.str() == "pol 1 2 + s ;");
}

TEST_CASE("PolBuilder: weighted sum")
{
    PolBuilder b;
    // First a bare leading term, then weighted ones — mirrors cumulative.cc.
    b.add(ProofLineNumber{10})
        .add(ProofLineNumber{20}, 3_i)
        .add(ProofLineNumber{30}, 5_i);
    CHECK(b.str() == "pol 10 20 3 * + 30 5 * + ;");
}

TEST_CASE("PolBuilder: coefficient 1 elides the multiplier")
{
    PolBuilder b;
    b.add(ProofLineNumber{4}, 1_i).add(ProofLineNumber{5}, 1_i);
    CHECK(b.str() == "pol 4 5 + ;");
}

TEST_CASE("PolBuilder: coefficient 0 rejected")
{
    PolBuilder b;
    CHECK_THROWS(b.add(ProofLineNumber{1}, 0_i));
}

TEST_CASE("PolBuilder: running saturate (first push not saturated)")
{
    PolBuilder b;
    // Mirrors circuit_scc.cc::PLine::add_and_saturate: first push is the
    // base, subsequent pushes get "+ s" each.
    b.add_and_saturate(ProofLineNumber{1})
        .add_and_saturate(ProofLineNumber{2})
        .add_and_saturate(ProofLineNumber{3});
    CHECK(b.str() == "pol 1 2 + s 3 + s ;");
}

TEST_CASE("PolBuilder: multiply_by on top of stack")
{
    PolBuilder b;
    // recover_am1 pattern: multiply running result by a layer count between rounds.
    b.add(ProofLineNumber{1}).multiply_by(3_i).add(ProofLineNumber{2});
    CHECK(b.str() == "pol 1 3 * 2 + ;");
}

TEST_CASE("PolBuilder: divide_by at end")
{
    PolBuilder b;
    b.add(ProofLineNumber{1}).add(ProofLineNumber{2}).divide_by(3_i);
    CHECK(b.str() == "pol 1 2 + 3 d ;");
}

TEST_CASE("PolBuilder: reusable across clear")
{
    PolBuilder b;
    b.add(ProofLineNumber{1}).add(ProofLineNumber{2});
    CHECK(b.str() == "pol 1 2 + ;");

    b.clear();
    CHECK(b.empty());

    b.add(ProofLineNumber{9});
    CHECK(b.str() == "pol 9 ;");
}

TEST_CASE("PolBuilder: str is non-mutating")
{
    PolBuilder b;
    b.add(ProofLineNumber{1}).add(ProofLineNumber{2});
    CHECK(b.str() == "pol 1 2 + ;");
    CHECK(b.str() == "pol 1 2 + ;");
    CHECK_FALSE(b.empty());
}
