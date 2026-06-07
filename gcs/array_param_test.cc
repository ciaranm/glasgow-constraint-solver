#include <gcs/array_param.hh>

#include <catch2/catch_test_macros.hpp>

#include <memory>
#include <vector>

using namespace gcs;

using std::make_shared;
using std::shared_ptr;
using std::vector;

TEST_CASE("ArrayParam: owned construction moves data in")
{
    vector<int> v{1, 2, 3};
    ArrayParam<vector<int>> a{std::move(v)};
    CHECK(*a == vector<int>{1, 2, 3});
    CHECK(a->size() == 3);
}

TEST_CASE("ArrayParam: initializer_list construction")
{
    ArrayParam<vector<int>> a{4, 5, 6};
    CHECK(*a == vector<int>{4, 5, 6});
}

TEST_CASE("ArrayParam: shared construction reuses the same storage")
{
    auto shared = make_shared<const vector<int>>(vector<int>{7, 8});
    ArrayParam<vector<int>> a{shared};
    ArrayParam<vector<int>> b{shared};
    // Both handles point at the one shared vector, with no copy.
    CHECK(&*a == shared.get());
    CHECK(&*b == shared.get());
    CHECK(shared.use_count() == 3); // shared + a + b
}

TEST_CASE("ArrayParam: borrowed construction owns nothing")
{
    vector<int> external{9, 10, 11};
    ArrayParam<vector<int>> a{&external};
    // Aliases external storage directly; no copy, no ownership.
    CHECK(&*a == &external);
    CHECK(*a == vector<int>{9, 10, 11});
}

TEST_CASE("ArrayParam: copying a handle shares, and a copy outlives the original")
{
    ArrayParam<vector<int>> original{vector<int>{1, 2, 3}};
    const vector<int> * data = &*original;
    {
        ArrayParam<vector<int>> copy = original;
        CHECK(&*copy == data); // copy points at the same storage
    }
    // original still valid after the copy is gone.
    CHECK(*original == vector<int>{1, 2, 3});
}
