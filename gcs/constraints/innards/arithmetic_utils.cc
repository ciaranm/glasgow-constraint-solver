#include <gcs/constraints/innards/arithmetic_utils.hh>

#include <deque>
#include <mutex>

using std::deque;
using std::lock_guard;
using std::mutex;
using std::string;
using std::to_string;

auto gcs::innards::child_constraint_id(const ConstraintID & parent, const string & role) -> ConstraintID
{
    // The pool is never freed: NamedConstraint holds a string_view, and ids
    // are copied around freely, so the names must live for the rest of the
    // process. The counter makes every child id globally unique even when
    // the parent is itself unnamed. Deterministic for a fixed sequence of
    // solves, which is all proof reproducibility needs.
    static mutex pool_mutex;
    static deque<string> pool;
    static unsigned long long counter = 0;

    lock_guard<mutex> guard{pool_mutex};
    pool.push_back(as_string(parent) + "_" + role + "_" + to_string(counter++));
    return NamedConstraint{pool.back()};
}
