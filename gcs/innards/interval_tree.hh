#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INTERVAL_TREE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INTERVAL_TREE_HH

#include <gcs/integer.hh>

#include <memory>
#include <random>
#include <utility>

namespace gcs::innards
{
    /**
     * \brief A set of closed integer intervals supporting insertion and
     * containment queries: visit every stored interval that contains a query
     * interval, and every stored interval that is contained in one.
     *
     * Implemented as a treap keyed on (lo, hi), augmented with the minimum and
     * maximum interval end in each subtree, so both query directions can prune
     * subtrees that cannot match. Priorities come from a fixed-seed generator,
     * keeping the structure (and so anything emitted while traversing it)
     * deterministic across runs. There is no deletion: defined proof literals
     * are never taken back.
     *
     * \ingroup Innards
     */
    class IntervalTree
    {
    private:
        struct Node
        {
            Integer lo, hi;
            Integer min_hi, max_hi;
            unsigned long long priority;
            std::unique_ptr<Node> left, right;

            Node(Integer l, Integer h, unsigned long long p) : lo(l), hi(h), min_hi(h), max_hi(h), priority(p)
            {
            }
        };

        std::unique_ptr<Node> _root;
        std::mt19937_64 _priorities{12345};

        static auto update(Node & n) -> void
        {
            n.min_hi = n.hi;
            n.max_hi = n.hi;
            for (auto * child : {n.left.get(), n.right.get()})
                if (child) {
                    n.min_hi = std::min(n.min_hi, child->min_hi);
                    n.max_hi = std::max(n.max_hi, child->max_hi);
                }
        }

        static auto rotate_left(std::unique_ptr<Node> & n) -> void
        {
            auto r = std::move(n->right);
            n->right = std::move(r->left);
            update(*n);
            r->left = std::move(n);
            n = std::move(r);
            update(*n);
        }

        static auto rotate_right(std::unique_ptr<Node> & n) -> void
        {
            auto l = std::move(n->left);
            n->left = std::move(l->right);
            update(*n);
            l->right = std::move(n);
            n = std::move(l);
            update(*n);
        }

        auto insert_at(std::unique_ptr<Node> & n, Integer lo, Integer hi, unsigned long long priority) -> void
        {
            if (! n) {
                n = std::make_unique<Node>(lo, hi, priority);
                return;
            }
            if (lo == n->lo && hi == n->hi)
                return;

            if (std::pair{lo, hi} < std::pair{n->lo, n->hi}) {
                insert_at(n->left, lo, hi, priority);
                if (n->left->priority < n->priority)
                    rotate_right(n);
                else
                    update(*n);
            }
            else {
                insert_at(n->right, lo, hi, priority);
                if (n->right->priority < n->priority)
                    rotate_left(n);
                else
                    update(*n);
            }
        }

        template <typename Visit_>
        static auto visit_containing(const Node * n, Integer lo, Integer hi, const Visit_ & visit) -> void
        {
            // want stored [c, d] with c <= lo and d >= hi
            if (! n || n->max_hi < hi)
                return;
            visit_containing(n->left.get(), lo, hi, visit);
            if (n->lo > lo)
                return; // everything right of here (and this node) has c > lo
            if (n->hi >= hi)
                visit(n->lo, n->hi);
            visit_containing(n->right.get(), lo, hi, visit);
        }

        template <typename Visit_>
        static auto visit_contained_in(const Node * n, Integer lo, Integer hi, const Visit_ & visit) -> void
        {
            // want stored [c, d] with c >= lo and d <= hi
            if (! n || n->min_hi > hi)
                return;
            if (n->lo >= lo) {
                visit_contained_in(n->left.get(), lo, hi, visit);
                if (n->hi <= hi)
                    visit(n->lo, n->hi);
            }
            visit_contained_in(n->right.get(), lo, hi, visit);
        }

    public:
        /**
         * Insert the closed interval [lo, hi]; inserting an interval that is
         * already present does nothing.
         */
        auto insert(Integer lo, Integer hi) -> void
        {
            insert_at(_root, lo, hi, _priorities());
        }

        /**
         * Call visit(c, d) for every stored interval [c, d] with [lo, hi]
         * inside it (including [lo, hi] itself if stored), in increasing
         * (c, d) order.
         */
        template <typename Visit_>
        auto for_each_containing(Integer lo, Integer hi, const Visit_ & visit) const -> void
        {
            visit_containing(_root.get(), lo, hi, visit);
        }

        /**
         * Call visit(c, d) for every stored interval [c, d] inside [lo, hi]
         * (including [lo, hi] itself if stored), in increasing (c, d) order.
         */
        template <typename Visit_>
        auto for_each_contained_in(Integer lo, Integer hi, const Visit_ & visit) const -> void
        {
            visit_contained_in(_root.get(), lo, hi, visit);
        }
    };
}

#endif
