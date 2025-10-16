import unittest
import time
from gcspy import GCS


class TestGlasgowConstraintSolver(unittest.TestCase):
    def setUp(self):
        self.gcs = GCS()
        self.x = self.gcs.create_integer_variable(1, 3, "x")
        self.y = self.gcs.create_integer_variable(1, 3, "y")
        self.z = self.gcs.create_integer_variable(1, 3, "z")

    def test_unknown_id(self):
        with self.assertRaises(KeyError):
            self.gcs.get_solution_value("not_an_id")

    def test_minimise(self):
        self.gcs.minimise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 1)

    def test_maximise(self):
        self.gcs.maximise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 3)

    def test_negate(self):
        negx = self.gcs.negate(self.x)
        self.gcs.maximise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(negx), -3)

    def test_add_constant(self):
        x_plus_2 = self.gcs.add_constant(self.x, 2)
        self.gcs.maximise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(x_plus_2), 5)

    def test_alldifferent_simple(self):
        self.gcs.post_alldifferent([self.x, self.y, self.z])
        stats = self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 3)
        self.assertEqual(self.gcs.get_solution_value(self.y), 2)
        self.assertEqual(self.gcs.get_solution_value(self.z), 1)
        self.assertEqual(stats["solutions"], 6)

    def test_alldifferent_no_solutions(self):
        w = self.gcs.create_integer_variable(1, 1, "w")
        self.gcs.post_alldifferent([self.x, self.y, self.z, w])
        stats = self.gcs.solve(True)
        self.assertIsNone(self.gcs.get_solution_value(self.x))
        self.assertIsNone(self.gcs.get_solution_value(self.y))
        self.assertIsNone(self.gcs.get_solution_value(self.z))
        self.assertIsNone(self.gcs.get_solution_value(w))
        self.assertEqual(stats["solutions"], 0)

    def test_empty_clause(self):
        self.gcs.post_or([])
        stats = self.gcs.solve(True)
        self.assertEqual(stats["solutions"], 0)

    def test_abs(self):
        w = self.gcs.create_integer_variable(-2, -2, "w")
        self.gcs.post_abs(w, self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 2)

    def test_plus(self):
        w = self.gcs.create_integer_variable(1, 1, "w")
        self.gcs.post_arithmetic(w, w, self.x, "sum")
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 2)

    def test_times(self):
        w = self.gcs.create_integer_variable(4, 4, "w")
        p = self.gcs.create_integer_variable(5, 5, "w")
        q = self.gcs.create_integer_variable(-100, 100, "w")
        self.gcs.post_arithmetic(w, p, q, "mul")
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(q), 20)

    def test_div(self):
        w = self.gcs.create_integer_variable(50, 50, "w")
        p = self.gcs.create_integer_variable(2, 2, "w")
        q = self.gcs.create_integer_variable(-100, 100, "w")
        self.gcs.post_arithmetic(w, p, q, "div")
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(q), 25)

    def test_pow(self):
        w = self.gcs.create_integer_variable(3, 3, "w")
        p = self.gcs.create_integer_variable(2, 2, "w")
        q = self.gcs.create_integer_variable(-100, 100, "w")
        self.gcs.post_arithmetic(w, p, q, "pow")
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(q), 9)

    def test_mod(self):
        w = self.gcs.create_integer_variable(11, 11, "w")
        p = self.gcs.create_integer_variable(2, 2, "w")
        q = self.gcs.create_integer_variable(-100, 100, "w")
        self.gcs.post_arithmetic(w, p, q, "mod")
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(q), 1)

    def test_compare_less(self):
        w = self.gcs.create_integer_variable(3, 3, "w")
        self.gcs.post_less_than(self.x, w)
        self.gcs.maximise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 2)

    def test_compare_less_equal(self):
        w = self.gcs.create_integer_variable(3, 3, "w")
        self.gcs.post_less_than_equal(self.x, w)
        self.gcs.maximise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 3)

    def test_compare_less_if(self):
        w = self.gcs.create_integer_variable(3, 3, "w")
        reif = self.gcs.create_integer_variable(0, 0, "r")
        self.gcs.post_less_than_reif(self.x, w, reif, False)
        self.gcs.maximise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 3)

    def test_count(self):
        w = self.gcs.create_integer_variable(3, 3, "w")
        c = self.gcs.create_integer_variable(2, 2, "c")
        self.gcs.post_count([self.x, self.y, self.z], w, c)
        self.gcs.solve(True)
        sols = [
            self.gcs.get_solution_value(self.x),
            self.gcs.get_solution_value(self.y),
            self.gcs.get_solution_value(self.z),
        ]
        self.assertEqual(sum([1 for el in sols if el == 3]), 2)

    def test_element(self):
        w = self.gcs.create_integer_variable(3, 3, "w")
        c = self.gcs.create_integer_variable(2, 2, "c")
        idx = self.gcs.create_integer_variable(0, 0, "idx")
        self.gcs.post_element(self.x, idx, [w, c])
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 3)

    def test_equals(self):
        c = self.gcs.create_integer_variable(2, 2, "c")
        self.gcs.post_equals(self.x, c)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 2)

    def test_equals_if(self):
        w = self.gcs.create_integer_variable(1, 1, "w")
        reif = self.gcs.create_integer_variable(0, 0, "r")
        self.gcs.post_equals_reif(self.x, w, reif, False)
        self.gcs.maximise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 3)

    def test_not_equals(self):
        c = self.gcs.create_integer_variable(1, 1, "c")
        self.gcs.post_not_equals(self.x, c)
        self.gcs.minimise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 2)

    def test_in(self):
        self.gcs.post_in(self.x, [1, 2])
        self.gcs.maximise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 2)

    def test_in_vars(self):
        w = self.gcs.create_integer_variable(2, 2, "w")
        c = self.gcs.create_integer_variable(1, 1, "c")
        self.gcs.post_in_vars(self.x, [c, w])
        self.gcs.maximise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 2)

    def test_linear_equality(self):
        self.gcs.post_linear_equality([self.x, self.y, self.z], [3, 3, 3], 9)
        self.gcs.maximise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 1)
        self.assertEqual(self.gcs.get_solution_value(self.y), 1)
        self.assertEqual(self.gcs.get_solution_value(self.z), 1)

    def test_linear_less_equal(self):
        self.gcs.post_linear_less_equal([self.x, self.y, self.z], [3, 3, 3], 14)
        self.gcs.maximise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 2)
        self.assertEqual(self.gcs.get_solution_value(self.y), 1)
        self.assertEqual(self.gcs.get_solution_value(self.z), 1)

    def test_linear_greater_equal(self):
        self.gcs.post_linear_greater_equal([self.x, self.y, self.z], [3, 3, 3], 27)
        self.gcs.maximise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 3)
        self.assertEqual(self.gcs.get_solution_value(self.y), 3)
        self.assertEqual(self.gcs.get_solution_value(self.z), 3)

    def test_and(self):
        b1 = self.gcs.create_integer_variable(0, 1, "b1")
        b2 = self.gcs.create_integer_variable(0, 1, "b2")
        self.gcs.post_and([b1, b2])
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(b1), 1)
        self.assertEqual(self.gcs.get_solution_value(b1), 1)

    def test_and_if(self):
        b1 = self.gcs.create_integer_variable(0, 1, "b1")
        b2 = self.gcs.create_integer_variable(0, 1, "b2")
        r = self.gcs.create_integer_variable(0, 0, "r")
        self.gcs.post_and_reif([b1, b2], r, False)
        self.gcs.minimise(b1)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(b1), 0)

    def test_or(self):
        b1 = self.gcs.create_integer_variable(0, 1, "b1")
        b2 = self.gcs.create_integer_variable(0, 0, "b2")
        self.gcs.post_or([b1, b2])
        self.gcs.minimise(b1)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(b1), 1)

    def test_or_if(self):
        b1 = self.gcs.create_integer_variable(0, 1, "b1")
        b2 = self.gcs.create_integer_variable(0, 0, "b2")
        r = self.gcs.create_integer_variable(0, 0, "r")
        self.gcs.post_or_reif([b1, b2], r, False)
        self.gcs.minimise(b1)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(b1), 0)

    def test_implies(self):
        b1 = self.gcs.create_integer_variable(1, 1, "b1")
        b2 = self.gcs.create_integer_variable(0, 1, "b2")
        self.gcs.post_implies(b1, b2)
        self.gcs.minimise(b2)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(b2), 1)

    def test_implies_if(self):
        b1 = self.gcs.create_integer_variable(1, 1, "b1")
        b2 = self.gcs.create_integer_variable(0, 1, "b2")
        r = self.gcs.create_integer_variable(0, 0, "r")
        self.gcs.post_implies_reif(b1, b2, r, False)
        self.gcs.minimise(b2)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(b2), 0)

    def test_xor(self):
        b1 = self.gcs.create_integer_variable(1, 1, "b1")
        b2 = self.gcs.create_integer_variable(0, 1, "b2")
        self.gcs.post_xor([b1, b2])
        self.gcs.maximise(b2)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(b2), 0)

    def test_min(self):
        w = self.gcs.create_integer_variable(2, 2, "w")
        c = self.gcs.create_integer_variable(1, 1, "c")
        r = self.gcs.create_integer_variable(2, 2, "r")
        self.gcs.post_min([w, c, r], self.x)
        self.gcs.maximise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 1)

    def test_max(self):
        w = self.gcs.create_integer_variable(2, 2, "w")
        c = self.gcs.create_integer_variable(1, 1, "c")
        r = self.gcs.create_integer_variable(2, 2, "r")
        self.gcs.post_max([w, c, r], self.x)
        self.gcs.minimise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 2)

    def test_nvalue(self):
        w = self.gcs.create_integer_variable(2, 2, "w")
        c = self.gcs.create_integer_variable(1, 1, "c")
        r = self.gcs.create_integer_variable(2, 2, "r")
        self.gcs.post_nvalue(self.x, [w, c, r])
        self.gcs.minimise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 2)

    def test_table(self):
        table = [[2, 1, 1], [3, 2, 1]]
        self.gcs.post_table([self.x, self.y, self.z], table)
        self.gcs.minimise(self.x)
        self.gcs.solve(True)
        self.assertEqual(self.gcs.get_solution_value(self.x), 2)
        self.assertEqual(self.gcs.get_solution_value(self.y), 1)
        self.assertEqual(self.gcs.get_solution_value(self.z), 1)

    def test_timeout(self):
        [self.gcs.create_integer_variable(1, 1000, "") for i in range(1000)]
        start = time.time()
        self.gcs.solve(True, timeout=1.5)
        end = time.time()
        assert(abs(end - start - 1.5) < 1)
if __name__ == "__main__":
    unittest.main()
