import unittest
import pytest

australia_names = ['WA', 'NT', 'Q', 'NSW', 'V', 'SA', 'T']
australia_neighbors = [
    ('WA', 'NT'), ('NT', 'SA'), ('WA', 'SA'), ('NT', 'Q'), ('SA', 'Q'),
    ('Q', 'NSW'), ('SA', 'NSW'), ('SA', 'V'), ('NSW', 'V')
]

@pytest.fixture
def australia():
    import csp

    australia = csp.ConstraintSatisfactionProblem()

    class AustraliaVariable(csp.BaseVariable):
        def __init__(self, name):
            csp.BaseVariable.__init__(self, australia, name)
            self.domain = {'red', 'blue', 'green'}

    for name in australia_names:
        australia.variables[name] = AustraliaVariable(name)

    for constraint in australia_neighbors:
        vars = map(lambda t: australia.variables[t], constraint)
        australia.constraints.add(csp.AllDifferentConstraint(vars))

    return australia


class ConstraintSatisfactionProblemTestCase(unittest.TestCase):
    def test_solve(self):
        solution = australia().solve()
        self.assertTrue(all(variable.value for variable in solution.variables.values()))
        for pair in australia_neighbors:
            vars = [solution.variables.get(p) for p in pair]
            self.assertNotEqual(vars[0].value, vars[1].value, "Failed: {}".format(solution.variables))


class BaseVariableTestCase(unittest.TestCase):
    def test_neighbors(self):
        csp = australia()
        self.assertSetEqual(set(), csp.variables['T'].neighbors)
        self.assertSetEqual({csp.variables[x] for x in ['WA', 'SA', 'Q']}, csp.variables['NT'].neighbors)

if __name__ == '__main__':
    unittest.main()
