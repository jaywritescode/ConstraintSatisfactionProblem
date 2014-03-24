import csp

__author__ = 'Jay Harris'

import itertools
import re


class Cryptarithmetic(csp.ConstraintSatisfactionProblem):
    """
    Technically, it's a cryptarithmetic solver.
    """
    def __init__(self, puzzle):
        """
        Constructor.

        Args:
          puzzle (str): a cryptarithmetic with two addends and a sum
        """
        csp.ConstraintSatisfactionProblem.__init__(self)

        # Extract the words from the puzzle.
        self.puzzle = puzzle
        match = re.match('(\w+)\s*\+\s*(\w+)\s*=\s*(\w+)', puzzle)
        if match:
            (addend1, addend2, sum) = match.groups()
        else:
            raise InvalidPuzzleException()

        # Create a map: letter -> variable. Then create auxiliary
        # variables and add them to the map.
        self.variables = {char: CryptarithmeticVariable(self, char) for char in puzzle if str.isalpha(char)}
        if len(self.variables) > 10:
            raise InvalidPuzzleException()
        for i in (addend1, addend2, sum):
            self.variables[i[0]].domain.discard(0)
        for i in range(1, len(sum)):
            name = 'aux' + str(i)
            self.variables[name] = CryptarithmeticVariable(self, name, aux=True)

        # Create the constraints.
        for i in range(1, len(sum) + 1):
            left = list()
            if 'aux' + str(i - 1) in self.variables:
                left.append(self.variables['aux' + str(i - 1)])
            if i <= len(addend1):
                left.append(self.variables[addend1[-i]])
            if i <= len(addend2):
                left.append(self.variables[addend2[-i]])
            right = [self.variables[sum[-i]]]
            if 'aux' + str(i) in self.variables:
                right.append(self.variables['aux' + str(i)])
            self.constraints.add(SumConstraint(left, right))

        self.constraints.add(AllDifferentConstraint([var for var in self.variables.values() if not var.aux]))

    def print(self):
        print(self.puzzle)
        for var in self.variables.values():
            if not var.aux:
                print("%s: %s" % (var.name, var.value))


class InvalidPuzzleException(Exception): pass


class CryptarithmeticVariable(csp.BaseVariable):

    def __init__(self, csp, name, aux=False):
        csp.BaseVariable.__init__(self, csp, name, aux)
        self.domain = set(range(10)) if not self.aux else set(range(2))


class SumConstraint(csp.BaseConstraint):
    """
    A constraint of the form aux_n + A + B = C + 10 ** (aux_n+1)
    """
    def __init__(self, left_vars, right_vars):
        """
        Constructor.

        Args:
            left_vars (list of Variable): the variables on the left side
            of the constraint equation
            right_vars (list of Variable): the variable on the right side
            of the constraint equation
        """
        csp.BaseConstraint.__init__(self, left_vars + right_vars)
        self.left_vars = left_vars
        self.right_vars = right_vars

    def is_satisfiable(self, variable, assignment):
        result = False
        old_domain = variable.domain
        variable.domain = {assignment}

        all_assignments = itertools.product(
            itertools.product(*(var.domain for var in self.left_vars)),
            itertools.product(*(var.domain for var in self.right_vars)))
        try:
            for combination in all_assignments:
                left_sum = sum(x for x in combination[0])
                right_sum = 0
                for i in range(len(combination[1])):
                    right_sum += combination[1][i] * (10 ** self.right_vars[i].aux)

                if left_sum == right_sum:
                    raise SumConstraint.FoundException
        except SumConstraint.FoundException:
            result = True
        finally:
            variable.domain = old_domain

        return result

    class FoundException(Exception): pass

    def __repr__(self):
        return "[Constraint] %s = %s" % (' + '.join(var.name for var in self.left_vars),
            "%s %s" % (self.right_vars[0].name, '+ 10 * ' + self.right_vars[1].name if len(self.right_vars) == 2 else ''))


class AllDifferentConstraint(csp.BaseConstraint):
    def __init__(self, variables):
        csp.BaseConstraint.__init__(self, variables)

    def is_satisfiable(self, variable, assignment):
        if variable.value is not None:
            return True

        if assignment in [var.value for var in self.variables if var.value is not None]:
            return False

        def remove_if_exists(target, collection):
            try:
                collection.remove(target)
            except (KeyError, ValueError):
                pass

        tmp_vars_domains = {var: var.domain.copy() for var in self.variables if not var.value and var is not variable}

        # Remove assignment from all the variables' temp domains
        for domain in tmp_vars_domains.values():
            remove_if_exists(assignment, domain)

        # If any temp domain is empty, then this assignment is not
        # satisfiable.
        while all(tmp_vars_domains.values()):
            # If we have any singletons, we need to process the domains
            singletons = [x for x in tmp_vars_domains.keys() if len(tmp_vars_domains[x]) == 1]
            if singletons:
                d = list(singletons[0].domain)[0]
                for s in tmp_vars_domains.values():
                    remove_if_exists(d, s)
                del tmp_vars_domains[singletons[0]]
            else:
                return True

        return False

        singletons = [x for x in tmp_vars_domains if len(x) == 1]
        while singletons:
            for domain in tmp_vars_domains:
                remove_if_exists(domain, singletons[0][0])
            singletons = [x for x in tmp_vars_domains if len(x) == 1]

        return not all(tmp_vars_domains)

    def __repr__(self):
        return "[Constraint] All different: {%s}" % self.variables


if __name__ == '__main__':
    c = Cryptarithmetic("send + more = money")
    c.solve()
    c.print()

    c = Cryptarithmetic("cross + roads = danger")
    c.solve()
    c.print()

    c = Cryptarithmetic("use + less = kiddy")
    c.solve()
    c.print()

    c = Cryptarithmetic("green + orange = colors")
    c.solve()
    c.print()

    c = Cryptarithmetic("taurus + pisces = scorpio")
    c.solve()
    c.print()