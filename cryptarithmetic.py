"""
This module solves (certain types of) cryptarithmetic problems.
"""

from csp import *

import itertools
import re


class Cryptarithmetic(ConstraintSatisfactionProblem):
    """
    The cryptarithmetic solver.

    This one only solves decimal domain puzzles, and only puzzles with two
    addends and a sum.
    """
    def __init__(self, puzzle):
        """
        Constructor.

        Args:
            puzzle (str): a cryptarithmetic with two addends and a sum, on one
                line

        Raises:
            InvalidPuzzleException: The puzzle is invalid.
        """
        ConstraintSatisfactionProblem.__init__(self)

        # Extract the words from the puzzle.
        self.puzzle = puzzle
        match = re.match('(\w+)\s*\+\s*(\w+)\s*=\s*(\w+)', puzzle)
        if match:
            (addend1, addend2, the_sum) = match.groups()
        else:
            raise InvalidPuzzleException()

        m = max(len(the_sum), len(addend2) + 2)
        self.puzzle = ''.join([addend1.rjust(m), "\n", ("+ " + addend2).rjust(m),
                "\n", '-' * m, "\n", the_sum.rjust(m)])

        # Create a map: letter -> variable. Then create auxiliary
        # variables and add them to the map.
        self.variables = {char: CryptarithmeticVariable(self, char)
                          for char in puzzle if str.isalpha(char)}
        if len(self.variables) > 10:
            raise InvalidPuzzleException()
        for i in (addend1, addend2, the_sum):
            self.variables[i[0]].domain.discard(0)
        for i in range(1, len(the_sum)):
            name = 'aux' + str(i)
            self.variables[name] = CryptarithmeticVariable(self, name, aux=True)

        # Create the constraints.
        for i in range(1, len(the_sum) + 1):
            left = list()
            if 'aux' + str(i - 1) in self.variables:
                left.append(self.variables['aux' + str(i - 1)])
            if i <= len(addend1):
                left.append(self.variables[addend1[-i]])
            if i <= len(addend2):
                left.append(self.variables[addend2[-i]])
            right = [self.variables[the_sum[-i]]]
            if 'aux' + str(i) in self.variables:
                right.append(self.variables['aux' + str(i)])
            self.constraints.add(SumConstraint(left, right))

        self.constraints.add(AllDifferentConstraint(
                [var for var in self.variables.values() if not var.aux]))

    def __str__(self):
        p = self.puzzle[:]
        for letter in self.variables:
            p = p.replace(letter, str(self.variables[letter].value))
        return self.puzzle + "\n\n" + p


class InvalidPuzzleException(Exception):
    pass


class CryptarithmeticVariable(BaseVariable):

    def __init__(self, csp, name, aux=False):
        BaseVariable.__init__(self, csp, name, aux)
        self.domain = set(range(10)) if not self.aux else set(range(2))


class SumConstraint(BaseConstraint):
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
        BaseConstraint.__init__(self, left_vars + right_vars)
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
        return ' '.join["[Constraint",
                        ' + '.join(var.name for var in self.left_vars), "=",
                        self.right_vars[0].name, '+ 10 *',
                        self.right_vars[1].name
                            if len(self.right_vars) == 2 else '']


class AllDifferentConstraint(BaseConstraint):
    def __init__(self, variables):
        BaseConstraint.__init__(self, variables)

    def is_satisfiable(self, variable, assignment):
        if variable.value is not None:
            return True

        if assignment in [var.value for var in self.variables
                          if var.value is not None]:
            return False

        def remove_if_exists(target, collection):
            try:
                collection.remove(target)
            except (KeyError, ValueError):
                pass

        tmp_vars_domains = {var: var.domain.copy() for var in self.variables
                            if not var.value and var is not variable}

        # Remove assignment from all the variables' temp domains
        for domain in tmp_vars_domains.values():
            remove_if_exists(assignment, domain)

        # If any temp domain is empty, then this assignment is not
        # satisfiable.
        while all(tmp_vars_domains.values()):
            # If we have any singletons, we need to process the domains
            singletons = [x for x in tmp_vars_domains.keys()
                          if len(tmp_vars_domains[x]) == 1]
            if singletons:
                d = list(singletons[0].domain)[0]
                for s in tmp_vars_domains.values():
                    remove_if_exists(d, s)
                del tmp_vars_domains[singletons[0]]
            else:
                return True

        return False

    def __repr__(self):
        return "[Constraint] All different: {%s}" % self.variables

def main(puzzle):
    c = Cryptarithmetic(puzzle)
    if c.solve():
        print(c)
    else:
        print("No solution.")

if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("puzzle", help="Enter the cryptarithmetic in double quotes, on one line")
    args = parser.parse_args()
    main(args.puzzle)

    # send + more = money => 9567 + 1085 = 10652
    # cross + roads = danger => 96233 + 62513 = 158746
    # use + less = kiddy => 876 + 9677 = 10553
    # green + orange = colors => 83446 + 135684 = 219130
    # taurus + pisces = scorpio => 859091 + 461371 = 1320462