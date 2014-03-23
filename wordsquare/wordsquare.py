__author__ = 'jayharris'

from csp import *

from collections import deque, Counter


class WordSquare:
    """
    Find a word square of the given size from the given dictionary.
    """
    
    alphabet = list('ABCDEFGHIJKLMNOPQRSTUVWXYZ')

    def __init__(self, wordsfile):
        """
        Constructor.

        Arguments:
        wordsfile -- the path to a text file of valid words for this
            word square, with one word on a line
        """                
        self.words = (str.upper(w.rstrip()) for w in open(wordsfile) if str.isalpha(w.rstrip()))

    def csp(self, size, diag=False):
        return WordSquareCSP(self, size, diag)


class WordSquareCSP(ConstraintSatisfactionProblem):

    def __init__(self, wordsquare, size, diag):
        """
        Constructor.

        Arguments:
        wordsquare -- the word square associated with the CSP
        size -- the length of the words in the square
        diag -- True if the CSP has a diagonal constraint, otherwise
            False
        """
        self.size = size

        self.letters_count = Counter()

        # create a map: indexOf -> map(letter -> wordlist)
        lettermap = [{letter: set() for letter in wordsquare.alphabet} for i in range(size)]
        # filter out words whose length != size
        for word in (word for word in wordsquare.words if len(word) == size):
            for index in range(len(word)):
                lettermap[index][word[index]].add(word)
                self.letters_count.update(word[index])

        # create a variable for each (row,col) pair in the word square
        self.variables = {(i, j): WordSquareVariable(self, (i, j)) for i in range(size) for j in range(size)}

        # create a constraint for each row and for each col (and the diagonal if requested)
        self.constraints = set()
        WordSquareConstraint.lettermap = lettermap
        for i in range(size):
            self.constraints.add(WordSquareConstraint({self.variables[(i, col)] for col in range(size)}))
            self.constraints.add(WordSquareConstraint({self.variables[(row, i)] for row in range(size)}))
        if diag:
            self.constraints.add(WordSquareConstraint({self.variables[(i, i)] for i in range(size)}))

    def print(self):
        i = 0
        for var_name in sorted(list(self.variables.keys())):
            print(' ' if not self.variables[var_name].value else self.variables[var_name].value, end='')
            i += 1
            if i % self.size == 0:
                print("")


class WordSquareVariable(BaseVariable):
    """
    A variable in the word square CSP.

    Public instance variables:
    csp -- a reference to the CSP wrapping this variable
    name -- a (row, column) tuple identifying this variable referencing
        the letter at (row, column) in the word square
    domain -- this variable's domain of legal values at this stage in
        the problem
    value -- the letter assigned to this variable, or None
    constraints -- a set of constraints covering this variable

    Unpublished instance variables:
    neighbors -- a set of variables that share at least one constraint with
        this variable. Should be retrieved via `self.get_neighbors()`.
    """
    def __init__(self, csp, name):
        BaseVariable.__init__(self, csp, name)
        self.domain = WordSquare.alphabet[:]

    def ordered_domain(self):
        """
        Returns:
        This variable's domain as a list of values, sorted by most common
        to least common.
        """
        return sorted(self.domain, key=lambda c: self.csp.letters_count[c], reverse=True)

    def find_constraint(self, other_var):
        """
        Find a constraint that covers two given variables.

        Arguments:
        other_var -- the variable we're looking for a shared constraint
        with

        Returns:
        The constraint that covers both `self` and `other_var`. The nature
        of the word square implies that at most one constraint covers
        any two given variables.
        """
        for constraint in self.constraints:
            if constraint in other_var.constraints:
                return constraint
        return None


class WordSquareConstraint(BaseConstraint):
    """
    A constraint in the word square CSP. The constraint is of the form
    [V_0 = d_0, V_1 = d_1, ..., V_n = d_n] and is satisfied if there's a
    word W such that W[0] = d_0, W[1] = d_1, ..., W[n] = d_n.

    Public instance variables:
    variables -- a list of variables this constraint covers, in order from
        top to bottom or left to right

    Public class variables:
    lettermap -- a map: string index i -> map: letter -> words whose
        i-th character is letter

    Unpublished instance variables:
    indices -- a map: variable v -> index i such that `self.variables[i] is v`
    """
    def __init__(self, variables):
        """
        Constructor.

        Arguments:
        variables -- a set of variables this constraint covers
        """
        BaseConstraint.__init__(self, sorted(iter(variables), key=WordSquareVariable.get_name))
        self.indices = {self.variables[i].name: i for i in range(len(self.variables))}

    def is_satisfiable(self, variable, assignment):
        """
        Is the constraint, including variables already assigned values,
        satisfiable with the given assignment `variable.value = assignment`?

        Arguments:
        variable -- the variable we're assigning to
        assignment -- the value we're assigning to the variable

        Returns:
        A list of words W such that for all indices i in self.variables,
        W[i] is in self.variables[i].domain AND `W[i] = assignment` if
        `self.variables[i] is variable`.
        """
        words = self.lettermap[self.indices[variable.name]][assignment]
        for other_var in self.variables:
            if other_var is not variable:
                words = [w for w in words if w[self.indices[other_var.name]] in other_var.domain]
        return words

    def __repr__(self):
        return "[Constraint] %s" % [var.name for var in self.variables]


if __name__ == '__main__':
    wordsquare = WordSquare('resources/words.txt')
    puzzle = wordsquare.csp(5, True)
    puzzle.solve().print()
