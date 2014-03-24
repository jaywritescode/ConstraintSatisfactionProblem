__author__ = 'Jay Harris'

from collections import deque


class ConstraintSatisfactionProblem:
    """
    A framework for solving constraint satisfaction problems.

    Attributes:
      variables (dict): a mapping of variable names -> variable objects
      constraints (set): the set of the problem's constraints
    """
    def __init__(self):
        """
        Basic constructor.

        Just exists to make some otherwise ambiguous variable types explicit.
        """
        self.variables = dict()
        self.constraints = set()

    def solve(self):
        """
        Solve the constraint satisfaction problem.

        Returns:
        The CSP with values assigned to all its non-auxiliary variables,
        or None if there is no solution.
        """
        self.ac3()
        return self.recursive_backtracking(0)

    def recursive_backtracking(self, depth):
        """
        Backtracking search.

        Args:
          depth (int): the current depth of the search tree

        Returns:
          self on success or the local conflict set on a branch fail.
        """
        if self.is_solved():
            return self

        current_var = self.select_unassigned_variable()
        current_var.conflict_set = {n for n in current_var.get_neighbors() if n.value is not None}

        for value in current_var.ordered_domain():
            # Assign a value to the current variable.
            current_var.value = value

            # Let reduced_domains be a map: variable V -> a set of values
            # removed from V's domain.
            reduced_domains = {current_var: {x for x in current_var.domain if x is not value}}
            current_var.domain = [value]

            # Make the variables' domains arc-consistent.
            ac3_changes = self.ac3()
            for (key, removed_values) in ac3_changes.items():
                if key is current_var:
                    reduced_domains[key].update(ac3_changes[key])
                else:
                    reduced_domains[key] = removed_values

            # Try the next variable N.
            result = self.recursive_backtracking(depth + 1)
            if result is self:
                return self

            # No satisfying value for N, so de-assign the current variable
            # and restore all the domains we changed above.
            for (variable, removed_values) in reduced_domains.items():
                variable.domain.extend(removed_values)
            reduced_domains.clear()
            current_var.value = None

            # If the current variable isn't in N's conflict set, then
            # no value will satisfy this variable. So backtrack and
            # pass the conflict set up to the next stack frame.
            if current_var not in result and depth > 0:
                return result

            # Otherwise absorb the conflict set from N into the current
            # variable's conflict set.
            for e in result:
                if e is not current_var:
                    current_var.conflict_set.add(e)

        return current_var.conflict_set

    def ac3(self, is_disjoint_constraints=True):
        """
        AC-3 domain reduction algorithm.

        Maintains (hyper)arc consistency in a CSP by removing incompatible
        values from variables' domains.

        Args:
          isDisjointConstraints (bool): True if two variables uniquely identify a
            constraint. We can use this information to optimize the algorithm.

        Returns:
          A multimap of variables V -> a set of values removed from the domain of V
        """
        queue = deque()

        find_constraints = (BaseVariable.find_constraints_between
                            if is_disjoint_constraints
                            else BaseVariable.find_constraint_between)

        for c in self.constraints:
            queue.extend((vi, c) for vi in c.get_variables() if vi.value is None)

        removed = dict()
        while queue:
            (variable, constraint) = queue.popleft()
            inconsistent_values = self.remove_inconsistent_values(variable, constraint)
            if inconsistent_values:
                if variable in removed:
                    removed[variable].update(inconsistent_values)
                else:
                    removed[variable] = inconsistent_values

                for neighbor in variable.get_neighbors():
                    for cst in find_constraints(variable, neighbor):
                        if (neighbor, cst) not in queue:
                            queue.append((neighbor, cst))
        return removed

    def select_unassigned_variable(self):
        """
        Choose the next variable to examine.

        Most-restricted variable selection algorithm: Choose the
        variable with the smallest domain, breaking ties in favor
        of the variable that appears in more constraints.

        Returns:
          The next variable to examine.
        """
        the_variables = [var for var in self.variables.values() if var.value is None]
        assert(len(the_variables))

        choice = None
        for var in the_variables:
            if not choice or len(var.domain) < len(choice.domain):
                choice = var
            elif len(var.domain) == len(choice.domain):
                if len([x for x in var.get_neighbors() if not x.value]) > len(
                        [x for x in choice.get_neighbors() if not x.value]):
                    choice = var
        return choice

    def remove_inconsistent_values(self, variable, constraint):
        """
        Remove values from `variable.domain` that are inconsistent with `constraint`.

        Args:
          variable:
          constraint:

        Returns:
          The set of inconsistent domain values.
        """
        inconsistent = set()
        for value in variable.domain:
            if not constraint.is_satisfiable(variable, value):
                inconsistent.add(value)

        variable.domain = [x for x in variable.domain if x not in inconsistent]
        return inconsistent

    def is_solved(self):
        """
        Determine if the puzzle is solved.

        Returns:
          True iff for all variables V in self.variable, V is assigned
          a non-None value or V is an auxiliary variable.
        """
        return all(var.value is not None for var in self.variables.values() if not var.aux)


class BaseVariable:
    """
    A variable in the CSP.

    Attributes:
      csp: a reference to the CSP wrapping this variable
      name: an immutable, hashable representation of the variable
      domain: the variable's domain of legal values at this stage in the
        problem.
      value: the value assigned to this variable, or None
      constraints: a set of constraints covering this variable
      aux: An auxiliary variable isn't part of the problem. That is,
        the problem can be said to be solved even if this variable's
        value is still None.
    """
    def __init__(self, csp, name, aux=False):
        self.csp = csp
        self.name = name
        self.domain = None
        self.value = None
        self.constraints = set()
        self.neighbors = None
        self.aux = aux

    def get_neighbors(self):
        """
        Get all the variables that share at least one constraint with this variable.

        Returns:
          A set of this variable's neighbors, not including self.
        """
        if self.neighbors is None:
            self.neighbors = set()
            for c in self.constraints:
                self.neighbors |= {v for v in c.variables if v is not self}
        return self.neighbors

    def ordered_domain(self):
        """
        Get this variable's domain as an indexable collection.

        Note that the code implies all values in the domain are consistent
        with all constraints in the problem.

        Returns:
          A (sorted) list of this variable's domain.
        """
        return self.domain

    def find_constraints_between(self, other_var):
        """
        Find all the constraints covered by both of two given variables.

        Args:
          other_var: the other variable we're looking for in a constraint.

        Returns:
          A list of the shared constraints.
        """
        return [c for c in self.constraints if c.covers(other_var)]

    def find_constraint_between(self, other_var):
        """
        For a "linear" CSP, return the only constraint that covers two given variables.

        Args:
          other_var: the other variable we're looking for in a constraint

        Returns:
          A singleton list of the shared constraint, or an empty list if
        no shared constraint exists.
        """
        for c in self.constraints:
            if c.covers(other_var):
                return [c]
        return list()

    def get_name(self):
        """
        A convenience method for sorting variables in a list.
        """
        return self.name

    def __hash__(self):
        return object.__hash__(self.name)

    def __eq__(self, other):
        return self.name == other.name

    def __repr__(self):
        return "[Variable] %s => %s" % (self.name, self.value if self.value is not None else self.domain)


class BaseConstraint:
    """
    A constraint in the CSP.

    Attributes:
      variables: a list of variables this constraint covers
    """
    def __init__(self, variables):
        """
        Constructor.

        Args:
          variables: an iterable of variables this constraint covers
        """
        self.variables = variables
        for variable in self.variables:
            variable.constraints.add(self)

    def is_satisfiable(self, variable, assignment):
        """
        Is the constraint satisfiable with the given `variable.value = assignment`?

        This is an abstract method that should be implemented by subclasses.

        Arguments:
          variable: the variable we're assigning to
          assignment: the value we're assigning to the variable
        """
        raise NotImplementedError

    def covers(self, variable):
        """
        Does this constraint cover the given variable?

        Args:
          variable: the variable we're checking against this constraint

        Returns:
          True iff this constraint covers the given variable.
        """
        return variable in self.variables

    def get_variables(self):
        """
        Get all the variables this constraint covers.

        Returns:
          An iterable of variables this constraint covers.
        """
        return self.variables