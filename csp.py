"""
This module is a framework for solving constraint satisfaction problems.
"""

from collections import deque


class ConstraintSatisfactionProblem:
    """
    The abstract base class of a constraint satisfaction problem.

    Attributes:
        variables (dict): A mapping of variable names -> variable objects
        constraints (set): The set of the problem's constraints
        is_disjoint_constraints: If the csp is such that any two variables
            uniquely identify a constraint, set this to True for optimizations
    """
    def __init__(self):
        """
        Basic constructor.

        Just exists to make some otherwise ambiguous variable types explicit.
        """
        self.variables = dict()
        self.constraints = set()
        self.is_disjoint_constraints = False

    def solve(self):
        """
        Solves the constraint satisfaction problem.

        Returns:
            The CSP with values assigned to all its non-auxiliary variables,
            or None if there is no solution.
        """
        self._ac3()
        return self._recursive_backtracking(0)

    def _recursive_backtracking(self, depth):
        """
        Backtracking search.

        Args:
            depth (int): The current depth of the search tree

        Returns:
            self on success or the local conflict set on a branch fail. This
                implies that the method returns something falsy if there is no
                solution.
        """
        if self.is_solved():
            return self

        current_var = self._select_unassigned_variable()
        current_var.conflict_set = {n for n in current_var.neighbors
                                    if n.value is not None}

        for value in current_var.ordered_domain():
            self._assign_value_to_variable(current_var, value)

            # Record the values we're removing from each variable's domain.
            reduced_domains = {current_var: {x for x in current_var.domain
                                             if x is not value}}

            ac3_changes = self._ac3(current_var)
            for (key, removed_values) in ac3_changes.items():
                if key is current_var:
                    reduced_domains[key].update(ac3_changes[key])
                else:
                    reduced_domains[key] = removed_values

            result = self._recursive_backtracking(depth + 1)
            if result is self:
                return self

            # No value works at depth + 1, so de-assign current_var and undo
            # all the domain modifications.
            for (variable, removed_values) in reduced_domains.items():
                variable.domain.extend(removed_values)
            reduced_domains.clear()
            current_var.value = None

            # If the current variable isn't in the conflict set from recursion
            # depth + 1, then no value will satisfy this constraint. So
            # backtrack and pass the conflict set up to the next stack frame.
            if current_var not in result and depth > 0:
                return result

            # Otherwise absorb the conflict set from the previous recursion into
            # current_var's conflict set.
            for e in result:
                if e is not current_var:
                    current_var.conflict_set.add(e)

        return current_var.conflict_set

    @staticmethod
    def _assign_value_to_variable(variable, value):
        """
        Assigns `value` to `variable`, or raises an error if `value` is not in
        `variable's` domain.

        Args:
            variable: The variable target of the assignment.
            value: The value we're assigning to the variable.
        """
        if value not in variable.domain:
            raise ValueError

        variable.value = value
        variable.domain = [value]

    def _ac3(self, variable=None):
        """
        AC-3 domain reduction algorithm.

        Maintains (hyper)arc consistency in a CSP by removing incompatible
        values from variables' domains.

        Args:
            variable: The variable whose domain was just modified. Constraints
                not connected to variable via the consistency graph don't need
                to be considered. Passing None initializes the AC-3 queue with
                the Cartesian product of all variables and all constraints.

        Returns:
            A multimap of variables V -> a set of values removed from the
                domain of V
        """
        queue = deque()

        find_constraints = (BaseVariable.find_constraints_between
                            if self.is_disjoint_constraints
                            else BaseVariable.find_constraint_between)

        for c in (self.constraints
                  if variable is None
                  else variable.constraints):
            queue.extend((vi, c) for vi in c.get_variables()
                         if vi.value is None)

        removed = dict()
        while queue:
            (variable, constraint) = queue.popleft()
            inconsistent_values = self._remove_inconsistent_values(
                    variable, constraint)

            if inconsistent_values:
                if variable in removed:
                    removed[variable].update(inconsistent_values)
                else:
                    removed[variable] = inconsistent_values

                for neighbor in variable.neighbors:
                    for cst in find_constraints(variable, neighbor):
                        if (neighbor, cst) not in queue:
                            queue.append((neighbor, cst))
        return removed

    def _select_unassigned_variable(self):
        """
        Choose the next variable to examine.

        Most-restricted variable selection algorithm: Choose the
        variable with the smallest domain, breaking ties in favor
        of the variable that appears in more constraints.

        Returns:
            The next variable to examine.
        """
        the_variables = [var for var in self.variables.values()
                         if var.value is None]
        assert(len(the_variables))

        choice = None
        for var in the_variables:
            if not choice or len(var.domain) < len(choice.domain):
                choice = var
            elif len(var.domain) == len(choice.domain):
                if len([x for x in var.neighbors if not x.value]) > len(
                        [x for x in choice.neighbors if not x.value]):
                    choice = var
        return choice

    @staticmethod
    def _remove_inconsistent_values(variable, constraint):
        """
        Remove values from variable.domain that are inconsistent with constraint.

        Args:
            variable: The variable whose domain we're checking
            constraint: The constraint we're checking the variable against

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
        csp: A reference to the CSP wrapping this variable
        name: An immutable, hashable representation of the variable
        domain: The variable's domain of legal values at this stage in the
            problem
        value: The value assigned to this variable, possibly None
        constraints: A set of constraints covering this variable
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
        self._neighbors = None
        self.aux = aux

    @property
    def neighbors(self):
        """
        Get all the variables that share at least one constraint with this variable.

        Returns:
            A set of this variable's neighbors, not including self.
        """
        if self._neighbors is None:
            self._neighbors = set()
            for c in self.constraints:
                self._neighbors |= {v for v in c.variables if v is not self}
        return self._neighbors

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
            other_var: The other variable we're looking for in each constraint.

        Returns:
            A list of the shared constraints.
        """
        return [c for c in self.constraints if c.covers(other_var)]

    def find_constraint_between(self, other_var):
        """
        For a "linear" CSP, return the only constraint that covers two given variables.

        Args:
            other_var: The other variable we're looking for in each constraint

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
        return "[Variable] {} => {}".format(
            self.name, self.value if self.value is not None else self.domain)


class BaseConstraint:
    """
    A constraint in the CSP.

    Attributes:
        variables: A list of variables this constraint covers
    """
    def __init__(self, variables):
        """
        Constructor.

        Args:
            variables: An iterable of variables this constraint covers
        """
        self.variables = list(variables)
        for variable in self.variables:
            variable.constraints.add(self)

    def is_satisfiable(self, variable, assignment):
        """
        Determine if variable.value = assignment is satisfiable with the constraint.

        This is an abstract method that should be implemented by subclasses.

        Arguments:
            variable: The variable we're assigning to
            assignment: The value we're assigning to the variable
        """
        raise NotImplementedError

    def covers(self, variable):
        """
        Determine if this constraint covers the given variable.

        Args:
            variable: The variable we're checking against this constraint

        Returns:
            True iff this constraint covers the given variable.
        """
        return variable in self.variables

    def get_variables(self):
        """
        Get all the variables this constraint covers.

        Returns:
            A list of variables this constraint covers.
        """
        return self.variables