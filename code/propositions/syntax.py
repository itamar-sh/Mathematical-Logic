# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulas."""

from __future__ import annotations
from functools import lru_cache
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method

@lru_cache(maxsize=100) # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= 'p' and string[0] <= 'z' and \
           (len(string) == 1 or string[1:].isdigit())

@lru_cache(maxsize=100) # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return string == 'T' or string == 'F'

@lru_cache(maxsize=100) # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == '~'

@lru_cache(maxsize=100) # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    # return string == '&' or string == '|' or string == '->'
    # For Chapter 3:
    return string in {'&', '|',  '->', '+', '<->', '-&', '-|'}

@frozen
class Formula:
    """An immutable propositional formula in tree representation, composed from
    variable names, and operators applied to them.

    Attributes:
        root (`str`): the constant, variable name, or operator at the root of
            the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand for the root, if the root is a unary or
                binary operator.
            second: the second operand for the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert first is not None and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root)
            assert first is not None and second is not None
            self.root, self.first, self.second = root, first, second

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1
        if is_constant(self.root):
            return self.root
        if is_variable(self.root[0]):
            return self.root
        if is_unary(self.root):
            return self.root+str(self.first)
        if is_binary(self.root):
            return '('+str(self.first)+self.root+str(self.second)+')'

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 1.2
        vars_set = set()
        if is_variable(self.root):
            vars_set.add(self.root)
            return vars_set
        if is_constant(self.root):
            return vars_set
        if is_unary(self.root):
            vars_set.update(self.first.variables())
            return vars_set
        if is_binary(self.root):
            vars_set.update(self.first.variables())
            vars_set.update(self.second.variables())
            return vars_set


    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        vars_set = set()
        if is_variable(self.root):
            return vars_set
        if is_constant(self.root):
            vars_set.add(self.root)
            return vars_set
        if is_unary(self.root):
            vars_set.add(self.root)
            vars_set.update(self.first.operators())
            return vars_set
        if is_binary(self.root):
            vars_set.add(self.root)
            vars_set.update(self.first.operators())
            vars_set.update(self.second.operators())
            return vars_set
        
    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a variable name (e.g.,
            ``'x12'``) or a unary operator followed by a variable name, then the
            parsed prefix will include that entire variable name (and not just a
            part of it, such as ``'x1'``). If no prefix of the given string is a
            valid standard string representation of a formula then returned pair
            should be of ``None`` and an error message, where the error message
            is a string with some human-readable content.
        """
        # Task 1.4
        if string is None or string == "":
            return None, "ERROR: "

        if is_variable(string[0]):
            if len(string) == 1:
                return Formula(string[0]), ""
            i = 1
            while i != len(string) and string[i].isdigit():
                i = i+1
            return Formula(string[:i]), string[i:]

        if is_constant(string[0]):
            if len(string) == 1:
                return Formula(string[0]), ""
            return Formula(string[0]), string[1:]

        if is_unary(string[0]):
            if Formula._parse_prefix(string[1:])[0] != None:
                return Formula('~', Formula._parse_prefix(string[1:])[0]), Formula._parse_prefix(string[1:])[1]
            return None, "ERROR: "

        if string[0] == '(':
            i = 1
            sum_of_open_bracket = 1
            while len(string) != i and sum_of_open_bracket != 0:  # find the operator index
                if string[i] == '(':
                    sum_of_open_bracket = sum_of_open_bracket + 1
                if string[i] == ')':
                    sum_of_open_bracket = sum_of_open_bracket - 1
                i = i+1
            if sum_of_open_bracket == 0 and Formula.is_formula(string[:i]):
                return Formula.parse(string[:i]), string[i:]

        return None, "ERROR: "


    @staticmethod
    def is_formula(string: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            string: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5
        if string is None or string == "":
            return False

        if is_constant(string) or is_variable(string):
            return True

        if is_unary(string[0]):
            return Formula.is_formula(string[1:])

        if string[0] == '(':
            sum_of_open_bracket = 1    # We check for inner loops and find the operator index
            i = 1
            while len(string) != i:    # find the operator index
                if string[i] == '(':
                    sum_of_open_bracket = sum_of_open_bracket+1
                if string[i] == ')':
                    sum_of_open_bracket = sum_of_open_bracket-1
                if is_binary(string[i]) and sum_of_open_bracket == 1:   # found regular operator
                    return Formula.is_formula(string[1:i]) and Formula.is_formula(string[i+1:-1])
                if i+2 < len(string) and is_binary(string[i:i+2]) and sum_of_open_bracket == 1:  # found 2 digits op
                    return Formula.is_formula(string[1:i]) and Formula.is_formula(string[i+2:-1])
                if i+3 < len(string) and is_binary(string[i:i+3]) and sum_of_open_bracket == 1:  # found 3 digits op
                    return Formula.is_formula(string[1:i]) and Formula.is_formula(string[i + 3:-1])
                i = i+1
            return False

        return False




        
    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(string)
        # Task 1.6
        if is_variable(string[0]) or is_constant(string[0]):
            return Formula(string)

        if is_unary(string[0]):
            return Formula(string[0], Formula.parse(string[1:]))

        if string[0] == '(':
            sum_of_open_bracket = 1  # We check for inner loops and find the operator index
            i = 1
            while len(string) != i:  # find the operator index
                if string[i] == '(':
                    sum_of_open_bracket = sum_of_open_bracket + 1
                if string[i] == ')':
                    sum_of_open_bracket = sum_of_open_bracket - 1
                if is_binary(string[i]) and sum_of_open_bracket == 1:  # found regular operator
                    first_formula = Formula.parse(string[1:i])
                    second_formula = Formula.parse(string[i+1:-1])
                    return Formula(string[i], first_formula, second_formula)
                if i+2 < len(string) and is_binary(string[i:i + 2]) and sum_of_open_bracket == 1:  # found 2 digits op
                    first_formula = Formula.parse(string[1:i])
                    second_formula = Formula.parse(string[i + 2:-1])
                    return Formula(string[i:i + 2], first_formula, second_formula)
                if i+3 < len(string) and is_binary(string[i:i + 3]) and sum_of_open_bracket == 1:  # found <-> operator
                    first_formula = Formula.parse(string[1:i])
                    second_formula = Formula.parse(string[i + 3:-1])
                    return Formula(string[i:i + 3], first_formula, second_formula)
                i = i + 1



    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

    @staticmethod
    def parse_polish(string: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Substitutes in the current formula, each variable name `v` that is a
        key in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            variables name occurrences originating in the current formula are
            substituted (i.e., variable name occurrences originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((p->p)|r)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
            (((q&r)->(q&r))|p)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3
        keys = substitution_map.keys()
        if len(keys) == 0 or len(self.variables()) == 0:  # nothing to change
            return self
        if is_variable(self.root):
            if self.root in keys:
                return substitution_map[self.root]
            return self
        if is_unary(self.root):
            return Formula("~", self.first.substitute_variables(substitution_map))
        if is_binary(self.root):
            return Formula(self.root, self.first.substitute_variables(substitution_map),
                           self.second.substitute_variables(substitution_map))
        return self

    def substitute_operators(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            operator occurrences originating in the current formula are
            substituted (i.e., operator occurrences originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_constant(operator) or is_unary(operator) or \
                   is_binary(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4
        keys = substitution_map.keys()
        if len(keys) == 0:  # nothing to change
            return self
        if is_constant(self.root):
            if self.root in keys:
                return substitution_map[self.root]
            return self
        if is_unary(self.root):
            new_formula = Formula("~", self.first.substitute_operators(substitution_map))
            if self.root in keys:
                new_dict = {"p": new_formula.first}
                # imaginary formula with full of "p" instead of first argument
                transformed_formula_imaginary = substitution_map[self.root]
                transformed_formula_real = transformed_formula_imaginary.substitute_variables(new_dict)
                return transformed_formula_real
            return new_formula
        if is_binary(self.root):
            new_formula = Formula(self.root, self.first.substitute_operators(substitution_map),
                                  self.second.substitute_operators(substitution_map))
            if self.root in keys:
                new_dict = {"p": new_formula.first, "q": new_formula.second}
                # current formula with full of "p" and "q" instead of regular variable
                transformed_formula_imaginary = substitution_map[self.root]
                # imaginary = with p and q instead of real values
                transformed_formula_real = transformed_formula_imaginary.substitute_variables(new_dict)
                return transformed_formula_real
            return new_formula
        return self
