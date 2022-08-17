# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: predicates/syntax.py

"""Syntactic handling of predicate-logic expressions."""

from __future__ import annotations
from functools import lru_cache
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union

from logic_utils import fresh_variable_name_generator, frozen, \
                        memoized_parameterless_method

from propositions.syntax import Formula as PropositionalFormula, \
                                is_variable as is_propositional_variable

class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context.

    Attributes:
        variable_name (`str`): the variable name that was forbidden in the
            context in which a term containing it was to be substituted.
    """
    variable_name: str

    def __init__(self, variable_name: str):
        """Initializes a `ForbiddenVariableError` from the offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it is to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name

@lru_cache(maxsize=100) # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return  (((string[0] >= '0' and string[0] <= '9') or \
              (string[0] >= 'a' and string[0] <= 'e')) and \
             string.isalnum()) or string == '_'

@lru_cache(maxsize=100) # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= 'u' and string[0] <= 'z' and string.isalnum()

@lru_cache(maxsize=100) # Cache the return value of is_function
def is_function(string: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return string[0] >= 'f' and string[0] <= 't' and string.isalnum()

@frozen
class Term:
    """An immutable predicate-logic term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a function name.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str, arguments: Optional[Sequence[Term]] = None):
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments for the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None and len(arguments) > 0
            self.root = root
            self.arguments = tuple(arguments)

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        # Task 7.1
        #self.root[0] >= 'u' and self.root[0] <= 'z' and \
        #   (len(self.root) == 1 or self.root[1:].isalnum())
        if is_variable(self.root) or is_constant(self.root):
            return self.root
        # function
        cur_str = self.root + "("
        for arg in self.arguments:
            cur_str += str(arg) + ","
        cur_str = cur_str[:-1]
        cur_str += ")"
        return cur_str

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)
        
    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.3a
        if is_variable(string[0]) or is_constant(string[0]):
            n = 1
            while string[:n + 1].isalnum() and len(string) > n:
                n += 1
            return Term(string[:n]), string[n:]
        if is_function(string[0]):
            n = 1
            while string[:n + 1].isalnum() and string[n] != '(':
                n += 1
            func_name = string[:n]
            arguments = list()
            left, rest = Term._parse_prefix(string[n + 1:])
            arguments.append(left)
            while rest[0] == ',':
                left, rest = Term._parse_prefix(rest[1:])
                arguments.append(left)
            return Term(func_name, arguments), rest[1:]


    @staticmethod
    def parse(string: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            string: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        # Task 7.3b
        return Term._parse_prefix(string)[0]


    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        # Task 7.5a
        constants_set = set()
        if is_constant(self.root):
            constants_set.add(self.root)
        if is_function(self.root):
            for term in self.arguments:
                constants_set.update(term.constants())
        return constants_set


    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        # Task 7.5b
        variables_set = set()
        if is_variable(self.root):
            variables_set.add(self.root)
        if is_function(self.root):
            for term in self.arguments:
                variables_set.update(term.variables())
        return variables_set

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        # Task 7.5c
        tuple_set = set()
        if is_function(self.root):
            tuple_set.add((self.root, len(self.arguments)))
            for term in self.arguments:
                tuple_set.update(term.functions())
        return tuple_set


    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> Term:
        """Substitutes in the current term, each constant name `construct` or
        variable name `construct` that is a key in `substitution_map` with the
        term `substitution_map[construct].

        Parameters:
            substitution_map: mapping the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current term are substituted (i.e., those originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from
                `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))

            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1

        if is_function(self.root):
            args_list = list()
            for arg in self.arguments:
                args_list.append(arg.substitute(substitution_map, forbidden_variables))
            return Term(self.root, args_list)

        if self.root in substitution_map:
            if is_variable(self.root) or is_constant(self.root):
                vars_from_map = substitution_map[self.root].variables()
                for var in vars_from_map:
                    if var in forbidden_variables:
                        raise ForbiddenVariableError(var)

        if is_variable(self.root) or is_constant(self.root):
            if self.root in substitution_map:
                new_val = substitution_map[self.root]
                if str(new_val) in forbidden_variables:
                    raise ForbiddenVariableError(str(new_val))
                return substitution_map[self.root]
            return Term(self.root)

        # check validity
        new_args = []
        for arg in self.arguments:
            new_args.append(arg.substitute(substitution_map,
                                           forbidden_variables))
        new_term = Term(self.root, new_args)
        for arg in new_term.variables():
            if arg in forbidden_variables:
                raise ForbiddenVariableError(arg)
        return new_term



@lru_cache(maxsize=100) # Cache the return value of is_equality
def is_equality(string: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return string == '='

@lru_cache(maxsize=100) # Cache the return value of is_relation
def is_relation(string: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return string[0] >= 'F' and string[0] <= 'T' and string.isalnum()

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
    return string == '&' or string == '|' or string == '->'

@lru_cache(maxsize=100) # Cache the return value of is_quantifier
def is_quantifier(string: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return string == 'A' or string == 'E'

@frozen
class Formula:
    """An immutable predicate-logic formula in tree representation, composed
    from relation names applied to predicate-logic terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        statement (`~typing.Optional`\\[`Formula`]): the statement quantified by
            the root, if the root is a quantification.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    statement: Optional[Formula]

    def __init__(self, root: str,
                 arguments_or_first_or_variable: Union[Sequence[Term],
                                                       Formula, str],
                 second_or_statement: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable name and statement.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments for the root, if the
                root is a relation name or the equality relation; the first
                operand for the root, if the root is a unary or binary operator;
                the variable name to be quantified by the root, if the root is a
                quantification.
            second_or_statement: the second operand for the root, if the root is
                a binary operator; the statement to be quantified by the root,
                if the root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert isinstance(arguments_or_first_or_variable, Sequence) and \
                   not isinstance(arguments_or_first_or_variable, str)
            if is_equality(root):
                assert len(arguments_or_first_or_variable) == 2
            assert second_or_statement is None
            self.root, self.arguments = \
                root, tuple(arguments_or_first_or_variable)
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula)
            assert second_or_statement is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula)
            assert second_or_statement is not None
            self.root, self.first, self.second = \
                root, arguments_or_first_or_variable, second_or_statement
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.statement
            assert isinstance(arguments_or_first_or_variable, str) and \
                   is_variable(arguments_or_first_or_variable)
            assert second_or_statement is not None
            self.root, self.variable, self.statement = \
                root, arguments_or_first_or_variable, second_or_statement

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 7.2
        if is_equality(self.root):
            return '{}={}'.format(str(self.arguments[0]),
                                  str(self.arguments[1]))
        if is_unary(self.root):
            return '~{}'.format(self.first)
        if is_binary(self.root):
            return '({}{}{})'.format(str(self.first), self.root,
                                     str(self.second))
        if is_relation(self.root):
            relation = '{}('.format(self.root)
            for term in self.arguments:
                relation += '{},'.format(str(term))
            if len(self.arguments) != 0:
                relation = relation[:-1]
            relation += ')'
            return relation
        if is_quantifier(self.root):
            return '{}{}[{}]'.format(self.root, self.variable,
                                     str(self.statement))



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

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'f(y)=c12'``) or by a variable
            name (e.g., ``'f(y)=x12'``), then the parsed prefix will include
            that entire name (and not just a part of it, such as ``'f(y)=x1'``).
        """
        # Task 7.4a
        if is_unary(string[0]):
            left, rest = Formula._parse_prefix(string[1:])
            return Formula('~', left), rest
        if is_relation(string[0]):
            n = 1
            while string[:n + 1].isalnum() and string[n] != '(':
                n += 1
            relation = string[:n]
            if string[n+1] == ")":
                return Formula(relation, []), string[n+2:]
            arguments = list()
            left, rest = Term._parse_prefix(string[n + 1:])  # Skips '('
            arguments.append(left)
            while rest[0] == ',':
                left, rest = Term._parse_prefix(rest[1:])  # Skips '('
                arguments.append(left)
            return Formula(relation, arguments), rest[1:]
        if is_function(string[0]) or is_constant(string[0]) or \
                is_variable(string[0]):  # is_equality
            left = Term.parse(string)
            length1 = len(str(left))
            right = Term.parse(string[length1 + 1:])
            length2 = len(str(right))
            return Formula('=', [left, right]), string[length1 + length2 + 1:]
        if is_quantifier(string[0]):
            n = 1
            while string[:n + 1].isalnum() and string[n] != '[':
                n += 1
            var_name = string[1:n]
            statement, rest = Formula._parse_prefix(string[n + 1:])
            return Formula(string[0], var_name, statement), rest[1:]
        if string[0] == '(':  # is_binary
            left = Formula._parse_prefix(string[1:])[0]
            length1 = len(str(left))
            binary = string[length1 + 1]
            if binary == "-":
                binary += ">"
                length1 += 1
            right = Formula._parse_prefix(string[length1 + 2:])[0]
            length2 = len(str(right))
            return Formula(binary, left, right), string[length1 + length2 + 3:]


    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        # Task 7.4b
        return Formula._parse_prefix(string)[0]

    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        # Task 7.6a
        constants_set = set()
        if is_unary(self.root):
            constants_set.update(self.first.constants())
        if is_relation(self.root):
            for term in self.arguments:
                constants_set.update(term.constants())
        if is_equality(self.root):
            constants_set.update(self.arguments[0].constants())
            constants_set.update(self.arguments[1].constants())
        if is_quantifier(self.root):
            constants_set.update(self.statement.constants())
        if is_binary(self.root):
            constants_set.update(self.first.constants())
            constants_set.update(self.second.constants())
        return constants_set



    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 7.6b
        variables_set = set()
        if is_unary(self.root):
            variables_set.update(self.first.variables())
        if is_relation(self.root):
            for term in self.arguments:
                variables_set.update(term.variables())
        if is_equality(self.root):
            variables_set.update(self.arguments[0].variables())
            variables_set.update(self.arguments[1].variables())
        if is_quantifier(self.root):
            variables_set.add(self.variable)
            variables_set.update(self.statement.variables())
        if is_binary(self.root):
            variables_set.update(self.first.variables())
            variables_set.update(self.second.variables())
        return variables_set

    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of every variable name that is used in the current formula not
            only within a scope of a quantification on that variable name.
        """
        # Task 7.6c
        variables_set = set()
        if is_quantifier(self.root):
            variables_set = self.statement.free_variables()
            if self.variable in variables_set:
                variables_set.remove(self.variable)
        if is_unary(self.root):
            variables_set.update(self.first.free_variables())
        if is_binary(self.root):
            variables_set.update(self.first.free_variables())
            variables_set.update(self.second.free_variables())
        if is_equality(self.root) or is_relation(self.root):
            variables_set.update(self.variables())
        return variables_set


    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        # Task 7.6d
        functions_set = set()
        if is_function(self.root):
            functions_set.add((self.root, len(self.arguments)))
            for formula in self.arguments:
                functions_set.update(formula.functions())
        if is_equality(self.root):
            functions_set.update(self.arguments[0].functions())
            functions_set.update(self.arguments[1].functions())
        if is_relation(self.root):
            for term in self.arguments:
                functions_set.update(term.functions())
        if is_binary(self.root):
            functions_set.update(self.first.functions())
            functions_set.update(self.second.functions())
        if is_quantifier(self.root):
            functions_set.update(self.statement.functions())
        if is_unary(self.root):
            functions_set.update(self.first.functions())
        return functions_set

    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        # Task 7.6e
        relations_set = set()
        if is_quantifier(self.root):
            relations_set.update(self.statement.relations())
        if is_unary(self.root):
            relations_set.update(self.first.relations())
        if is_binary(self.root):
            relations_set.update(self.first.relations())
            relations_set.update(self.second.relations())
        if is_relation(self.root):
            relations_set.add((self.root, len(self.arguments)))
        return relations_set

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> \
            Formula:
        """Substitutes in the current formula, each constant name `construct` or
        free occurrence of variable name `construct` that is a key in
        `substitution_map` with the term
        `substitution_map[construct].

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current formula are substituted (i.e., those originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from `forbidden_variables`
                or a variable name occurrence that becomes bound when that term
                is substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)

        if is_quantifier(self.root):
            variable = self.variable
            new_subtitution_map = dict()
            new_subtitution_map.update(substitution_map)
            if variable in substitution_map:
                del new_subtitution_map[variable]
            next_forbidden_variables = set(forbidden_variables)
            next_forbidden_variables.add(self.variable)
            statement = self.statement.substitute(new_subtitution_map, next_forbidden_variables)
            return Formula(self.root, variable, statement)

        if is_equality(self.root): # arguments 0 and 1
            left_term = self.arguments[0].substitute(substitution_map, forbidden_variables)
            right_term = self.arguments[1].substitute(substitution_map, forbidden_variables)
            new_formula = Formula("=", (left_term, right_term))
            return new_formula

        if is_relation(self.root):  # arguments
            arguments = list()
            for arg in self.arguments:
                arguments.append(arg.substitute(substitution_map, forbidden_variables))
            new_formula = Formula(self.root, arguments)
            return new_formula

        if is_binary(self.root):
            left_func = self.first.substitute(substitution_map, forbidden_variables)
            right_func = self.second.substitute(substitution_map, forbidden_variables)
            new_formula = Formula(self.root, left_func, right_func)
            return new_formula

        if is_unary(self.root):
            func = self.first.substitute(substitution_map, forbidden_variables)
            new_formula = Formula(self.root, func)
            return new_formula

    def propositional_skeleton(self) -> Tuple[PropositionalFormula,
                                              Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation name or quantifier at its root with a
            propositional variable name, consistently such that multiple
            identical such (outermost) subformulas are substituted with the same
            propositional variable name. The propositional variable names used
            for substitution are obtained, from left to right (considering their
            first occurrence), by calling
            next(~logic_utils.fresh_variable_name_generator).
            The second element of the pair is a mapping from each propositional
            variable name to the subformula for which it was substituted.

        Examples:
            >>> formula = Formula.parse('((Ax[x=7]&x=7)|(~Q(y)->x=7))')
            >>> formula.propositional_skeleton()
            (((z1&z2)|(~z3->z2)), {'z1': Ax[x=7], 'z2': x=7, 'z3': Q(y)})
            >>> formula.propositional_skeleton()
            (((z4&z5)|(~z6->z5)), {'z4': Ax[x=7], 'z5': x=7, 'z6': Q(y)})
        """
        # Task 9.8
        new_dict = dict()
        new_tup = self.propositional_skeleton_helper_itamar_made(new_dict)
        return new_tup

    def propositional_skeleton_helper_itamar_made(self, cur_dict) -> Tuple[PropositionalFormula,
                                              Mapping[str, Formula]]:
        new_dict = cur_dict
        new_formula = self
        if is_quantifier(self.root) or is_relation(self.root) or is_equality(self.root):
            new_var = ""
            if self in cur_dict.values():
                for key in cur_dict:
                    if cur_dict[key] == self:
                        new_var = key
                        break
            else:
                new_var = next(fresh_variable_name_generator)
                new_dict[new_var] = new_formula
            return PropositionalFormula(new_var), new_dict
        if is_unary(self.root):
            temp_formula = new_formula
            if self.first in cur_dict.values():
                for key in cur_dict:
                    if cur_dict[key] == self.first:
                        temp_formula = PropositionalFormula(key)
                        break
            else:
                temp_formula, temp_dict = self.first.propositional_skeleton_helper_itamar_made(cur_dict)
                new_dict.update(temp_dict)
            new_formula = PropositionalFormula('~', temp_formula)
            return new_formula, new_dict
        if is_binary(self.root):
            temp_formula1, temp_dict1 = self.first.propositional_skeleton_helper_itamar_made(cur_dict)
            new_dict.update(temp_dict1)
            temp_formula2, temp_dict2 = self.second.propositional_skeleton_helper_itamar_made(cur_dict)
            new_dict.update(temp_dict2)
            new_formula = PropositionalFormula(self.root, temp_formula1, temp_formula2)
            return new_formula, new_dict

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula,
                                    substitution_map: Mapping[str, Formula]) \
            -> Formula:
        """Computes a predicate-logic formula from a propositional skeleton and
        a substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute,
                containing no constants or operators beyond ``'~'``, ``'->'``,
                ``'|'``, and ``'&'``.
            substitution_map: mapping from each propositional variable name of
                the given propositional skeleton to a predicate-logic formula.

        Returns:
            A predicate-logic formula obtained from the given propositional
            skeleton by substituting each propositional variable name with the
            formula mapped to it by the given map.

        Examples:
            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z1&z2)|(~z3->z2))'),
            ...     {'z1': Formula.parse('Ax[x=7]'), 'z2': Formula.parse('x=7'),
            ...      'z3': Formula.parse('Q(y)')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))

            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z9&z2)|(~z3->z2))'),
            ...     {'z2': Formula.parse('x=7'), 'z3': Formula.parse('Q(y)'),
            ...      'z9': Formula.parse('Ax[x=7]')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))
        """
        for operator in skeleton.operators():
            assert is_unary(operator) or is_binary(operator)
        for variable in skeleton.variables():
            assert variable in substitution_map
        # Task 9.10
        prop_form_str = str(skeleton)
        for mapper in substitution_map:
            prop_form_str = prop_form_str.replace(mapper, str(substitution_map[mapper]))
        return Formula.parse(prop_form_str)