# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: predicates/proofs.py

"""Schemas and proofs in Predicate Logic."""

from __future__ import annotations
from typing import AbstractSet, FrozenSet, Mapping, Sequence, Tuple, Union

from logic_utils import frozen, frozendict

from propositions.semantics import is_tautology as is_propositional_tautology

from predicates.syntax import *

# itamar added
from propositions.tautology import proof_or_counterexample as propositional_prove_or_counter_exapmle

#: A mapping from constant names, variable names, and relation names to
#: terms, variable names, and formulas respectively.
InstantiationMap = Mapping[str, Union[Term, str, Formula]]

@frozen
class Schema:
    """An immutable schema of predicate-logic formulas, comprised of a formula
    along with the constant names, variable names, and nullary or unary relation
    names in that formula that serve as templates. A template constant name is a
    placeholder for any term. A template variable name is a placeholder for any
    variable name. A template nullary or unary relation name is a placeholder
    for any (parametrized for a unary template relation name) predicate-logic
    formula that does not refer to any variable name in the schema (except
    possibly through its instantiated argument for a unary relation name).

    Attributes:
        formula (`~predicates.syntax.Formula`): the formula of the schema.
        templates (`~typing.FrozenSet`\\[`str`]): the constant, variable, and
            relation names from the formula that serve as templates.
    """
    formula: Formula
    templates: FrozenSet[str]

    def __init__(self, formula: Formula,
                 templates: AbstractSet[str] = frozenset()):
        """Initializes a `Schema` from its formula and template names.

        Parameters:
            formula : the formula for the schema.
            templates: the constant, variable, and relation names from the
                formula to serve as templates.
        """
        for template in templates:
            assert is_constant(template) or is_variable(template) or \
                   is_relation(template)
            if is_relation(template):
                arities = {arity for relation,arity in formula.relations() if
                           relation == template}
                assert arities == {0} or arities == {1}
        self.formula = formula
        self.templates = frozenset(templates)

    def __repr__(self) -> str:
        """Computes a string representation of the current schema.

        Returns:
            A string representation of the current schema.
        """
        return 'Schema: ' + str(self.formula) + ' [templates: ' + \
               ('none' if len(self.templates) == 0 else
                ", ".join(sorted(self.templates))) + ']'

    def __eq__(self, other: object) -> bool:
        """Compares the current schema with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Schema` object that equals the
            current schema, ``False`` otherwise.
        """
        return isinstance(other, Schema) and self.formula == other.formula and \
               self.templates == other.templates

    def __ne__(self, other: object) -> bool:
        """Compares the current schema with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Schema` object or does not
            equal the current schema, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    class BoundVariableError(Exception):
        """Raised by `_instantiate_helper` when a variable name becomes bound
        during a schema instantiation in a way that is disallowed in that
        context.

        Attributes:
            variable_name (`str`): the variable name that became bound in a way
                that was disallowed during a schema instantiation.
            relation_name (`str`): the relation name during whose substitution
                the relevant occurrence of the variable name became bound.
        """
        variable_name: str
        relation_name: str

        def __init__(self, variable_name: str, relation_name: str):
            """Initializes a `~Schema.BoundVariableError` from the offending
            variable name and the relation name during whose substitution the
            error occurred.

            Parameters:
                variable_name: variable name that is to become bound in a way
                    that is disallowed during a schema instantiation.
                relation_name: the relation name during whose substitution the
                    relevant occurrence of the variable name is to become bound.
            """            
            assert is_variable(variable_name)
            assert is_relation(relation_name)
            self.variable_name = variable_name
            self.relation_name = relation_name

    @staticmethod
    def _instantiate_helper(formula: Formula,
                            constants_and_variables_instantiation_map:
                            Mapping[str, Term],
                            relations_instantiation_map: Mapping[str, Formula],
                            bound_variables: AbstractSet[str] = frozenset()) \
            -> Formula:
        """Performs the following substitutions in the given formula:

        1. Substitute each occurrence of each constant name or variable name
           that is a key of the given constants and variables instantiation map
           with the term mapped to this name by this map.
        2. Substitute each nullary invocation of each relation name that is a
           key of the given relations instantiation map with the formula mapped
           to it by this map.
        3. For each unary invocation of each relation name that is a key of the
           given relations instantiation map, first perform all substitutions
           to the argument of this invocation (according to the given constants
           and variables instantiation map), then substitute the result for
           each occurrence of the constant name ``'_'`` in the formula mapped to
           the relation name by this map, and then substitute the result for
           this unary invocation of the relation name.

        Only name occurrences originating in the given formula are substituted
        (i.e., name occurrences originating in one of the above substitutions
        are not subjected to additional substitutions).

        Parameters:
            formula: formula in which to perform the substitutions.
            constants_and_variables_instantiation_map: mapping from constant
                names and variable names in the given formula to terms to be
                substituted for them, where the roots of terms mapped to
                variable names are variable names.
            relations_instantiation_map: mapping from nullary and unary relation
                names in the given formula to formulas to be substituted for
                them, where formulas to be substituted for unary relation names
                are parametrized by the constant name ``'_'``.
            bound_variables: variable names to be treated as bound (see below).

        Returns:
            The result of all substitutions.

        Raises:
            BoundVariableError: if one of the following occurs when substituting
                an invocation of a relation name:

                1. A free occurrence of a variable name in the formula
                   mapped to the relation name by the given relations
                   instantiation map is in `bound_variables` or becomes bound
                   by a quantification in the given formula after all variable
                   names in the given formula have been substituted.
                2. For a unary invocation: a variable name that is in the
                   argument to that invocation after all substitutions have been
                   applied to this argument, becomes bound by a quantification
                   in the formula mapped to the relation name by the given
                   relations instantiation map.

        Examples:
            The following succeeds:
            
            >>> Schema._instantiate_helper(
            ...     Formula.parse('Ax[(Q(c)->R(x))]'), {'x': Term('w')},
            ...     {'Q': Formula.parse('y=_')}, {'x', 'z'})
            Aw[(y=c->R(w))]

            however the following fails since ``'Q(c)'`` is to be substituted
            with ``'y=c'`` while ``'y'`` is specified to be treated as bound:
            
            >>> Schema._instantiate_helper(
            ...     Formula.parse('Ax[(Q(c)->R(x))]'), {},
            ...     {'Q': Formula.parse('y=_')}, {'x', 'y', 'z'})
            Traceback (most recent call last):
              ...
            predicates.proofs.Schema.BoundVariableError: ('y', 'Q')

            and the following fails since as ``'Q(c)'`` is to be substituted
            with ``'y=c'``, ``'y'`` is to become bound by the quantification
            ``'Ay'``:
            
            >>> Schema._instantiate_helper(
            ...     Formula.parse('Ax[(Q(c)->R(x))]'), {'x': Term('y')},
            ...     {'Q': Formula.parse('y=_')})
            Traceback (most recent call last):
              ...
            predicates.proofs.Schema.BoundVariableError: ('y', 'Q')

            The following succeeds:
            
            >>> Schema._instantiate_helper(
            ...     Formula.parse('Ax[(Q(c)->R(x))]'),
            ...     {'c': Term.parse('plus(d,x)')},
            ...     {'Q': Formula.parse('Ey[y=_]')})
            Ax[(Ey[y=plus(d,x)]->R(x))]

            however the following fails since as ``'_'`` is to be substituted
            with ``'plus(d,y)'`` in ``'Ey[y=_]'``, the ``'y'`` in
            ``'plus(d,y)'`` is to become bound by the quantification ``'Ey'``:

            >>> Schema._instantiate_helper(
            ...     Formula.parse('Ax[(Q(c)->R(x))]'),
            ...     {'c': Term.parse('plus(d,y)')},
            ...     {'Q': Formula.parse('Ey[y=_]')})
            Traceback (most recent call last):
              ...
            predicates.proofs.Schema.BoundVariableError: ('y', 'Q')
        """
        for construct in constants_and_variables_instantiation_map:
            assert is_constant(construct) or is_variable(construct)
            if is_variable(construct):
                assert is_variable(
                    constants_and_variables_instantiation_map[construct].root)
        for relation in relations_instantiation_map:
            assert is_relation(relation)
        for variable in bound_variables:
            assert is_variable(variable)

        # Task 9.3
        first_relation_cond = is_relation(formula.root) and formula.root not in relations_instantiation_map or is_equality(
                formula.root)
        if first_relation_cond:   # easy case
            args_list = list()
            for arg in formula.arguments:
                args_list.append(arg.substitute(constants_and_variables_instantiation_map, set()))
            return Formula(formula.root, args_list)
        second_relation_cond = is_relation(formula.root) and formula.root in relations_instantiation_map
        if second_relation_cond:  # hard case
            # check validity
            root = formula.root
            vars = relations_instantiation_map[root].free_variables()
            if len(formula.arguments) == 0:
                for cur_var in vars:
                    if cur_var in bound_variables:
                        raise Schema.BoundVariableError(cur_var, root)   # 3
                return relations_instantiation_map[root]
            else:
                first_arg_subtituted = formula.arguments[0].substitute(constants_and_variables_instantiation_map, set())
                for cur_var in vars:
                    if cur_var in bound_variables:
                        raise Schema.BoundVariableError(cur_var, root)    # 4
                # check valid
                try:
                    new_case = relations_instantiation_map[root].substitute({'_': first_arg_subtituted}, set())
                    return new_case
                except ForbiddenVariableError as e:
                    raise Schema.BoundVariableError(e.variable_name, root)   # 5

        if is_quantifier(formula.root):
            bound_variable = set(bound_variables)
            new_var = formula.variable
            bound_variable.add(formula.variable)
            new_variable = formula.variable
            # check for validity
            if new_var in constants_and_variables_instantiation_map:
                if new_variable == new_var:
                    new_var = formula.variable
                bound_variable.remove(new_var)
                new_variable = constants_and_variables_instantiation_map[new_var]
                bound_variable.add(str(new_variable))
            cur_formula = Formula(formula.root, str(new_variable),
                           Schema._instantiate_helper(
                               formula.statement, constants_and_variables_instantiation_map,
                               relations_instantiation_map,
                               bound_variable))
            return cur_formula

        if is_binary(formula.root):
            left_func = Schema._instantiate_helper(formula.first, constants_and_variables_instantiation_map,
                                                   relations_instantiation_map, bound_variables)
            right_func = Schema._instantiate_helper(formula.second, constants_and_variables_instantiation_map,
                                                    relations_instantiation_map, bound_variables)
            new_formula = Formula(formula.root, left_func, right_func)
            return new_formula

        if is_unary(formula.root):
            func = Schema._instantiate_helper(formula.first, constants_and_variables_instantiation_map,
                                              relations_instantiation_map, bound_variables)
            new_formula = Formula(formula.root, func)
            return new_formula

    def instantiate(self, instantiation_map: InstantiationMap) -> \
            Union[Formula, None]:
        """Instantiates the current schema according to the given map from
        templates of the current schema to expressions.

        Parameters:
            instantiation_map: mapping from templates of the current schema to
                expressions of the type for which they serve as placeholders.
                That is, constant names are mapped to terms, variable names are
                mapped to variable names (strings), and relation names are
                mapped to formulas where unary relation names are mapped to
                formulas parametrized by the constant name ``'_'``.

        Returns:
            The predicate-logic formula obtained by applying the substitutions
            specified by the given map to the formula of the current schema:

            1. Each occurrence in the formula of the current schema of each
               template constant name specified in the given map is substituted
               with the term to which that template constant name is mapped.
            2. Each occurrence in the formula of the current schema of each
               template variable name specified in the given map is substituted
               with the variable name to which that template variable name is
               mapped.
            3. Each nullary invocation in the formula of the current schema of
               each template relation name specified in the given map is
               substituted with the formula to which that template relation name
               is mapped.
            4. Each unary invocation in the formula of the current schema of
               each template relation name specified in the given map is
               substituted with the formula to which that template relation name
               is mapped, in which each occurrence of the constant name ``'_'``
               is substituted with  the instantiated argument of that invocation
               of the template relation name (that is, the term that results
               from instantiating the argument of that invocation by performing
               all the specified substitutions on it).

            ``None`` is returned if one of the keys of the given map is not a
            template of the current schema or if one of the following occurs
            when substituting an invocation of a template relation name:

            1. A free occurrence of a variable name in the formula substituted
               for the template relation name becomes bound by a quantification
               in the instantiated schema formula, except if the template
               relation name is unary and this free occurrence originates in the
               instantiated argument of the invocation of the template relation
               name.
            2. For a unary invocation: a variable name in the instantiated
               argument of that invocation becomes bound by a quantification in
               the formula that is substituted for the invocation of the
               template relation name.
            
        Examples:
            >>> s = Schema(Formula.parse('(Q(c1,c2)->(R(c1)->R(c2)))'),
            ...            {'c1', 'c2', 'R'})
            >>> s.instantiate({'c1': Term.parse('plus(x,1)'),
            ...                'R': Formula.parse('Q(_,y)')})
            (Q(plus(x,1),c2)->(Q(plus(x,1),y)->Q(c2,y)))
            >>> s.instantiate({'c1': Term.parse('plus(x,1)'),
            ...                'c2': Term.parse('c1'),
            ...                'R': Formula.parse('Q(_,y)')})
            (Q(plus(x,1),c1)->(Q(plus(x,1),y)->Q(c1,y)))

            >>> s = Schema(Formula.parse('(P()->P())'), {'P'})
            >>> s.instantiate({'P': Formula.parse('plus(a,b)=c')})
            (plus(a,b)=c->plus(a,b)=c)

            For the following schema:
            
            >>> s = Schema(Formula.parse('(Q(d)->Ax[(R(x)->Q(f(c)))])'),
            ...            {'R', 'Q', 'x', 'c'})

            the following succeeds:
            
            >>> s.instantiate({'R': Formula.parse('_=0'),
            ...                'Q': Formula.parse('x=_'),
            ...                'x': 'w'})
            (x=d->Aw[(w=0->x=f(c))])

            however, the following returns ``None`` because ``'d'`` is not a
            template of the schema:

            >>> s.instantiate({'R': Formula.parse('_=0'),
            ...                'Q': Formula.parse('x=_'),
            ...                'x': 'w',
            ...                'd': Term('z')})

            and the following returns ``None`` because ``'z'`` that is free in
            the assignment to ``'Q'`` is to become bound by a quantification in
            the instantiated schema formula:
            
            >>> s.instantiate({'R': Formula.parse('_=0'),
            ...                'Q': Formula.parse('s(z)=_'),
            ...                'x': 'z'})

            and the following returns ``None`` because ``'y'`` in the
            instantiated argument ``'f(plus(a,y))'`` of the second invocation of
            ``'Q'`` is to become bound by the quantification in the formula
            substituted for ``'Q'``:

            >>> s.instantiate({'R': Formula.parse('_=0'),
            ...                'Q': Formula.parse('Ay[s(y)=_]'),
            ...                'c': Term.parse('plus(a,y)')})
        """
        for construct in instantiation_map:
            if is_variable(construct):
                assert is_variable(instantiation_map[construct])
            elif is_constant(construct):
                assert isinstance(instantiation_map[construct], Term)
            else:
                assert is_relation(construct)
                assert isinstance(instantiation_map[construct], Formula)
        # Task 9.4
        const_and_vars = dict()
        relations = dict()
        for var in instantiation_map:
            if is_variable(var) or is_constant(var):
                if not(var in self.templates):  ##!!
                    return None
                value = instantiation_map[var]
                if isinstance(value, str):
                    const_and_vars[var] = Term.parse(value)
                else:
                    const_and_vars[var] = value
            elif is_relation(var):
                relations[var] = instantiation_map[var]
        for relation in relations:
            if not (relation in self.templates):
                return None
        try:
            formula = Schema._instantiate_helper(self.formula,
                                              const_and_vars,
                                              relations,
                                              set())
            return formula
        except:
            return None


@frozen
class Proof:
    """An immutable deductive proof in Predicate Logic, comprised of a list of
    assumptions/axioms, a conclusion, and a list of lines that prove the
    conclusion from (instances of) these assumptions/axioms and from
    tautologies, via the Modus Ponens (MP) and Universal Generalization (UG)
    inference rules.

    Attributes:
        assumptions (`~typing.FrozenSet`\\[`Schema`]): the assumption/axioms of
            the proof.
        conclusion (`~predicates.syntax.Formula`): the conclusion of the proof.
        lines (`~typing.Tuple`\\[`Line`\]): the lines of the proof.
    """
    assumptions: FrozenSet[Schema]
    conclusion: Formula
    lines: Tuple[Proof.Line, ...]
    
    def __init__(self, assumptions: AbstractSet[Schema], conclusion: Formula,
                 lines: Sequence[Proof.Line]):
        """Initializes a `Proof` from its assumptions/axioms, conclusion,
        and lines.

        Parameters:
            assumptions: the assumption/axioms for the proof.
            conclusion: the conclusion for the proof.
            lines: the lines for the proof.
        """
        self.assumptions = frozenset(assumptions)
        self.conclusion = conclusion
        self.lines = tuple(lines)

    @frozen
    class AssumptionLine:
        """An immutable proof line justified as an instance of an
        assumption/axiom.

        Attributes:
            formula (`~predicates.syntax.Formula`): the formula justified by the
                line.
            assumption (`Schema`): the assumption/axiom that instantiates the
                formula.
            instantiation_map (`~typing.Mapping`\\[`str`, `~typing.Union`\\[`~predicates.syntax.Term`, `str`, `~predicates.syntax.Formula`]]):
                the mapping instantiating the formula from the assumption/axiom.
        """
        formula: Formula
        assumption: Schema
        instantiation_map: InstantiationMap
    
        def __init__(self, formula: Formula, assumption: Schema,
                     instantiation_map: InstantiationMap):
            """Initializes an `~Proof.AssumptionLine` from its formula, its
            justifying assumption/axiom, and its instantiation map from the
            justifying assumption/axiom.

            Parameters:
                formula: the formula to be justified by the line.
                assumption: the assumption/axiom that instantiates the formula.
                instantiation_map: the mapping instantiating the formula from
                    the assumption/axiom.
            """
            for construct in instantiation_map:
                if is_variable(construct):
                    assert is_variable(instantiation_map[construct])
                elif is_constant(construct):
                    assert isinstance(instantiation_map[construct], Term)
                else:
                    assert is_relation(construct)
                    assert isinstance(instantiation_map[construct], Formula)
            self.formula = formula
            self.assumption = assumption
            self.instantiation_map = frozendict(instantiation_map)

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            return str(self.formula) + "    (Assumption " + \
                   str(self.assumption) + " instantiated with " + \
                   str(self.instantiation_map) + ")"

        def is_valid(self, assumptions: AbstractSet[Schema],
                     lines: Sequence[Proof.Line], line_number: int) -> bool:
            """Checks if the current line is validly justified in the context of
            the specified proof.

            Parameters:
                assumptions: assumptions/axioms of the proof.
                lines: lines of the proof.
                line_number: line number of the current line in the given lines.

            Returns:
                ``True`` if the assumption/axiom of the current line is an
                assumption/axiom of the specified proof and if the formula
                justified by the current line is a valid instance of this
                assumption/axiom via the instantiation map of the current line,
                ``False`` otherwise.
            """
            assert line_number < len(lines) and lines[line_number] is self
            # Task 9.5
            if self.assumption not in assumptions:
                return False
            instantiation = self.assumption.instantiate(self.instantiation_map)
            if instantiation:
                if self.formula == instantiation:
                    return True
            return False
    
    @frozen
    class MPLine:
        """An immutable proof line justified by the Modus Ponens (MP) inference
        rule.

        Attributes:
            formula (`~predicates.syntax.Formula`): the formula justified by the
                line.
            antecedent_line_number (`int`): the line number of the antecedent of
                the MP inference justifying the line.
            conditional_line_number (`int`): the line number of the conditional
                of the MP inference justifying the line.
        """
        formula: Formula
        antecedent_line_number: int
        conditional_line_number: int

        def __init__(self, formula: Formula, antecedent_line_number: int,
                     conditional_line_number: int):
            """Initializes a `~Proof.MPLine` from its formula and line numbers
            of the antecedent and conditional of the MP inference justifying it.

            Parameters:
                formula: the formula to be justified by the line.
                antecedent_line_number: the line number of the antecedent of the
                    MP inference to justify the line.
                conditional_line_number: the line number of the conditional of
                    the MP inference to justify the line.
            """
            self.formula = formula
            self.antecedent_line_number = antecedent_line_number
            self.conditional_line_number = conditional_line_number

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            return str(self.formula) + "    (MP from lines " + \
                   str(self.antecedent_line_number) + " and " + \
                   str(self.conditional_line_number) + ")"

        def is_valid(self, assumptions: AbstractSet[Schema],
                     lines: Sequence[Proof.Line], line_number: int) -> bool:
            """Checks if the current line is validly justified in the context of
            the specified proof.

            Parameters:
                assumptions: assumptions/axioms of the proof.
                lines: lines of the proof.
                line_number: line number of the current line in the given lines.

            Returns:
                ``True`` if the formula of the line from the given lines whose
                number is the conditional line number justifying the current
                line is (antecedent`->consequent`),
                where `antecedent` is the formula of the line from the given
                lines whose number is the antecedent line number justifying the
                current line and `consequent` is the formula justified by the
                current line; ``False`` otherwise.
            """
            assert line_number < len(lines) and lines[line_number] is self
            # Task 9.6
            cur_line = lines[line_number]
            antecedent_line = lines[cur_line.antecedent_line_number]
            conditional_line = lines[cur_line.conditional_line_number]
            # if the conclusion of -> is the right formula
            if cur_line.formula != conditional_line.formula.second:
                return False
            # if the formula that is the left of the -> is what we have in antecedent_line
            if conditional_line.formula.first != antecedent_line.formula:
                return False
            # check that we are not jump to forward numbers
            if line_number <= cur_line.antecedent_line_number or line_number <= cur_line.conditional_line_number:
                return False
            return True

    @frozen
    class UGLine:
        """An immutable proof line justified by the Universal Generalization
        (UG) inference rule.

        Attributes:
            formula (`~predicates.syntax.Formula`): the formula justified by the
                line.
            nonquantified_line_number (`int`): the line number of the statement
                quantified by the formula.
        """
        formula: Formula
        nonquantified_line_number: int

        def __init__(self, formula: Formula, nonquantified_line_number: int):
            """Initializes a `~Proof.UGLine` from its formula and line number of
            the statement quantified by the formula.

            Parameters:
                formula: the formula to be justified by the line.
                nonquantified_line_number: the line number of the statement
                    quantified by the formula.
            """
            self.formula = formula
            self.nonquantified_line_number = nonquantified_line_number

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            return str(self.formula) + "    (UG of line " + \
                   str(self.nonquantified_line_number) + ")"

        def is_valid(self, assumptions: AbstractSet[Schema],
                     lines: Sequence[Proof.Line], line_number: int) -> bool:
            """Checks if the current line is validly justified in the context of
            the specified proof.

            Parameters:
                assumptions: assumptions/axioms of the proof.
                lines: lines of the proof.
                line_number: line number of the current line in the given lines.

            Returns:
                ``True`` if the formula of the current line is of the form
                 Ax[nonquantified], where
                `nonquantified` is the formula of the line from the given lines
                whose number is the nonquantified line number justifying the
                current line and `x` is any variable name; ``False`` otherwise.
            """
            assert line_number < len(lines) and lines[line_number] is self
            # Task 9.7
            if line_number <= self.nonquantified_line_number:
                return False
            if is_quantifier(self.formula.root) and \
                    lines[self.nonquantified_line_number].formula == self.formula.statement and \
                    self.formula.root == 'A':
                return True
            return False


    @frozen
    class TautologyLine:
        """An immutable proof line justified as a tautology.

        Attributes:
            formula (`~predicates.syntax.Formula`): the formula justified by the
                line.
        """
        formula: Formula

        def __init__(self, formula: Formula):
            """Initializes a `~Proof.TautologyLine` from its formula.

            Parameters:
                formula: the formula to be justified by the line.
            """
            self.formula = formula

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            return str(self.formula) + "    (Tautology)"

        def is_valid(self, assumptions: AbstractSet[Schema],
                     lines: Sequence[Proof.Line], line_number: int) -> bool:
            """Checks if the current line is validly justified in the context of
            the specified proof.

            Parameters:
                assumptions: assumptions/axioms of the proof.
                lines: lines of the proof.
                line_number: line number of the current line in the given lines.

            Returns:
                ``True`` if the formula justified by the current line is a
                (predicate-logic) tautology, ``False`` otherwise.
            """
            assert line_number < len(lines) and lines[line_number] is self
            # Task 9.9
            prop = self.formula.propositional_skeleton()
            prop_str = str(prop[0])
            new_prop = PropositionalFormula.parse(prop_str)
            result = is_propositional_tautology(new_prop)
            return result

    #: An immutable proof line.
    Line = Union[AssumptionLine, MPLine, UGLine, TautologyLine]
                 
    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof of ' + str(self.conclusion) + ' from assumptions/axioms:\n'
        for assumption in self.assumptions:
            r += '  '  + str(assumption) + '\n'
        r += 'Lines:\n'
        for i in range(len(self.lines)):
            r += ('%3d) ' % i) + str(self.lines[i]) + '\n'
        r += 'QED\n'
        return r
        
    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed
        conclusion from (instances of) its assumptions/axioms.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            conclusion from (instances of) its assumptions/axioms, ``False``
            otherwise.
        """
        if len(self.lines) == 0 or self.lines[-1].formula != self.conclusion:
            return False
        for line_number in range(len(self.lines)):
            if not self.lines[line_number].is_valid(self.assumptions,
                                                    self.lines, line_number):
                return False
        return True

from propositions.proofs import Proof as PropositionalProof, \
                                InferenceRule as PropositionalInferenceRule, \
                                SpecializationMap as \
                                PropositionalSpecializationMap
from propositions.axiomatic_systems import AXIOMATIC_SYSTEM as \
                                           PROPOSITIONAL_AXIOMATIC_SYSTEM, \
                                           MP, I0, I1, D, I2, N, NI, NN, R
from propositions.tautology import prove_tautology as \
                                   prove_propositional_tautology

# Schema equivalents of the propositional-logic axioms for implication and
# negation

#: Schema equivalent of the propositional-logic self implication axiom
#: `~propositions.axiomatic_systems.I0`.
I0_SCHEMA = Schema(Formula.parse('(P()->P())'), {'P'})
#: Schema equivalent of the propositional-logic implication introduction (right)
#: axiom `~propositions.axiomatic_systems.I1`.
I1_SCHEMA = Schema(Formula.parse('(Q()->(P()->Q()))'), {'P', 'Q'})
#: Schema equivalent of the propositional-logic self-distribution of implication
#: axiom `~propositions.axiomatic_systems.D`.
D_SCHEMA = Schema(Formula.parse(
    '((P()->(Q()->R()))->((P()->Q())->(P()->R())))'), {'P', 'Q', 'R'})
#: Schema equivalent of the propositional-logic implication introduction (left)
#: axiom `~propositions.axiomatic_systems.I2`.
I2_SCHEMA = Schema(Formula.parse('(~P()->(P()->Q()))'), {'P', 'Q'})
#: Schema equivalent of the propositional-logic converse contraposition axiom
#: `~propositions.axiomatic_systems.N`.
N_SCHEMA  = Schema(Formula.parse('((~Q()->~P())->(P()->Q()))'), {'P', 'Q'})
#: Schema equivalent of the propositional-logic negative-implication
#: introduction axiom `~propositions.axiomatic_systems.NI`.
NI_SCHEMA = Schema(Formula.parse('(P()->(~Q()->~(P()->Q())))'), {'P', 'Q'})
#: Schema equivalent of the propositional-logic double-negation introduction
#: axiom `~propositions.axiomatic_systems.NN`.
NN_SCHEMA = Schema(Formula.parse('(P()->~~P())'), {'P'})
#: Schema equivalent of the propositional-logic resolution axiom
#: `~propositions.axiomatic_systems.R`.
R_SCHEMA  = Schema(Formula.parse(
    '((Q()->P())->((~Q()->P())->P()))'), {'P', 'Q'})

#: Schema system equivalent of the axioms of the propositional-logic large
#: axiomatic system for implication and negation
#: `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMAS = {I0_SCHEMA, I1_SCHEMA, D_SCHEMA,
                                          I2_SCHEMA, N_SCHEMA, NI_SCHEMA,
                                          NN_SCHEMA, R_SCHEMA}

#: Mapping from propositional-logic axioms for implication and negation to their
#: schema equivalents.
PROPOSITIONAL_AXIOM_TO_SCHEMA = {
        I0: I0_SCHEMA, I1: I1_SCHEMA, D: D_SCHEMA, I2: I2_SCHEMA, N: N_SCHEMA,
        NI: NI_SCHEMA, NN: NN_SCHEMA, R: R_SCHEMA}

def _axiom_specialization_map_to_schema_instantiation_map(
        propositional_specialization_map: PropositionalSpecializationMap,
        substitution_map: Mapping[str, Formula]) -> Mapping[str, Formula]:
    """Composes the given propositional-logic specialization map, specifying the
    transformation from a propositional-logic axiom to a specialization of it,
    and the given substitution map, specifying the transformation from that
    specialization (as a propositional skeleton) to a predicate-logic formula,
    into an instantiation map specifying how to instantiate the schema
    equivalent of that axiom into the same predicate-logic formula.

    Parameters:
        propositional_specialization_map: mapping specifying how some
            propositional-logic axiom `axiom` (which is not specified) from
            `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM` specializes into
            some specialization `specialization` (which is also not specified),
            and containing no constants or operators beyond ``'~'``, ``'->'``,
            ``'|'``, and ``'&'``.
        substitution_map: mapping from each propositional variable name of
            `specialization` to a predicate-logic formula.

    Returns:
        An instantiation map for instantiating the schema equivalent of `axiom`
        into the predicate-logic formula obtained from its propositional
        skeleton `specialization` by the given substitution map.

    Examples:
        >>> _axiom_specialization_map_to_schema_instantiation_map(
        ...     {'p': PropositionalFormula.parse('(z1->z2)'),
        ...      'q': PropositionalFormula.parse('~z1')},
        ...     {'z1': Formula.parse('Ax[(x=5&M())]'),
        ...      'z2': Formula.parse('R(f(8,9))')})
        {'P': (Ax[(x=5&M())]->R(f(8,9))), 'Q': ~Ax[(x=5&M())]}
    """
    for variable in propositional_specialization_map:
        assert is_propositional_variable(variable)
        for operator in propositional_specialization_map[variable].operators():
            assert is_unary(operator) or is_binary(operator)
    for variable in substitution_map:
        assert is_propositional_variable(variable)
    # Task 9.11a
    new_dict = dict()
    for var in propositional_specialization_map:
        prop_form_str = str(propositional_specialization_map[var])
        for mapper in substitution_map:
            prop_form_str = prop_form_str.replace(mapper, str(substitution_map[mapper]))
        new_dict[var.upper()] = Formula.parse(prop_form_str)
    return new_dict

def _prove_from_skeleton_proof(formula: Formula,
                               skeleton_proof: PropositionalProof,
                               substitution_map: Mapping[str, Formula]) -> \
        Proof:
    """Translates the given proof of a propositional skeleton of the given
    predicate-logic formula into a proof of that predicate-logic formula.

    Parameters:
        formula: predicate-logic formula to prove.
        skeleton_proof: valid propositional-logic proof of a propositional
            skeleton of the given formula, from no assumptions and via
            `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`, and containing
            no constants or operators beyond ``'~'``, ``'->'``, ``'|'``, and
            ``'&'``.
        substitution_map: mapping from each propositional variable name of the
            propositional skeleton of the given formula that is proven in the
            given proof to the respective predicate-logic subformula of the
            given formula.

    Returns:
        A valid predicate-logic proof of the given formula from the axioms
        `PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMAS` via only assumption lines and
        MP lines.
    """
    assert len(skeleton_proof.statement.assumptions) == 0 and \
           skeleton_proof.rules.issubset(PROPOSITIONAL_AXIOMATIC_SYSTEM) and \
           skeleton_proof.is_valid()
    assert Formula.from_propositional_skeleton(
        skeleton_proof.statement.conclusion, substitution_map) == formula
    for line in skeleton_proof.lines:
        for operator in line.formula.operators():
            assert is_unary(operator) or is_binary(operator)
    # Task 9.11b
    assumptions = PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMAS
    conclusion = formula
    lines = []
    for line in skeleton_proof.lines:  # Only using MP / Assumptions
        if line.rule == MP:  # formula, antecedent_ln, conditional_ln
            cur_formula = Formula.from_propositional_skeleton(line.formula, substitution_map)
            antecedent_ln = line.assumptions[0]
            conditional_ln = line.assumptions[1]
            lines.append(Proof.MPLine(cur_formula, antecedent_ln, conditional_ln))
        else:  # formula, assumptions, inst_map
            pro_formula = line.formula
            axiom_inst_map = PropositionalInferenceRule._formula_specialization_map(line.rule.conclusion, pro_formula)
            cur_formula = Formula.from_propositional_skeleton(line.formula, substitution_map)
            schema_form = find_axiom(line.rule)
            # axiom_inst_map =
            inst_map = _axiom_specialization_map_to_schema_instantiation_map(axiom_inst_map, substitution_map)
            lines.append(Proof.AssumptionLine(cur_formula, schema_form, inst_map))
    proof = Proof(assumptions, conclusion, lines)
    return proof

def find_axiom(axiom_in_propositions):
    if axiom_in_propositions == D:
        return D_SCHEMA
    if axiom_in_propositions == I0:
        return I0_SCHEMA
    if axiom_in_propositions == I1:
        return I1_SCHEMA
    if axiom_in_propositions == I2:
        return I2_SCHEMA
    if axiom_in_propositions == N:
        return N_SCHEMA
    if axiom_in_propositions == NI:
        return NI_SCHEMA
    if axiom_in_propositions == NN:
        return NN_SCHEMA
    if axiom_in_propositions == R:
        return R_SCHEMA


def prove_tautology(tautology: Formula) -> Proof:
    """Proves the given predicate-logic tautology.

    Parameters:
        tautology: predicate-logic tautology, whose propositional skeleton
            contains no constants or operators beyond ``'->'`` and ``'~'``, to
            prove.

    Returns:
        A valid proof of the given predicate-logic tautology from the axioms
        `PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMAS` via only assumption lines
        and MP lines.
    """
    skeleton = tautology.propositional_skeleton()[0]
    assert is_propositional_tautology(skeleton)
    assert skeleton.operators().issubset({'->', '~'})
    # Task 9.12
    propositional_tautology, map_for_propositional_tautology = tautology.propositional_skeleton()
    prop_proof_of_tautology = propositional_prove_or_counter_exapmle(propositional_tautology)
    result = _prove_from_skeleton_proof(tautology, prop_proof_of_tautology, map_for_propositional_tautology)
    return result

