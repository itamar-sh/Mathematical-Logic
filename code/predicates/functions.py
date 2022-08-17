# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: predicates/functions.py

"""Syntactic conversion of predicate-logic formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]


def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]


def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function interpretations, replacing each function interpretation with a
    canonically corresponding relation interpretation.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            interpretations in this model.

    Returns:
        A model obtained from the given model by replacing every function
        interpretation of a function name with a relation interpretation of the
        canonically corresponding relation name, such that the relation
        interpretation contains any tuple
        ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1` is the
        output of the function interpretation for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_interpretations:
        assert function_name_to_relation_name(function) not in \
               model.relation_interpretations
    # Task 8.1
    # init two dictionaries
    new_relation_interpretations = dict()
    for relation_interpretation_key in model.relation_interpretations.keys():
        new_relation_interpretations[relation_interpretation_key] = \
            model.relation_interpretations[relation_interpretation_key]
    # for each function - make new relation
    for function_interpretation_key in model.function_interpretations.keys():
        new_name = function_name_to_relation_name(function_interpretation_key)
        cur_map = model.function_interpretations[function_interpretation_key]
        new_tuples_sets = set()
        for values in cur_map.keys():
            new_tuples_sets.add(tuple(cur_map[values]) + values)
        new_relation_interpretations[new_name] = new_tuples_sets
    # unite all the info and make new model
    new_model = Model(model.universe, model.constant_interpretations,
                      new_relation_interpretations, dict())
    return new_model


def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function interpretations to a
    canonically corresponding model with interpretations for the given function
    names, having each new function interpretation replace a canonically
    corresponding relation interpretation.

    Parameters:
        model: model to convert, that contains no function interpretations.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has an interpretation in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    assert len(model.function_interpretations) == 0
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_interpretations
        assert function_name_to_relation_name(function) in \
               model.relation_interpretations
    # Task 8.2
    # for every relation check if he has to be converted
    new_functions = dict()
    new_relations = dict()
    for relation in model.relation_interpretations:
        function_name = relation_name_to_function_name(relation)
        if function_name in original_functions:  # if has to convert
            new_function = dict()
            relation_set = model.relation_interpretations[relation]
            # check for function
            if len(relation_set) != len(model.universe) ** (len(next(iter(relation_set))) - 1):
                return None
            for tup in relation_set:
                # check function consistency
                for arity in new_function:
                    if tup[1:] == arity:
                        return None
                # everything is ok
                new_function[tup[1:]] = tup[0]
            new_functions[function_name] = new_function
        else:
            new_relations[relation] = model.relation_interpretations[relation]
    new_model = Model(model.universe, model.constant_interpretations,
                      new_relations, new_functions)
    return new_model


def _compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and which
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        'y=f(x1...,xn)'
        where `y` is a new variable name obtained by calling
        `next(~logic_utils.fresh_variable_name_generator),
        f is a function name, and each of the `xi` is either a constant name
        or a variable name. If `xi` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable name of the
        last returned step evaluates in that model to the value of the given
        term.
    """
    assert is_function(term.root)
    for variable in term.variables():
        assert variable[0] != 'z'
    # Task 8.3
    formula_list = list()
    new_args = list()
    for arg in term.arguments:
        if is_function(arg.root):
            new_formule = _compile_term(arg)
            formula_list.extend(new_formule)
            new_var = formula_list[-1].arguments[0]  # takes the zi in "zi=x1"
            new_args.append(new_var)
        else:
            new_args.append(arg)
    reterm = Term(term.root, new_args)
    new_var = next(fresh_variable_name_generator)
    formula_list.append(Formula("=", [Term(new_var), reterm]))
    return formula_list


def _convert_func_to_relation(second, cur_func):
    new_terms = list()
    new_terms.append(second)
    for arg in cur_func.arguments:
        new_terms.append(arg)
    return Formula(function_name_to_relation_name(cur_func.root), new_terms)


def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function interpretations.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        replace_function_with_relations_in_model(model).
    """
    assert len({function_name_to_relation_name(function) for
                function, arity in formula.functions()}.intersection(
        {relation for relation, arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 8.4
    if is_equality(formula.root):
        # answer
        all_formulas = None
        all_variables = list()
        # first
        if is_function(formula.arguments[0].root):
            first_formulas = _compile_term(formula.arguments[0])
            first = first_formulas[-1].arguments[0]  # its a Term
            # & for all the formulas
            for i in range(len(first_formulas)):
                all_variables.append(first_formulas[i].arguments[0])
                cur_formula = _convert_func_to_relation(first_formulas[i].arguments[0],
                                                        first_formulas[i].arguments[1])
                if all_formulas is None:
                    all_formulas = cur_formula
                else:
                    all_formulas = Formula("&", all_formulas, cur_formula)
        else:
            first = formula.arguments[0]
        # second
        if is_function(formula.arguments[1].root):
            second_formulas = _compile_term(formula.arguments[1])
            second = second_formulas[-1].arguments[0]  # its a Term
            # & for all the formulas
            for i in range(len(second_formulas)):
                all_variables.append(second_formulas[i].arguments[0])
                cur_formula = _convert_func_to_relation(second_formulas[i].arguments[0],
                                                        second_formulas[i].arguments[1])
                if all_formulas is None:
                    all_formulas = cur_formula
                else:
                    all_formulas = Formula("&", all_formulas, cur_formula)
        else:
            second = formula.arguments[1]

        # change f(a)=b to z1=b
        basic_formula = Formula("=", [first, second])
        # add last formula
        if all_formulas is None:  # nothing to do
            return formula
        all_formulas = Formula("->", all_formulas, basic_formula)

        # add for every new zi "for all zi" . only two because we have only z1=z2 in worse case
        for var in all_variables:
            all_formulas = Formula("A", var.root, all_formulas)

        return all_formulas

    if is_relation(formula.root):
        all_formulas = None
        all_variables = list()
        final_rational_args = list()
        for cur_term in formula.arguments:
            if is_function(cur_term.root):
                cur_formulas = _compile_term(cur_term)
                z = cur_formulas[-1].arguments[0]  # its a Term
                # & for all the formulas
                for i in range(len(cur_formulas)):
                    all_variables.append(cur_formulas[i].arguments[0])
                    final_rational_args.append(cur_formulas[i].arguments[0])
                    cur_formula = _convert_func_to_relation(cur_formulas[i].arguments[0], cur_formulas[i].arguments[1])
                    if all_formulas is None:
                        all_formulas = cur_formula
                    else:
                        all_formulas = Formula("&", all_formulas, cur_formula)
            else:  # regular term
                final_rational_args.append(cur_term)
        # now we add all the results to our rational
        basic_formula = Formula(formula.root, final_rational_args)
        # add last formula
        if all_formulas is None:  # nothing to do
            return formula
        all_formulas = Formula("->", all_formulas, basic_formula)

        # add for every new zi "for all zi" . only two because we have only z1=z2 in worse case
        for var in all_variables:
            all_formulas = Formula("A", var.root, all_formulas)

        return all_formulas

    if is_quantifier(formula.root):
        new_formula = Formula(formula.root, formula.variable,
                              replace_functions_with_relations_in_formula(formula.statement))
        return new_formula

    if is_binary(formula.root):
        new_formula = Formula(formula.root, replace_functions_with_relations_in_formula(formula.first),
                              replace_functions_with_relations_in_formula(formula.second))
        return new_formula

    if is_unary(formula.root):
        new_formula = Formula(formula.root, replace_functions_with_relations_in_formula(formula.first))
        return new_formula

def replace_functions_with_relations_in_formulas(formulas:
AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function interpretations.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with interpretations for the functions
       names of the former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, which contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas hold in a model `model` if and only if the
           returned formulas hold in
           replace_functions_with_relations_in_model(model).
        2. The returned formulas hold in a model `model` if and only if
           replace_relations_with_functions_in_model(model, original_functions),
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function, arity in formula.functions()}
                           for formula in formulas]).intersection(
        set.union(*[{relation for relation, arity in
                     formula.relations()} for
                    formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'
    # Task 8.5
    fixed_formulas = set()
    for formula in formulas:
        fixed_formulas.add(
            replace_functions_with_relations_in_formula(formula))
        i = 0
        str_form = str(formula)
        while i < len(str_form):
            if is_function(str_form[i]):
                j = i
                while str_form[j] != ')':
                    if str_form[j] == '(':
                        open_p = j
                    j += 1
                func_name = function_name_to_relation_name(str_form[i:open_p])
                elems = str_form[open_p + 1:j]
                print(elems)
                first = Formula.parse('Ez[{}(z,x)])'.format(func_name))
                second = Formula('A', 'z1', Formula('A', 'z2', Formula(
                    '->',
                    Formula('&', Formula(func_name, [Term('z1'), Term('x')]), Formula(func_name, [Term('z2'), Term
                    ('x')])), Formula.parse('z1=z2'))))
                fixed_formula = Formula('&', first, second)
                i = j
                fixed_formulas.add(Formula('A', 'x', fixed_formula))
            i += 1
    return fixed_formulas



def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model of the returned formulas, the
       interpretation of the relation name ``'SAME'`` is reflexive,
       symmetric, and transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model of the returned formulas, the interpretation of this
       relation name respects the interpretation of the relation name
       ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation, arity in formula.relations()}
    # Task 8.6
    same_set = set()
    same_set.add(Formula.parse('Ax[SAME(x,x)]'))
    same_set.add(Formula.parse('Ax[Ay[(SAME(x,y)->SAME(y,x))]]'))
    same_set.add(Formula.parse('Ax[Ay[Az[((SAME(x,y)&SAME(y,z))->SAME(x,z))]]]'))
    for formula in formulas:
        all_relations = formula.relations()
        for relation in all_relations:
            test_to_parse = relation_to_equality(relation)
            same_set.add(Formula.parse(test_to_parse))
        same_set.add(eq_to_same_helper(formula))
    return same_set


def relation_to_equality(relation_tup):
    # we get a tup of str and int
    relation_name, arity_num = relation_tup
    result = ""
    prefix = ""
    left_branch = ""
    right_branch_x = "{}(".format(relation_name)
    right_branch_y = "{}(".format(relation_name)
    suffix = ""
    for i in range(1, arity_num+1):
        # prefix: Axi[
        prefix += "Ax{}[".format(i)
        prefix += "Ay{}[".format(i)
        # left branch SAME(x1,y1)&SAME(x2,y2)..
        if i == 1:
            left_branch = "SAME(x1,y1)"
        else:
            left_branch += "&SAME(x{},y{})".format(i, i)
        # right branch_x: R(x1,x2)
        if i == 1:
            right_branch_x += "x1"
            right_branch_y += "y1"
        else:
            right_branch_x += ",x{}".format(i)
            right_branch_y += ",y{}".format(i)
        # suffix ]
        suffix += "]]"
    right_branch_x += ")"
    right_branch_y += ")"
    # unite right branch
    right_branch = "({}->{})".format(right_branch_x, right_branch_y)

    # unite all
    result += prefix
    result += "(({})".format(left_branch)
    result += "->{})".format(right_branch)
    result += suffix

    return result


# Takes a formula and returns it with SAME and without any equality.
def eq_to_same_helper(formula: Formula) -> Formula:
    i = 0
    str_form = str(formula)
    prev_eq = 0
    new_form = ''
    while i < len(str_form):
        if str_form[i] == '=':
            eq = i
            k = i
            while not str_form[k].isalnum():
                k -= 1
            while not str_form[i].isalnum():
                i += 1
            first = str_form[k:eq]
            second = str_form[eq+1:i+1]
            new_form += str_form[:k] + 'SAME({},{})'.format(first, second)
            prev_eq = i+1
        i += 1
    new_form += str_form[prev_eq:]
    return Formula.parse(new_form)

def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds an interpretation of the relation name ``'SAME'`` in the given
    model, that canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no interpretation of the relation name
            ``'SAME'``, to add the interpretation to.

    Returns:
        A model obtained from the given model by adding an interpretation of the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_interpretations
    # Task 8.7
    all_relations = dict()
    for relation in model.relation_interpretations:
        all_relations[relation] = model.relation_interpretations[relation]
    same_set = set()
    for omega in model.universe:
        same_set.add((omega, omega))
    all_relations['SAME'] = same_set
    return Model(model.universe, model.constant_interpretations, all_relations,
                 model.function_interpretations)


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    interpretation of ``'SAME'`` in the given model, in the sense that any set
    of formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function interpretations, and
            contains an interpretation of the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the
            interpretations of all other relation names.

    Returns:
        A model that is a model of any set `formulas` if and only if the given
        model is a model of
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        interpretation of ``'SAME'`` in the given model.
    """
    assert 'SAME' in model.relation_interpretations and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_interpretations) == 0
    # Task 8.8
    new_universe = set()
    same_numbers = dict()
    for elem in model.universe:
        new_universe.add(elem)
    same_model = model.relation_interpretations['SAME']
    for tup in same_model:
        if tup[0] != tup[1]:
            same_numbers[tup[0]] = tup[1]
            same_numbers[tup[1]] = tup[0]
            if tup[1] in new_universe and tup[0] in new_universe:
                new_universe.remove(tup[0])
    new_relations = dict()
    for relation in model.relation_interpretations:
        if relation == "SAME":
            continue
        new_rel = set()
        for tup in model.relation_interpretations[relation]:
            flag = True
            for elem in tup:
                if elem not in new_universe:
                    flag = False
            if flag:
                new_rel.add(tup)
        new_relations[relation] = new_rel
    new_constant = dict()
    for key in model.constant_interpretations:
        if model.constant_interpretations[key] in new_universe:
            new_constant[key] = model.constant_interpretations[key]
        else:
            new_constant[key] = same_numbers[model.constant_interpretations[key]]

    new_model = Model(new_universe, new_constant, new_relations, dict())
    return new_model


