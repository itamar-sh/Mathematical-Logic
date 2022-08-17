# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""
from itertools import permutations, combinations_with_replacement, product
from typing import AbstractSet, Iterable, Iterator, Mapping, Sequence, Tuple

from propositions.syntax import *
from propositions.proofs import *

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]

def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variable
    names.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variable
        names, ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variable names over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variable names over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()

def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variable names of the
            given formula, to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1
    if is_variable(formula.root):
        return model[formula.root]

    if is_constant(formula.root):
        return formula.root == 'T'

    if is_unary(formula.root):
        return not evaluate(formula.first, model)

    if is_binary(formula.root):
        if formula.root == "&":
            return evaluate(formula.first, model) and evaluate(formula.second, model)
        if formula.root == "|":
            return evaluate(formula.first, model) or evaluate(formula.second, model)
        if formula.root == "->":
            return not evaluate(formula.first, model) or evaluate(formula.second, model)
        if formula.root == "+":  # Xor
            return (evaluate(formula.first, model) and not evaluate(formula.second, model)) or \
                   (not evaluate(formula.first, model) and evaluate(formula.second, model))
        if formula.root == "<->":  # if and only if (iff)
            return evaluate(formula.first, model) == evaluate(formula.second, model)
        if formula.root == "-&":  # Nand
            return not (evaluate(formula.first, model) and evaluate(formula.second, model))
        if formula.root == "-|":  # Nor
            return not (evaluate(formula.first, model) or evaluate(formula.second, model))

def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variable names.

    Parameters:
        variables: variable names over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variable names. The
        order of the models is lexicographic according to the order of the given
        variable names, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]

        >>> list(all_models(['q', 'p']))
        [{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True, 'p': False}, {'q': True, 'p': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2
    list_of_models = []

    all_options = product([False, True], repeat=len(variables))    #all_options = product([False, True], len(variables))
    for permutation in all_options:
        cur_model = {}
        i = 0
        for v in variables:
            cur_model[v] = permutation[i]
            i = i+1
        list_of_models.append(cur_model)
    return list_of_models









def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    models.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.

    Examples:
        >>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 'q76'])))
        [True, True, True, False]
    """
    # Task 2.3
    list_of_bools = []
    for model in models:
        list_of_bools.append(evaluate(formula, model))
    return list_of_bools

def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4
    def bool_to_str(var: bool) -> str:
        if var:
            return "T"
        return "F"
    set_of_vars = sorted(formula.variables())  # set contains the vars
    if len(set_of_vars) == 0:
        return
    all_options = all_models(set_of_vars)  # list of models
    # init two lines
    first_line = "| "
    second_line = "|-"
    for v in set_of_vars:  # print every var
        first_line += v + " | "
        second_line += len(v)*"-" + "-|-"
    first_line += str(formula) + " |"
    second_line += len(str(formula))*"-" + "-|"
    print(first_line)
    print(second_line)
    # print the others lines
    for option in all_options:
        cur_line = "| "  # start new line
        for v in set_of_vars:
            cur_line += bool_to_str(option[v]) + " "*(len(v)-1) + " | "
        print(cur_line + bool_to_str(evaluate(formula, option)) + (len(str(formula))-1)*" " + " |")


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a
    set_of_vars = formula.variables()  # set contains the vars
    if len(set_of_vars) == 0:
        return evaluate(formula, {})  # empty set because there isn't vars
    all_options = all_models(set_of_vars)  # list of models
    for option in all_options:
        if not evaluate(formula, option):
            return False
    return True



def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    set_of_vars = formula.variables()  # set contains the vars
    if len(set_of_vars) == 0:
        return not evaluate(formula, {})  # empty set because there isn't vars
    all_options = all_models(set_of_vars)  # list of models
    for option in all_options:
        if evaluate(formula, option):
            return False
    return True

def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c
    return not is_contradiction(formula)

def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Task 2.6

    def _make_var_to_formula(var: str) -> Formula:   # Help function: make single var to relevant formula
        if model[var]:
            return Formula(var)
        return Formula("~", Formula(var))
    first_key = list(model.keys())[0]  # the first var in the formula

    formula = _make_var_to_formula(first_key)   # get a one formula to begin with

    for key in model.keys():  # main loop - nested Formulas
        if key != first_key:
            formula = Formula("&", _make_var_to_formula(key), formula)
    return formula

def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7

    there_is_true  = False  # check for any T in the truth table
    for v in values:
        if v:
            there_is_true = True
    if not there_is_true:
        return Formula("&", Formula("~", Formula(variables[0])), Formula(variables[0]))

    all_options = all_models(variables)  # init the models
    iter_values = iter(values)  # init a iterator to know which row we want (those with T)
    first_time = True
    formula = Formula(variables[0])  # should be overwritten inside the loop.
    for option in all_options:
        if not iter_values.__next__():
            continue
        if first_time:
            formula = _synthesize_for_model(option)
            first_time = False
            continue
        else:
            formula = Formula("|", _synthesize_for_model(option), formula)
    return formula



def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to not hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Optional Task 2.8

def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in CNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Optional Task 2.9

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    # Task 4.2
    if evaluate(rule.conclusion, model):
        conclusion = True
    else:
        conclusion = False

    assumptions = True
    for assumption in rule.assumptions:
        if not evaluate(assumption, model):
            assumptions = False

    if assumptions and not conclusion:  # check if assumptions => conclusion
        return False
    return True

def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
    all_options = all_models(rule.variables())
    sound = True
    for model in all_options:
        if not evaluate_inference(rule, model):
            sound = False
    return sound
