# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5

    formula_p = Formula("p")
    formula_q = Formula("q")
    formula_not_p = Formula("~", formula_p)  # basic
    formula_not_q = Formula("~", formula_q)
    formula_p_and_q = Formula("&", formula_p, formula_q)
    formula_p_and_not_q = Formula("&", formula_p, formula_not_q)  # inside the or
    formula_not_p_and_q = Formula("&", formula_not_p, formula_q)
    formula_not_p_and_not_q = Formula("&", formula_not_p, formula_not_q)

    new_dict = {}
    formula_or_1 = Formula("|", formula_not_p_and_not_q, formula_not_p_and_q)
    new_dict["->"] = Formula("|", formula_or_1, formula_p_and_q)  # ->
    new_dict["-&"] = Formula("|", formula_or_1, formula_p_and_not_q)  # Nand, -&
    new_dict["<->"] = Formula("|", formula_not_p_and_not_q, formula_p_and_q)  # <-> iff
    new_dict["-|"] = formula_not_p_and_not_q  # -| Nor
    new_dict["+"] = Formula("|", formula_not_p_and_q, formula_p_and_not_q)  # + Xor
    new_dict["T"] = Formula("|", formula_p, formula_not_p)
    new_dict["F"] = Formula("&", formula_p, formula_not_p)

    return formula.substitute_operators(new_dict)



def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    formula_3_parts = to_not_and_or(formula)
    new_dict = {"|": Formula("~", Formula("&", Formula("~", Formula("p")), Formula("~", Formula("q"))))}
    new_formula = formula_3_parts.substitute_operators(new_dict)
    return new_formula

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    formula_2_parts = to_not_and(formula)
    formula_2_p = Formula("-&", Formula("p"), Formula("p"))
    formula_p_q = Formula("-&", Formula("p"), Formula("q"))
    new_dict = {"~": formula_2_p, "&": Formula("-&", formula_p_q, formula_p_q)}
    new_formula = formula_2_parts.substitute_operators(new_dict)
    return new_formula

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    formula_1_part = to_nand(formula)
    new_dict = {"-&": Formula("->", Formula("p"), Formula("~", Formula("q")))}
    new_formula = formula_1_part.substitute_operators(new_dict)
    return new_formula


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    formula_1_part = to_nand(formula)
    new_dict = {"-&": Formula("->", Formula("p"), Formula("->", Formula("q"), Formula("F")))}
    new_formula = formula_1_part.substitute_operators(new_dict)
    return new_formula
