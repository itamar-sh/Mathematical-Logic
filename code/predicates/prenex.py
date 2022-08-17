# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for Predicate Logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))

def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3a
    return 'Ax' not in str(formula) and 'Ay' not in str(formula) \
           and 'Az' not in str(formula) and 'Ez' not in str(formula) \
           and 'Ex' not in str(formula) and 'Ey' not in str(formula)

def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3b
    if is_quantifier_free(formula):
        return True
    if not is_quantifier(formula.root):
        return False
    return is_in_prenex_normal_form(formula.statement)

def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))

def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both bound and
        free occurrences or is quantified by more than one quantifier, ``True``
        otherwise.

    Examples:
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ey[R(y)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(y=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ay[R(y)]|Ez[R(z)]))'))
        True
    """
    forbidden_variables = set(formula.free_variables())
    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.statement)
        else:
            assert is_equality(formula.root) or is_relation(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)

def _uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = _uniquely_rename_quantified_variables(
        ...     formula)
        >>> returned_formula
        ~(w=x|Az58[(Ez17[(z17=z58&Az4[z4=z17])]->Az32[z32=y])])
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    # Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
    #                      '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
    #        {'x', 'y', 'R', 'Q'}),
    # Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
    #                      '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
    #        {'x', 'y', 'R', 'Q'})
    for variable in formula.variables():
        assert variable[0] != 'z'

    # Task 11.5
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    if is_quantifier(formula.root):
        # deal with inner formula
        statement_formula, statement_proof = _uniquely_rename_quantified_variables(formula.statement)
        new_var = next(fresh_variable_name_generator)
        new_statement_formula = statement_formula.substitute({formula.variable: Term(new_var)})
        new_formula = Formula.parse("{}{}[{}]".format(formula.root, new_var, new_statement_formula))
        step1 = prover.add_proof(statement_proof.conclusion, statement_proof)
        # unite eq
        eq_statement = statement_proof.lines[-1].formula
        eq_formula = equivalence_of(formula, new_formula)

        type_of_quntifier = 14
        if formula.root == "E":
            type_of_quntifier = 15
        cur_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[type_of_quntifier]
        final_eq = "({}->{}".format(eq_statement, eq_formula)
        R_form = formula.statement.substitute({formula.variable: Term('_')})
        Q_form = statement_formula.substitute({formula.variable: Term('_')})
        step2 = prover.add_instantiated_assumption(final_eq, cur_axiom,
             {'R': R_form,
              'Q': Q_form,
              'x': formula.variable,
              'y': new_var})
        step3 = prover.add_mp(eq_formula, step1, step2)
        return new_formula, prover.qed()

    elif is_unary(formula.root):
        # insert inner
        inner_formula, inner_proof = _uniquely_rename_quantified_variables(formula.first)
        inner_proof_line_number = prover.add_proof(inner_proof.conclusion, inner_proof)
        # add ~
        new_formula = Formula.parse("~" + str(inner_formula))
        prover.add_tautological_implication(equivalence_of(formula, new_formula), {inner_proof_line_number})
        return new_formula, prover.qed()

    elif is_binary(formula.root):
        # insert sides
        statement_formula_left, statement_prove_left = _uniquely_rename_quantified_variables(formula.first)
        left_line_number = prover.add_proof(equivalence_of(formula.first, statement_formula_left), statement_prove_left)
        statement_formula_right, statement_prove_right = _uniquely_rename_quantified_variables(formula.second)
        right_line_number = prover.add_proof(equivalence_of(formula.second, statement_formula_right),
                                             statement_prove_right)
        # unite sides
        new_formula = str(Formula(formula.root, statement_formula_left, statement_formula_right))
        a = prover.add_tautological_implication(equivalence_of(formula, Formula.parse(new_formula)),
                                                {left_line_number, right_line_number})
        return Formula.parse(new_formula), prover.qed()

    elif is_equality(formula.root):
        # everything is equivalence to itself
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    # double for debugging
    elif is_relation(formula.root):
        # everything is equivalence to itself
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()


def find_line(prover: Prover, formula: Formula) -> int:
    for line in range(len(prover._lines)):
        if prover._lines[line].formula == formula:
            return line


def _pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = _pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6
    proof = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    if is_quantifier(formula.first.root):
        var = formula.first.variable
        inner_formula = formula.first.statement
        new_r = inner_formula.substitute({var: Term('_')})
        if formula.first.root == 'A':
            cur_formula = Formula('E', var, Formula('~', inner_formula))
            next_line = equivalence_of(formula, cur_formula)
            first_step = proof.add_instantiated_assumption(
                next_line,
                ADDITIONAL_QUANTIFICATION_AXIOMS[0],
                {'x': var, 'R': new_r})
        if formula.first.root == 'E':
            cur_formula = Formula('A', var, Formula('~', inner_formula))
            first_step = proof.add_instantiated_assumption(
                equivalence_of(formula, cur_formula),
                ADDITIONAL_QUANTIFICATION_AXIOMS[1],
                {'x': var, 'R': new_r})
        if is_quantifier(formula.first.statement.root):
            inner_formula_before_change = Formula('~', formula.first.statement)
            inner_formula, inner_proof = _pull_out_quantifications_across_negation(
                inner_formula_before_change)
            proof.add_proof(inner_proof.conclusion, inner_proof)
            # remake the whole prove
            type_of_quntifier = 14
            char_of_quantifier = 'A'
            if cur_formula.root == "E":
                type_of_quntifier = 15
                char_of_quantifier = 'E'
            formula_before_change = Formula(char_of_quantifier, formula.first.variable,
                                                     inner_formula_before_change)
            formula_after_change = Formula(char_of_quantifier, formula.first.variable,
                                                     inner_formula)
            old_equivalence = equivalence_of(inner_formula_before_change, inner_formula)
            new_equivalence = equivalence_of(formula_before_change, formula_after_change)
            old_cause_new = '({}->{})'.format(old_equivalence, new_equivalence)
            R_inner_formula_before_change = inner_formula_before_change.substitute({var: Term('_')})
            Q_inner_formula = inner_formula.substitute({var: Term('_')})
            step1 = proof.add_instantiated_assumption(old_cause_new,
                                                      ADDITIONAL_QUANTIFICATION_AXIOMS[type_of_quntifier],
                                                      {'x': formula.first.variable, 'y': formula.first.variable,
                                                       'R': R_inner_formula_before_change,
                                                       'Q': Q_inner_formula})
            step2 = proof.add_mp(new_equivalence, step1-1, step1)
            first_equivalence = equivalence_of(formula, cur_formula)
            all_equivalence = equivalence_of(formula, formula_after_change)
            new_tautology = "(({}&{})->{})".format(new_equivalence, first_equivalence, all_equivalence)
            step3 = proof.add_tautology(new_tautology)
            step4 = proof.add_tautological_and(step2, first_step)
            step5 = proof.add_mp(all_equivalence, step4, step3)
            return formula_after_change, proof.qed()
        return cur_formula, proof.qed()
    else:
        proof.add_tautology(equivalence_of(formula, formula))
        return formula, proof.qed()

def _pull_out_quantifications_from_left_across_binary_operator(formula:
                                                               Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7a
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    if not is_quantifier(formula.first.root):  # Base case
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    else:
        formula_binary = formula.root
        quantifier = formula.first.root
        flipped_quantifier = 'E' if quantifier == 'A' else 'A'
        var = formula.first.variable
        fixed_quantifier = flipped_quantifier if formula_binary == '->' else quantifier
        left_inner = Formula(formula_binary, formula.first.statement, formula.second)
        inner_formula, inner_proof = \
            _pull_out_quantifications_from_left_across_binary_operator(left_inner)
        ug_form = Formula(fixed_quantifier, var, left_inner)
        result_formula = Formula(fixed_quantifier, var, inner_formula)
        step0 = prover.add_proof(inner_proof.conclusion, inner_proof)
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14] if fixed_quantifier == 'A' \
            else ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        step1 = prover.add_instantiated_assumption(
            Formula('->', inner_proof.conclusion,
                    equivalence_of(ug_form, result_formula)), axiom,
            {'R': left_inner.substitute({var: Term('_')}),
             'Q': inner_formula.substitute({var: Term('_')}),
             'x': var,
             'y': var})
        step2 = prover.add_mp(
            equivalence_of(ug_form, result_formula), step0, step1)
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[get_needed_axiom_for_left_binary(formula_binary, quantifier)]
        step3 = prover.add_instantiated_assumption(
            equivalence_of(formula, ug_form), axiom,
            {'x': var,
             'R': formula.first.statement.substitute({var: Term('_')}),
             'Q': formula.second})
        step_final = prover.add_tautological_implication(
            equivalence_of(formula, result_formula), {step2, step3})
        return result_formula, prover.qed()


def get_needed_axiom_for_left_binary(binary, quantifier):
    if quantifier == 'A':
        if binary == '&':
            return 2
        elif binary == '|':
            return 6
        elif binary == '->':
            return 10
    else:  # E
        if binary == '&':
            return 3
        elif binary == '|':
            return 7
        elif binary == '->':
            return 11
    
def _pull_out_quantifications_from_right_across_binary_operator(formula:
                                                                Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7b
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    if not is_quantifier(formula.second.root):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    else:
        formula_binary = formula.root
        quantifier = formula.second.root
        var = formula.second.variable
        right_inner = Formula(formula_binary, formula.first, formula.second.statement)
        inner_formula, inner_proof = _pull_out_quantifications_from_right_across_binary_operator(right_inner)
        result_formula = Formula(quantifier, var, inner_formula)
        ug_form = Formula(quantifier, var, right_inner)
        step0 = prover.add_proof(inner_proof.conclusion, inner_proof)
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14 if quantifier == 'A' else 15]
        step1 = prover.add_instantiated_assumption(
            Formula('->', inner_proof.conclusion, equivalence_of(ug_form, result_formula)),
            axiom,
            {'R': right_inner.substitute({var: Term('_')}),
             'Q': inner_formula.substitute({var: Term('_')}),
             'x': var, 'y': var})
        step2 = prover.add_mp(
            equivalence_of(ug_form, result_formula), step0, step1)
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[get_needed_axiom_for_right_binary(formula_binary, quantifier)]
        step3 = prover.add_instantiated_assumption(
            equivalence_of(formula, ug_form), axiom,
            {'x': var,
             'R': formula.second.statement.substitute({var: Term('_')}),
             'Q': formula.first})

        step_final = prover.add_tautological_implication(
            equivalence_of(formula, result_formula), {step2, step3})
        return result_formula, prover.qed()


def get_needed_axiom_for_right_binary(binary, quantifier):
    if quantifier == 'A':
        if binary == '&':
            return 4
        elif binary == '|':
            return 8
        elif binary == '->':
            return 12
    else:  # E
        if binary == '&':
            return 5
        elif binary == '|':
            return 9
        elif binary == '->':
            return 13

def _pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    left_inner_formula, left_inner_proof = _pull_out_quantifications_from_left_across_binary_operator(formula)
    step0 = prover.add_proof(left_inner_proof.conclusion, left_inner_proof)
    last_statement, quantifiers_list = quantifiers_finder(left_inner_formula)  # Helper function
    right_inner_formula, right_inner_proof = _pull_out_quantifications_from_right_across_binary_operator(last_statement)
    last_step = prover.add_proof(right_inner_proof.conclusion, right_inner_proof)
    for quantifier, var in reversed(quantifiers_list):
        last_formula = prover._lines[last_step].formula
        ug_last_statement = Formula(quantifier, var, last_statement)
        ug_right_inner = Formula(quantifier, var, right_inner_formula)
        new_step = prover.add_instantiated_assumption(
            Formula('->', last_formula, equivalence_of(ug_last_statement, ug_right_inner)),
            ADDITIONAL_QUANTIFICATION_AXIOMS[14 if quantifier == 'A' else 15],
            {'R': last_statement.substitute({var: Term('_')}),
             'Q': right_inner_formula.substitute({var: Term('_')}),
             'x': var, 'y': var})
        last_step = prover.add_mp(equivalence_of(ug_last_statement, ug_right_inner), last_step, new_step)
        last_statement = ug_last_statement
        right_inner_formula = ug_right_inner
    step_final = prover.add_tautological_implication(
        equivalence_of(formula, right_inner_formula), {step0, last_step})
    return right_inner_formula, prover.qed()


def quantifiers_finder(formula):
    if not is_quantifier(formula.root):
        return formula, []
    lst = [(formula.root, formula.variable)]
    statement = formula.statement
    while is_quantifier(statement.root):
        lst.append((statement.root, statement.variable))
        statement = statement.statement
    return statement, lst

def _to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = _to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    if is_binary(formula.root):
        quan_form, quan_proof = _pull_out_quantifications_across_binary_operator(formula)
        prover.add_proof(quan_proof.conclusion, quan_proof)
        first_form, first_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        step0 = prover.add_proof(first_proof.conclusion, first_proof)
        second_form, second_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.second)
        step1 = prover.add_proof(second_proof.conclusion, second_proof)
        fixed_form = Formula(formula.root, first_form, second_form)
        bin_form, bin_proof = _pull_out_quantifications_across_binary_operator(fixed_form)
        step2 = prover.add_proof(bin_proof.conclusion, bin_proof)

        both_conclusions = Formula('&', first_proof.conclusion, second_proof.conclusion)
        step3 = prover.add_tautological_and(step0, step1)  # Proves both_conclusions

        step4 = prover.add_tautology(Formula('->', both_conclusions, equivalence_of(formula, fixed_form)))

        step5 = prover.add_mp(equivalence_of(formula, fixed_form), step3, step4)
        step_final = prover.add_tautological_implication(equivalence_of(formula, bin_form), {step2, step5})
        return bin_form, prover.qed()

    if is_unary(formula.root):
        inner_form, inner_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        step0 = prover.add_proof(inner_proof.conclusion, inner_proof)
        neg_inner = Formula(formula.root, inner_form)

        neg_form, neg_proof = _pull_out_quantifications_across_negation(neg_inner)
        step1 = prover.add_proof(neg_proof.conclusion, neg_proof)

        step2 = prover.add_tautology(Formula('->', inner_proof.conclusion, equivalence_of(formula, neg_inner)))
        step3 = prover.add_mp(equivalence_of(formula, neg_inner), step0, step2)
        step_final = prover.add_tautological_implication(
            equivalence_of(formula, neg_form), {step3, step1})
        return neg_form, prover.qed()

    if is_quantifier(formula.root):
        var = formula.variable
        inner_form, inner_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.statement)
        step0 = prover.add_proof(inner_proof.conclusion, inner_proof)
        quan_inner = Formula(formula.root, formula.variable, inner_form)
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14 if formula.root == 'A' else 15]
        step1 = prover.add_instantiated_assumption(
            Formula('->', inner_proof.conclusion, equivalence_of(formula, quan_inner)), axiom,
            {'R': formula.statement.substitute({var: Term('_')}),
             'Q': inner_form.substitute({var: Term('_')}),
             'x': var, 'y': var})
        step_final = prover.add_mp(equivalence_of(formula, quan_inner), step0, step1)
        return quan_inner, prover.qed()

    else:
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = to_prenex_normal_form(formula)
        >>> returned_formula
        Ez58[Ez17[Az4[Ez32[~(w=x|((z17=z58&z4=z17)->z32=y))]]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 11.10
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    unique_formula, unique_proof = _uniquely_rename_quantified_variables(formula)
    step0 = prover.add_proof(unique_proof.conclusion, unique_proof)
    updated_formula, updated_proof = _to_prenex_normal_form_from_uniquely_named_variables(
        unique_formula)
    step1 = prover.add_proof(updated_proof.conclusion, updated_proof)
    step_final = prover.add_tautological_implication(
        equivalence_of(formula, updated_formula), {step0, step1})
    return updated_formula, prover.qed()
