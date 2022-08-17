# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Sequence, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *

def formulas_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulas that capture the given model: ``'``\ `x`\ ``'``
    for each variable name `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable name `x` that is assigned
    the value ``False``.

    Parameters:
        model: model to construct the formulas for.

    Returns:
        A list of the constructed formulas, ordered alphabetically by variable
        name.

    Examples:
        >>> formulas_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    # Task 6.1a
    list_of_vars = list()
    new_model = sorted(model)
    for key in new_model:
        if model[key]:
            list_of_vars.append(Formula(key))
        else:
            list_of_vars.append(Formula('~', Formula(key)))
    return list_of_vars


def extract_proof_lines(proof):  # helper
    new_lines = list()
    for line in proof.lines:
        new_lines.append(line)
    return new_lines


def update_proof_lines_numbers(lines, num):  # helper
    new_lines = list()
    for line in lines:
        if not(line.rule is None):
            temp_formula = line.formula
            temp_rule = line.rule
            temp_assumptions = list()
            for assumption in line.assumptions:
                temp_assumptions.append(assumption + num)
            new_lines.append(Proof.Line(temp_formula, temp_rule, temp_assumptions))
        else:
            new_lines.append(line)
    return new_lines


def prove_in_model(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If `formula` evaluates to ``True`` in the given model, then a valid
        proof of `formula`; otherwise a valid proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulas that capture the given model, in
        the order returned by `formulas_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p->q7)
        >>> proof.statement.assumptions
        (~p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p->q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    # Task 6.1b
    # find what we want to prove
    formula_bool = evaluate(formula, model)
    if formula.root == "->":   # if p->q formula
        if formula_bool:   # if p->q is true
            p_bool = evaluate(formula.first, model)
            if not p_bool:  # p is false - case I.  we will find ~q and use I2
                not_p_proof = prove_in_model(formula.first, model)  # ~p proof
                # make new proof
                # lines
                new_lines = extract_proof_lines(not_p_proof)
                formula_for_i2_left = Formula("~", formula.first)
                formula_for_i2 = Formula("->", formula_for_i2_left, formula)  # ~p->(p->q)
                new_lines.append(Proof.Line(formula_for_i2, I2, []))
                new_lines.append(Proof.Line(formula, MP, [len(new_lines) - 2, len(new_lines) - 1]))
                # rules = AXIOMATIC_SYSTEM_FULL
                # statement = formulas_capturing_model(model)=>formula
                new_statement = InferenceRule(formulas_capturing_model(model), formula)
                new_proof = Proof(new_statement, AXIOMATIC_SYSTEM, new_lines)

            else:   # if p is true case II. q must be also true so we prove q and use I1
                q_proof = prove_in_model(formula.second, model)  # q proof
                # make new proof
                # lines
                new_lines = extract_proof_lines(q_proof)
                formula_for_i1 = Formula("->", formula.second, formula)  # q->(p->q)
                new_lines.append(Proof.Line(formula_for_i1, I1, []))
                new_lines.append(Proof.Line(formula, MP, [len(new_lines) - 2, len(new_lines) - 1]))
                # rules = AXIOMATIC_SYSTEM_FULL
                # statement = formulas_capturing_model(model)=>formula
                new_statement = InferenceRule(formulas_capturing_model(model), formula)
                new_proof = Proof(new_statement, AXIOMATIC_SYSTEM, new_lines)

        else:   # if p->q is false
            # this case p is true and q is false. we prove that and use NI to prove ~(p->q)
            p_proof = prove_in_model(formula.first, model)  # p proof
            not_q_proof = prove_in_model(formula.second, model)  # ~q proof
            # make new proof
            # lines
            new_lines = list()
            new_lines1 = extract_proof_lines(p_proof)
            new_lines2 = update_proof_lines_numbers(extract_proof_lines(not_q_proof), len(new_lines1))
            new_lines.extend(new_lines1)
            new_lines.extend(new_lines2)
            formula_for_ni_right0 = Formula("~", formula)  # ~(p->q)
            formula_for_ni_right1 = Formula("->", Formula("~", formula.second), formula_for_ni_right0)  # ~q->~(p->q)
            formula_for_ni = Formula("->", formula.first, formula_for_ni_right1)  # p->(~q->~(p->q))
            new_lines.append(Proof.Line(formula_for_ni, NI, []))
            # ~q->~(p->q)
            new_lines.append(Proof.Line(formula_for_ni_right1, MP, [len(new_lines1) - 1, len(new_lines) - 1]))
            # ~(p->q)
            new_lines.append(Proof.Line(formula_for_ni_right0, MP, [len(new_lines1) + len(new_lines2) - 1, len(new_lines) - 1]))
            # rules = AXIOMATIC_SYSTEM
            # statement = formulas_capturing_model(model)=>formula
            new_statement = InferenceRule(formulas_capturing_model(model), formula_for_ni_right0)
            new_proof = Proof(new_statement, AXIOMATIC_SYSTEM, new_lines)

    else:  # not p->q formula. so we get or p or ~p
        if formula.root == "~":
            if evaluate(formula, model):  # ~p is true, so p is false. so we simply write it like that
                return prove_in_model(formula.first, model)
            else:  # ~p is false, so want to prove ~~p. we will prove p and use NN.
                p_proof = prove_in_model(formula.first, model)  # p proof
                new_lines = extract_proof_lines(p_proof)
                formula_for_nn_right = Formula("~", formula)  # ~~p
                formula_for_nn = Formula("->", formula.first, formula_for_nn_right)
                new_lines.append(Proof.Line(formula_for_nn, NN, []))  # p->~~p
                new_lines.append(Proof.Line(formula_for_nn_right, MP, [len(new_lines) - 2, len(new_lines) - 1]))
                new_statement = InferenceRule(formulas_capturing_model(model), formula_for_nn_right)
                new_proof = Proof(new_statement, AXIOMATIC_SYSTEM, new_lines)
        else:  # only p
            if evaluate(formula, model):
                new_lines = [Proof.Line(formula)]
                new_statement = InferenceRule(formulas_capturing_model(model), formula)
                new_proof = Proof(new_statement, AXIOMATIC_SYSTEM, new_lines)
            else:
                new_lines = [Proof.Line(Formula("~", formula))]
                new_statement = InferenceRule(formulas_capturing_model(model), Formula("~", formula))
                new_proof = Proof(new_statement, AXIOMATIC_SYSTEM, new_lines)
    return new_proof




def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the two given proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_from_negation: valid proof of `conclusion` from the same
            assumptions and inference rules of `proof_from_affirmation`, but
            with the last assumption being ``'~``\ `assumption`\ ``'`` instead
            of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If `proof_from_affirmation` is of ``['p', '~q', 'r'] ==> '(p&(r|~r))'``,
        then `proof_from_negation` must be of
        ``['p', '~q', '~r'] ==> '(p&(r|~r))'`` and the returned proof is of
        ``['p', '~q'] ==> '(p&(r|~r))'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2
    pos_proof = remove_assumption(proof_from_affirmation)
    neg_proof = remove_assumption(proof_from_negation)
    r_formula_right = Formula("->", neg_proof.statement.conclusion, neg_proof.statement.conclusion.second)
    r_formula = Formula("->", pos_proof.statement.conclusion, r_formula_right)
    r_line = Proof.Line(r_formula, R, [])  # (p->q)->((~p->q)->q)
    # ((~p->q)->q)
    mp1_line = Proof.Line(r_formula_right, MP, [len(pos_proof.lines)-1, len(pos_proof.lines)+len(neg_proof.lines)])
    mp2_line = Proof.Line(neg_proof.statement.conclusion.second, MP, [len(pos_proof.lines)+len(neg_proof.lines)-1,
                                                                      len(pos_proof.lines)+len(neg_proof.lines)+1])
    # statement
    new_statement = InferenceRule(pos_proof.statement.assumptions, neg_proof.statement.conclusion.second)
    # lines
    new_lines = extract_proof_lines(pos_proof)
    lines_neg = extract_proof_lines(neg_proof)
    lines_neg = update_proof_lines_numbers(lines_neg, len(new_lines))
    new_lines.extend(lines_neg)
    new_lines.append(r_line)
    new_lines.append(mp1_line)
    new_lines.append(mp2_line)
    # proof
    new_proof = Proof(new_statement, pos_proof.rules, new_lines)
    return new_proof


def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulas that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variable names of `tautology`, from whose
            formulas to prove.

    Returns:
        A valid proof of the given tautology from the formulas that capture the
        given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'),
        ...                         {'p': True, 'q': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        (p, ~q)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'))
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        ()
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a
    list_of_missed_vars = list()
    for var in tautology.variables():
        if not (var in model.keys()):
            list_of_missed_vars.append(var)
    list_of_missed_vars = sorted(list_of_missed_vars)
    # base case
    if len(list_of_missed_vars) == 0:
        return prove_in_model(tautology, model)
    # now we want to recursively reduce every var in list_of_missed_vars
    # get inside the recursion
    model_plus_pos_var = add_var_to_model(model, list_of_missed_vars[0], True)
    model_plus_neg_var = add_var_to_model(model, list_of_missed_vars[0], False)
    pos_branch_prove = prove_tautology(tautology, model_plus_pos_var)
    neg_branch_prove = prove_tautology(tautology, model_plus_neg_var)
    # merge the branches of the recursion
    # pos_reduced_proof = remove_assumption(pos_branch_prove)  # change the proof so the assumption conclude the proof
    # neg_reduced_proof = remove_assumption(neg_branch_prove)  # change the proof so the assumption conclude the proof
    reduced_proof = reduce_assumption(pos_branch_prove, neg_branch_prove)  # without the last assumption
    return reduced_proof


def add_var_to_model(model: Model, new_var: str, new_value: bool) -> Model:
    new_dict = dict()
    for key in model.keys():
        new_dict[key] = model[key]
    new_dict[new_var] = new_value
    return new_dict


def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    # Task 6.3b
    set_of_vars = formula.variables()  # set contains the vars
    if len(set_of_vars) == 0:
        return evaluate(formula, {})  # empty set because there isn't vars
    all_options = all_models(set_of_vars)  # list of models
    for option in all_options:
        if not evaluate(formula, option):
            return option
    return prove_tautology(formula, {})


def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))

        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a
    cur_formula = rule.conclusion
    reversed_assumptions = reversed(rule.assumptions)
    for assumption in reversed_assumptions:
        cur_formula = Formula("->", assumption, cur_formula)
    return cur_formula

def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion contain no
            constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in {rule.conclusion}.union(rule.assumptions):
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b
    rule_to_formula = encode_as_formula(rule)
    new_proof = prove_tautology(rule_to_formula, {})
    # again, we want to divide and conquer the proof:
    new_lines = extract_proof_lines(new_proof)
    index_of_tautology_proof_lines = len(new_lines)-1
    temp_formula = new_proof.statement.conclusion
    for assumption in rule.assumptions:
        new_lines.append(Proof.Line(temp_formula.first))
        # new_lines.append(Proof.Line(temp_formula.second, MP, [len(new_lines)-1, index_of_tautology_proof_lines]))
        new_lines.append(Proof.Line(temp_formula.second, MP, [len(new_lines) - 1, len(new_lines) - 2]))
        temp_formula = temp_formula.second
    new_proof = Proof(rule, new_proof.rules, new_lines)
    return new_proof

def model_or_inconsistency(formulas: Sequence[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulas hold, or proves
    ``'~(p->p)'`` from these formulas.

    Parameters:
        formulas: formulas that use only the operators ``'->'`` and ``'~'``, to
            either find a model of, or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulas hold if such exists,
        otherwise a valid proof of ``'~(p->p)'`` from the given formulas via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulas:
        assert formula.operators().issubset({'->', '~'})
    # Task 6.5
    set_of_vars = set()
    for formula in formulas:
        set_of_vars.update(formula.variables())  # set contains the vars
    all_options = all_models(set_of_vars)  # list of models
    for option in all_options:
        formulas_hold = True
        for formula in formulas:
            if not evaluate(formula, option):
                formulas_hold = False
        if formulas_hold:
            return option
    new_inference_rule = InferenceRule(formulas, Formula.parse('~(p->p)'))
    new_proof = prove_sound_inference(new_inference_rule)
    return new_proof


def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'`` (and may contain constants), whose affirmation
            or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If `formula` evaluates to ``True`` in the given model, then a valid
        proof of `formula`; otherwise a valid proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulas that capture the given model, in
        the order returned by `formulas_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.

    Examples:
        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': True, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p&q7)
        >>> proof.statement.assumptions
        (p, q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True

        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p&q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
