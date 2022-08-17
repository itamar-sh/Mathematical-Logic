# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *


def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a
    new_asumptions = list()
    new_asumptions.append(antecedent_proof.statement.assumptions[0])
    new_statement = InferenceRule(new_asumptions, consequent)
    lines_of_proof = list()
    for line in antecedent_proof.lines:
        lines_of_proof.append(line)
    lines_of_proof.append(Proof.Line(Formula("->", antecedent_proof.statement.conclusion, consequent), conditional, []))
    lines_of_proof.append(Proof.Line(consequent, MP, [len(antecedent_proof.lines) - 1, len(antecedent_proof.lines)]))
    new_proof = Proof(new_statement, antecedent_proof.rules, lines_of_proof)
    return new_proof


def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulas `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `double_conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
                    Formula('->', antecedent2_proof.statement.conclusion, consequent))
    ).is_specialization_of(double_conditional)
    # Task 5.3b
    # assumptions and conclusion
    new_assumptions = list()
    for assumption in antecedent1_proof.statement.assumptions:
        if not (assumption in new_assumptions):
            new_assumptions.append(assumption)
    for assumption in antecedent2_proof.statement.assumptions:
        if not (assumption in new_assumptions):
            new_assumptions.append(assumption)
    new_statement = InferenceRule(new_assumptions, consequent)
    # lines for antecedent1_proof and first ->
    lines_of_proof = list()
    rule_len = 0
    for line in antecedent1_proof.lines:
        lines_of_proof.append(line)
        rule_len += 1
    inner_formula = Formula("->", antecedent2_proof.statement.conclusion, consequent)
    lines_of_proof.append(Proof.Line(Formula("->", antecedent1_proof.statement.conclusion, inner_formula),
                          double_conditional, []))
    rule_len += 2
    inner_segment_line_num = rule_len-1
    # lines for antecedent2_proof and second ->
    for line in antecedent2_proof.lines:
        if line.rule is None:
            lines_of_proof.append(line)
            rule_len += 1
            continue
        assumptions = list()
        for assumption in line.assumptions:
            assumptions.append(assumption+inner_segment_line_num)
        new_line = Proof.Line(line.formula, line.rule, assumptions)   # update the current line numbers in the assumptions of each line
        lines_of_proof.append(new_line)
        rule_len += 1
    lines_of_proof.append(Proof.Line(inner_formula,
                                     MP, [len(antecedent1_proof.lines) - 1, len(antecedent1_proof.lines)]))
    # lines_of_proof.append(Proof.Line(consequent, MP, [inner_segment_line_num, rule_len - 1]))
    lines_of_proof.append(Proof.Line(consequent, MP, [rule_len - 2, rule_len - 1]))
    # combine rules
    rules_of_proof = list()
    for rule in antecedent1_proof.rules:
        rules_of_proof.append(rule)
    for rule in antecedent2_proof.rules:
        rules_of_proof.append(rule)
    new_proof = Proof(new_statement, rules_of_proof, lines_of_proof)
    return new_proof


def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    # make new statement for the new proof
    new_assumptions = list()
    for i in range(len(proof.statement.assumptions)-1):
        new_assumptions.append(proof.statement.assumptions[i])
    cur_assumption = proof.statement.assumptions[len(proof.statement.assumptions)-1]  # the assumption to convert
    new_conclusion = Formula("->", cur_assumption, proof.statement.conclusion)
    new_statement = InferenceRule(new_assumptions, new_conclusion)
    # we make list of all axioms (made from inferencesRules) so we will able to check if var is axiom:
    list_of_axioms = list()
    for rule in proof.rules:
        if rule != MP:
            list_of_axioms.append(rule.conclusion)
    # find the removed assumption in the old proof, then dealt with him according to one of three cases
    new_lines = list()
    line_index = -1
    for line in proof.lines:
        # first case: p, we need to make him p->p  ## p is cur_assumption
        if line.formula == cur_assumption:
            new_lines.append(Proof.Line(Formula("->", cur_assumption, cur_assumption), I0, []))
            line_index += 1
            continue
        # second case: q, we need to make p->q  ## q is an assumption different from cur_assumption
        if line.rule != MP:
            is_assumption_or_simple_axiom = line.formula in new_assumptions or line.formula in list_of_axioms
            is_null = line.rule is None
            is_not_null = not is_null
            is_specified_axiom = is_not_null and line.rule in proof.rules
            if is_assumption_or_simple_axiom or is_specified_axiom:
                temp_formula1 = Formula("->", cur_assumption, line.formula)   # (p->q)
                temp_formula2 = Formula("->", line.formula, temp_formula1)    # q->(p->q)
                new_lines.append(line)    # q
                new_lines.append(Proof.Line(temp_formula2, I1, []))   # q->(p->q)
                new_lines.append(Proof.Line(temp_formula1, MP, [line_index+1, line_index+2]))
                line_index += 3
                continue
        # third case: w, we need to make p->w  ## w is not an assumption nor axiom
        # if we got to this case its mean that the last five lines were:
        # q                          line_index+1   -5
        # q->(p->q)                  line_index+2   -4
        # p->q                       line_index+3   -3
        # p->(q->w)                  line_index+4   -2
        # p->((q->w)->(p->(q->w)))   line_index+5   -1
        # p->(p->(q->w))             line_index+6   +0
        p_mp_index = line.assumptions[0]
        p_q_mp_index = line.assumptions[1]
        p_mp = proof.lines[p_mp_index].formula  # q
        p_q_mp = proof.lines[p_q_mp_index].formula  # q->w
        q_mp = p_q_mp.second   # w
        # we want to return p->(q->w). meaning: cur_assumption->(q->w)
        temp_formula1 = Formula("->", cur_assumption, q_mp)  # (p->w)
        temp_formula11 = Formula("->", cur_assumption, p_mp)  # (p->q)
        temp_formula2 = Formula("->", temp_formula11, temp_formula1)  # (p->q)->(p->w)
        temp_formula22 = Formula("->", cur_assumption, p_q_mp)  # p->(q->w)
        temp_formula3 = Formula("->", temp_formula22, temp_formula2)  # (p->(q->w))->((p->q)->(p->w))
        index_of_p_q_w = -1  # p->(q->w)
        index_of_p_q = -1   # p->q
        for i in range(len(new_lines)):
            if new_lines[i].formula == temp_formula22:
                index_of_p_q_w = i
            if new_lines[i].formula == temp_formula11:
                index_of_p_q = i
        new_lines.append(Proof.Line(temp_formula3, D, []))  # (p->(q->w))->((p->q)->(p->w))   line_index+1
        new_lines.append(Proof.Line(temp_formula2, MP, [index_of_p_q_w, line_index+1]))  # (p->q)->(p->w)   line_index+2
        new_lines.append(Proof.Line(temp_formula1, MP, [index_of_p_q, line_index+2]))  # (p->w)
        line_index += 3
    # we got the lines!!!
    # now we need to add to the rules the next four axioms {MP,I0,I1,D}
    new_set_rules = set()
    new_axioms = {MP, I0, I1, D}
    for rule in proof.rules:
        new_set_rules.add(rule)
    for rule in new_axioms:
        new_set_rules.add(rule)
    # now we need to just sum all the info and make a new proof
    new_proof = Proof(new_statement, new_set_rules, new_lines)
    return new_proof


def prove_from_opposites(proof_of_affirmation: Proof,
                         proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.
        conclusion: formula to prove.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6
    # combine statement
    new_assumptions = list()
    for assumption in proof_of_affirmation.statement.assumptions:
        if not (assumption in new_assumptions):
            new_assumptions.append(assumption)
    for assumption in proof_of_negation.statement.assumptions:
        if not (assumption in new_assumptions):
            new_assumptions.append(assumption)
    new_statement = InferenceRule(new_assumptions, conclusion)

    # adding lines
    new_lines = list()
    counter_lines = 0
    for line in proof_of_affirmation.lines:
        new_lines.append(line)
        counter_lines += 1
    p_index = counter_lines-1
    for line in proof_of_negation.lines:
        if line.rule is None:
            new_lines.append(line)
            counter_lines += 1
            continue
        temp_assumption = [x + p_index + 1 for x in line.assumptions]
        temp_line = Proof.Line(line.formula, line.rule, temp_assumption)
        new_lines.append(temp_line)
        counter_lines += 1
    not_p_index = counter_lines-1
    # combine_rules
    new_rules = set()
    for rule in proof_of_affirmation.rules:
        new_rules.add(rule)
    for rule in proof_of_negation.rules:
        new_rules.add(rule)
    new_rules.add(MP)
    new_rules.add(I2)
    # rules = {MP,  # InferenceRule([Formula.parse('p'), Formula.parse('(p->q)')], # Formula.parse('q'))
    #          I2}  # InferenceRule([], Formula.parse('(~p->(p->q))'))


    # now we use (~p->(p->q)) to find q
    temp_formula_pos = proof_of_affirmation.statement.conclusion
    temp_formula_neg = proof_of_negation.statement.conclusion
    temp_formula_1 = Formula("->", temp_formula_pos, conclusion)
    temp_formula_2 = Formula("->", temp_formula_neg, temp_formula_1)
    new_lines.append(Proof.Line(temp_formula_2, I2, []))  # (~p->(p->q))
    counter_lines += 1
    new_lines.append(Proof.Line(temp_formula_1, MP, [not_p_index, counter_lines - 1]))  # (p->q)
    counter_lines += 1
    new_lines.append(Proof.Line(conclusion, MP, [p_index, counter_lines - 1]))  # q

    # pack all the info
    new_proof = Proof(new_statement, new_rules, new_lines)
    return new_proof


def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
    # arrange the proof
    removed_assumption_proof = remove_assumption(proof)
    # make the lines to proof q after ~q was the removed assumption
    new_lines = list()
    for line in removed_assumption_proof.lines:
        new_lines.append(line)
    formula_not_q = removed_assumption_proof.statement.conclusion.first
    formula_q = formula_not_q.first
    # N = InferenceRule([], Formula.parse('((~q->~p)->(p->q))'))
    formula_for_n0 = Formula("->", formula_not_q, Formula('~', Formula.parse('(p->p)')))
    formula_for_n1 = Formula("->", formula_for_n0, Formula("->", Formula.parse('(p->p)'), formula_q))
    new_lines.append(Proof.Line(formula_for_n1, N, []))
    temp_formula = Formula("->", Formula.parse('(p->p)'), formula_q)  # (p->p)->q
    new_lines.append(Proof.Line(temp_formula, MP, [len(new_lines) - 2, len(new_lines) - 1]))  # (p->p)->q
    new_lines.append(Proof.Line(Formula.parse('(p->p)'), I0, []))
    new_lines.append(Proof.Line(formula_q, MP, [len(new_lines)-1, len(new_lines)-2]))  # q
    # pack the new info
    new_statement = InferenceRule(removed_assumption_proof.statement.assumptions, formula_q)
    new_rules = set()
    for rule in removed_assumption_proof.rules:
        new_rules.add(rule)
    new_rules.add(N)
    new_proof = Proof(new_statement, new_rules, new_lines)
    return new_proof
