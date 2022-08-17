# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in Predicate Logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable name that is free in this assumption.
        print_as_proof_forms: flag specifying whether the proof of
            ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """        
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.1

    axioms = set()
    for axiom in proof.assumptions:
        if axiom.formula != assumption:
            axioms.add(axiom)
    prover = Prover(axioms, print_as_proof_forms)
    for line in proof.lines:
        get_lines(prover, proof, line, assumption)
    return prover.qed()

def get_lines(prover, proof, line, assumption):
    # first case: p, we need to make him p->p  ## p is cur_assumption
    if line.formula == assumption:
        return prover.add_tautology('({}->{})'.format(assumption, assumption))
    # second case: a, where a is assumption or AXIOM
    elif isinstance(line, Proof.AssumptionLine):
        step1 = prover.add_instantiated_assumption(line.formula, line.assumption, line.instantiation_map)
        step2 = prover.add_tautology('({}->({}->{}))'.format(line.formula, assumption, line.formula))
        step3 = prover.add_mp('({}->{})'.format(assumption, line.formula), step1, step2)
        return step3
    elif isinstance(line, Proof.MPLine):
        step1 = get_lines(prover, proof, proof.lines[line.antecedent_line_number], assumption)
        step2 = get_lines(prover, proof, proof.lines[line.conditional_line_number], assumption)
        temp_f1 = proof.lines[line.antecedent_line_number].formula   # a
        temp_f2 = proof.lines[line.conditional_line_number].formula  # a->b
        temp_f2_second = proof.lines[line.conditional_line_number].formula.second
        step3 = prover.add_tautology('(({}->{})->(({}->{})->({}->{})))'.format(assumption, temp_f2,
                                                                            assumption, temp_f1, assumption, temp_f2_second))
        step4 = prover.add_mp('(({}->{})->({}->{}))'.format(assumption, temp_f1, assumption, temp_f2_second), step2, step3)
        step5 = prover.add_mp('({}->{})'.format(assumption, temp_f2_second), step1, step4)
        return step5
    elif isinstance(line, Proof.TautologyLine):
        step1 = prover.add_tautology('({}->{})'.format(assumption, line.formula))
        return step1
    elif isinstance(line, Proof.UGLine):
        var = line.formula.variable
        step1 = get_lines(prover, proof, proof.lines[line.nonquantified_line_number], assumption)  # may can be omitted
        temp_f1 = proof.lines[line.nonquantified_line_number].formula
        step2 = prover.add_ug('A{}[({}->{})]'.format(var, assumption, temp_f1), step1)
        # step2 = prover.add_ug('A{}[{}]'.format(var, temp_f1), step1)
        Q_form = assumption.substitute({var: Term('_')})
        R_form = temp_f1.substitute({var: Term('_')})
        # R_form_for_prover = temp_f1.substitute({'x': Term(var)})
        step3_form = '(A{}[({}->{})]->({}->A{}[{}]))'.format(var, assumption, temp_f1, assumption, var, temp_f1)
        step3 = prover.add_instantiated_assumption(
            step3_form, prover.US,
            {'Q': assumption, 'R': R_form, 'x': str(var)})
        step4 = prover.add_mp('({}->A{}[{}])'.format(assumption, var, temp_f1), step2, step3)
        return step4



def prove_by_way_of_contradiction(proof: Proof, assumption: Formula) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable name that is free in this assumption.

    Returns:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2
    deducted_proof = remove_assumption(proof, assumption)
    updated_assumptions = {ass for ass in proof.assumptions if ass.formula != assumption}
    new_proof = Prover(updated_assumptions)
    for line in deducted_proof.lines:
        new_proof._add_line(line)
    step2 = new_proof.add_tautology('(({}->{})->((P()->P())->{}))'.format(
        str(assumption), str(proof.conclusion), str('~{}'.format(str(assumption)))))
    step3 = new_proof.add_mp('((P()->P())->{})'.
                             format(str('~{}'.format(str(assumption)))),
                             step2 - 1, step2)
    step4 = new_proof.add_tautology('(P()->P())')
    step5 = new_proof.add_mp(str('~{}'.format(str(assumption))), step4, step3)
    return new_proof.qed()
