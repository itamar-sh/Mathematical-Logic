# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: propositions/some_proofs.py

"""Some proofs in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *

# Some inference rules that only use conjunction.

#: Conjunction introduction inference rule
A_RULE = InferenceRule([Formula.parse('x'), Formula.parse('y')],
                       Formula.parse('(x&y)'))
#: Conjunction elimination (right) inference rule
AE1_RULE = InferenceRule([Formula.parse('(x&y)')], Formula.parse('y'))
#: Conjunction elimination (left) inference rule
AE2_RULE = InferenceRule([Formula.parse('(x&y)')], Formula.parse('x'))

def prove_and_commutativity() -> Proof:
    """Proves ``'(q&p)'`` from ``'(p&q)'`` via `A_RULE`, `AE1_RULE`, and
    `AE2_RULE`.

    Returns:
        A valid proof of ``'(q&p)'`` from the single assumption ``'(p&q)'`` via
        the inference rules `A_RULE`, `AE1_RULE`, and `AE2_RULE`.
    """
    # Task 4.7
    lemma = InferenceRule([Formula.parse('(p&q)')], Formula.parse('(q&p)'))
    rules = {A_RULE, AE1_RULE, AE2_RULE}
    lines = [Proof.Line(Formula.parse('(p&q)')),
             Proof.Line(Formula.parse('p'), AE2_RULE, [0]),
             Proof.Line(Formula.parse('q'), AE1_RULE, [0]),
             Proof.Line(Formula.parse('(q&p)'), A_RULE, [2, 1])]
    return Proof(lemma, rules, lines)

# : Modus ponens / implication elimination
# MP = InferenceRule([Formula.parse('p'), Formula.parse('(p->q)')],
#                    Formula.parse('q'))
# : Self implication
# I0 = InferenceRule([], Formula.parse('(p->p)'))
# : Implication introduction (right)
# I1 = InferenceRule([], Formula.parse('(q->(p->q))'))
# : Self-distribution of implication
# D = InferenceRule([], Formula.parse('((p->(q->r))->((p->q)->(p->r)))'))

def prove_I0() -> Proof:
    """Proves `~propositions.axiomatic_systems.I0` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I0` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    # Task 4.8

    lemma = I0    # InferenceRule([], Formula.parse('(p->p)'))
    rules = {MP,  # InferenceRule([Formula.parse('p'), Formula.parse('(p->q)')],
             # Formula.parse('q'))
             I1,  # InferenceRule([], Formula.parse('(q->(p->q))'))
             D}   # InferenceRule([], Formula.parse('((p->(q->r))->((p->q)->(p->r)))'))
    lines = [
             # [] - > '((p->(q->r))->((p->q)->(p->r)))'  p=p, q=(p->p), r=p   ==> '((p->((p->p)->p))->((p->(p->(p->p)))->(p->p)))'
             Proof.Line(Formula.parse('((p->((p->p)->p))->((p->(p->p))->(p->p)))'), D, []),
             # [] - > '(q->(p->q))'  p=(p->p), q=p   ==> '(p->((p->p)->p))'
             Proof.Line(Formula.parse('(p->((p->p)->p))'), I1, []),
             # ['q', '(p->q)']->['(p->p)']   q=(p->((p->p)->p)), q=p   => '(p->p)'
             Proof.Line(Formula.parse('((p->(p->p))->(p->p))'), MP, [1, 0]),
             Proof.Line(Formula.parse('(p->(p->p))'), I1, []),
             Proof.Line(Formula.parse('(p->p)'), MP, [3, 2])]
    return Proof(lemma, rules, lines)

#: Hypothetical syllogism
HS = InferenceRule([Formula.parse('(p->q)'), Formula.parse('(q->r)')],
                   Formula.parse('(p->r)'))

def prove_hypothetical_syllogism() -> Proof:
    """Proves `HS` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `HS` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    # Task 5.5
    rules = {MP,  # InferenceRule([Formula.parse('p'), Formula.parse('(p->q)')],
             # Formula.parse('q'))
             I1,  # InferenceRule([], Formula.parse('(q->(p->q))'))
             I0,  # InferenceRule([], Formula.parse('(p->p)'))
             D}   # InferenceRule([], Formula.parse('((p->(q->r))->((p->q)->(p->r)))'))
    statement = InferenceRule([Formula.parse('(p->q)'), Formula.parse('(q->r)'), Formula.parse('p')], Formula.parse('r'))
    lines = [
        Proof.Line(Formula.parse('p')),
        Proof.Line(Formula.parse('(p->q)')),
        Proof.Line(Formula.parse('q'), MP, [0, 1]),
        Proof.Line(Formula.parse('(q->r)')),
        Proof.Line(Formula.parse('r'), MP, [2, 3])
    ]
    temp_proof = Proof(statement, rules, lines)
    new_proof = remove_assumption(temp_proof)
    return new_proof

def prove_I2() -> Proof:
    """Proves `~propositions.axiomatic_systems.I2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I2` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7a

#: Double-negation elimination
_NNE = InferenceRule([], Formula.parse('(~~p->p)'))

def _prove_NNE() -> Proof:
    """Proves `_NNE` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_NNE` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7b

def prove_NN() -> Proof:
    """Proves `~propositions.axiomatic_systems.NN` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NN` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7c

#: Contraposition
_CP = InferenceRule([], Formula.parse('((p->q)->(~q->~p))'))

def _prove_CP() -> Proof:
    """Proves `_CP` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_CP` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7d

def prove_NI() -> Proof:
    """Proves `~propositions.axiomatic_systems.NI` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NI` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7e

#: Consequentia mirabilis
_CM = InferenceRule([Formula.parse('(~p->p)')], Formula.parse('p'))

def _prove_CM() -> Proof:
    """Proves `_CM` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_CM` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7f

def prove_R() -> Proof:
    """Proves `~propositions.axiomatic_systems.R` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.R` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7g

def prove_N() -> Proof:
    """Proves `~propositions.axiomatic_systems.N` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N_ALTERNATIVE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.N` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N_ALTERNATIVE`.
    """
    # Optional Task 6.8

def prove_NA1() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA1` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE1`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA1` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE1`.
    """
    # Optional Task 6.9a

def prove_NA2() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE2`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA2` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE2`.
    """
    # Optional Task 6.9b

def prove_NO() -> Proof:
    """Proves `~propositions.axiomatic_systems.NO` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.OE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NO` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.OE`.
    """
    # Optional Task 6.9c
