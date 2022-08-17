# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: propositions/soundness.py

"""Programmatic proof of the soundness of Propositional Logic."""

from typing import Tuple

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *

def rule_nonsoundness_from_specialization_nonsoundness(
        general: InferenceRule, specialization: InferenceRule, model: Model) \
        -> Model:
    """Demonstrated the non-soundness of the given general inference rule given
    an example of the non-soundness of the given specialization of this rule.

    Parameters:
        general: inference rule to the soundness of which to find a
            counterexample.
        specialization: non-sound specialization of `general`.
        model: model in which `specialization` does not hold.

    Returns:
        A model in which `general` does not hold.
    """
    assert specialization.is_specialization_of(general)
    assert not evaluate_inference(specialization, model)
    # Task 4.9
    cur_specialization_map = general.specialization_map(specialization)   # dict: str -> Formula
    cur_model = dict()  # we need to make dict: str -> bool
    for str_key in cur_specialization_map.keys():
        cur_formula = cur_specialization_map[str_key]
        cur_model[str_key] = evaluate(cur_formula, model)
    return cur_model

def nonsound_rule_of_nonsound_proof(proof: Proof, model: Model) -> \
        Tuple[InferenceRule, Model]:
    """Finds a non-sound inference rule used by the given valid proof of a
    non-sound inference rule, and demonstrates the non-soundness of the former
    rule.

    Parameters:
        proof: valid proof of a non-sound inference rule.
        model: model in which the inference rule proved by the given proof does
            not hold.

    Returns:
        A pair of a non-sound inference rule used in the given proof and a model
        in which this rule does not hold.
    """
    assert proof.is_valid()
    assert not evaluate_inference(proof.statement, model)
    # Task 4.10
    for line in proof.lines:
        if line.rule is None:
            continue
        if not evaluate(line.formula, model):  # there isn't a match. this is the lie.
            # now we make a new rule represents the current line.
            list_assumptions = list()
            for line_number in line.assumptions:
                list_assumptions.append(proof.lines[line_number].formula)  # gets all the assumptions of the line
            new_rule = InferenceRule(tuple(list_assumptions), line.formula)  # makes the new rule
            cur_map_from_str_to_formula = line.rule.specialization_map(new_rule)  # gets the transform map
            # makes final dict from the new keys to current bool values
            final_map_from_str_to_bool = dict()
            for key in cur_map_from_str_to_formula:
                # for each str - we make the the right formula into a boolean value through evaluation with our model
                final_map_from_str_to_bool[key] = evaluate(cur_map_from_str_to_formula[key], model)
            return line.rule, final_map_from_str_to_bool
    return None  # not supposed to happened
