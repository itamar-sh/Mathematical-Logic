# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: predicates/completeness.py

"""Building blocks for proving the Completeness Theorem for Predicate Logic."""
from itertools import product
from typing import AbstractSet, Container, Set, Union

from logic_utils import fresh_constant_name_generator

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import *

def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants

def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    return is_primitively_closed(sentences) and \
           is_universally_closed(sentences) and \
           is_existentially_closed(sentences)

def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation (or both),
        is one of the given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1a
    constants = get_constants(sentences)
    relations = get_relations(sentences)
    for relation in relations:
        consts_variations = [const for const in product(constants, repeat=relation[1])]
        for variation in consts_variations:
            cur_consts = [Term(const) for const in variation]
            if Formula(relation[0], cur_consts) not in sentences and \
                    Formula("~", Formula(relation[0], cur_consts)) not in sentences:
                return False
    return True

def get_relations(formulas):
    relations = set()
    for formula in formulas:
        relations.update(formula.relations())
    return relations

def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence from the given set
        of sentences, and for every constant name from these sentences, the
        statement quantified by this sentence, with every free occurrence of the
        universal quantification variable name replaced with this constant name,
        is also in the given set; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1b
    constants = get_constants(sentences)
    quantifiers = get_specific_statements(sentences, 'A')
    for statement in quantifiers:
        for constant in constants:
            new_quant = statement[0].substitute({statement[1]: Term(constant)})
            if new_quant not in sentences:
                return False
    return True

def get_specific_statements(formulas, quantifier):
    statements = set()
    for formula in formulas:
        if formula.root == quantifier:  # Assuming prenex-normal-form
            statements.add((formula.statement, formula.variable))
    return statements

def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence from the given
        set of sentences there exists a constant name such that the statement
        quantified by this sentence, with every free occurrence of the
        existential quantification variable name replaced with this constant
        name, is also in the given set; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1c
    constants = get_constants(sentences)
    quantifiers = get_specific_statements(sentences, 'E')
    for statement in quantifiers:
        flag = False
        for constant in constants:
            new_quant = statement[0].substitute({statement[1]: Term(constant)})
            if new_quant in sentences:
                flag = True
        if not flag:
            return False
    return True

def find_unsatisfied_quantifier_free_sentence(sentences: Container[Formula],
                                              model: Model[str],
                                              unsatisfied: Formula) -> Formula:
    """
    Given a universally and existentially closed set of prenex-normal-form
    sentences, given a model whose universe is the set of all constant names
    from the given sentences, and given a sentence from the given set that the
    given model does not satisfy, finds a quantifier-free sentence from the
    given set that the given model does not satisfy.

    Parameters:
        sentences: universally and existentially closed set of
            prenex-normal-form sentences, which is only to be accessed using
            containment queries, i.e., using the ``in`` operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given set of sentences that is not
        satisfied by the given model.
    """
    # We assume that every formula in sentences is in prenex normal form and has
    # no free variable names, that sentences is universally and existentially
    # closed, and that the set of constant names that appear somewhere in
    # sentences is model.universe; but we cannot assert these since we cannot
    # iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2
    if not is_quantifier(unsatisfied.root):
        return unsatisfied
    constants = model.constant_interpretations.keys()  # all constants
    for constant in constants:
        pealed_form = unsatisfied.statement.substitute({unsatisfied.variable: Term(constant)})
        if pealed_form in sentences and not model.evaluate_formula(pealed_form, {}):
            return find_unsatisfied_quantifier_free_sentence(sentences, model, pealed_form)


def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula that contains no function names
            and no equalities, whose subformulas are to be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of which the
        given quantifier-free formula is composed using logical operators.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)
    assert len(quantifier_free.functions()) == 0
    assert '=' not in str(quantifier_free)
    # Task 12.3a
    if is_binary(quantifier_free.root):
        primitives = get_primitives(quantifier_free.first)
        primitives.update(get_primitives(quantifier_free.second))
        return primitives
    if is_unary(quantifier_free.root):
        return {quantifier_free.first}
    return {quantifier_free}

def model_or_inconsistency(sentences: AbstractSet[Formula]) -> \
        Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences that contain no
            function names and no equalities, to either find a model of, or
            prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of  a contradiction from the given formulas via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_closed(sentences)
    for sentence in sentences:
        assert len(sentence.functions()) == 0
        assert '=' not in str(sentence)
    # Task 12.3b
    # Constructing the model
    universe = get_constants(sentences)
    constant_interpretations = {constant: constant for constant in universe}
    relations_interpretations = dict()
    for sentence in sentences:
        # Sentences are closed, so only check for relations
        # Negated relations should be false, so we won't add them to the interpretations.
        if is_relation(sentence.root):
            if sentence.root not in relations_interpretations:
                relations_interpretations[sentence.root] = {tuple(const.root for const in sentence.arguments)}
            else:
                relations_interpretations[sentence.root].update({tuple(const.root for const in sentence.arguments)})
    model = Model(universe, constant_interpretations, relations_interpretations, dict())
    for sentence in sentences:
        if not model.evaluate_formula(sentence):
            # Valid proof of a contradiction from the given formulas via Axioms
            unsatisfied = find_unsatisfied_quantifier_free_sentence(sentences, model, sentence)  # 1
            primitives = get_primitives(unsatisfied)
            needed_primtives = [primitive if primitive in sentences else Formula('~', primitive) for primitive in primitives]  # 2+3
            prover = Prover(Prover.AXIOMS.union(needed_primtives).union({unsatisfied}))
            assumption_lines = {prover.add_assumption(primitive) for primitive in needed_primtives}.union({prover.add_assumption(unsatisfied)})
            and_all_primitives = Formula('&', unsatisfied, needed_primtives[0])
            for primitive in needed_primtives[1:]:
                and_all_primitives = Formula('&', primitive, and_all_primitives)
            prover.add_tautological_implication(and_all_primitives, assumption_lines)
            return prover.qed()
    return model

def combine_contradictions(proof_from_affirmation: Proof,
                           proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption (i.e., without any templates) `assumption`
            replaced with its negation ``'~``\ `assumption`\ ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions)
    assert len(common_assumptions) == \
           len(proof_from_affirmation.assumptions) - 1
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(proof_from_affirmation.assumptions -
                               common_assumptions)[0]
    negated_assumption = list(proof_from_negation.assumptions -
                              common_assumptions)[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    assert negated_assumption.formula == \
           Formula('~', affirmed_assumption.formula)
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union({affirmed_assumption,
                                                negated_assumption}):
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.4
    assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions)  # All common assumptions/axioms
    # Looking for the problematic assumption
    problem_assump_affir = list(proof_from_affirmation.assumptions.difference(assumptions))[0].formula
    problem_assump_neg = Formula('~', problem_assump_affir)
    # Constructing the proof
    prover = Prover(assumptions)
    proof_cont_of_affirmation = prove_by_way_of_contradiction(proof_from_affirmation, problem_assump_affir)
    step1 = prover.add_proof(proof_cont_of_affirmation.conclusion, proof_cont_of_affirmation)
    proof_cont_of_negation = prove_by_way_of_contradiction(proof_from_negation, problem_assump_neg)
    step2 = prover.add_proof(proof_cont_of_negation.conclusion, proof_cont_of_negation)
    step_final = prover.add_tautological_and(step1, step2)
    return prover.qed()

def eliminate_universal_instantiation_assumption(proof: Proof,
                                                 universal: Formula,
                                                 constant: str) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is the universal
    instantiation of the former with the constant name `constant`, to a proof
    of a contradiction from the same assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        universal: assumption of the given proof that is universally quantified.
        constant: constant name such that the formula `instantiation` obtained
            from the statement quantified by `universal` by replacing all free
            occurrences of the universal quantification variable name by the
            given constant name, is an assumption of the given proof.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        given proof except `instantiation`.
    """
    assert proof.is_valid()
    assert Schema(universal) in proof.assumptions
    assert universal.root == 'A'
    assert is_constant(constant)
    assert Schema(universal.statement.substitute({universal.variable:
                                                  Term(constant)})) in \
           proof.assumptions
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.5
    instantiation = universal.statement.substitute({universal.variable: Term(constant)})
    contradicted_proof = prove_by_way_of_contradiction(proof, instantiation)
    prover = Prover(contradicted_proof.assumptions)  # All assumptions except instantiation
    step0 = prover.add_proof(contradicted_proof.conclusion, contradicted_proof)
    step1 = prover.add_assumption(universal)
    step2 = prover.add_universal_instantiation(instantiation, step1, constant)
    step_final = prover.add_tautological_implication(Formula('&', contradicted_proof.conclusion, instantiation),
                                                     {step0, step2})
    return prover.qed()

def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained from the statement quantified by any universally
        quantified sentence from the given sentences by replacing all
        occurrences of the quantification variable name with some constant name
        from the given sentences.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.6
    return {sentence.statement.substitute({sentence.variable: Term(const)})
            for const in get_constants(sentences) for sentence in sentences if sentence.root == 'A'} \
        .union(sentences)

def replace_constant(proof: Proof, constant: str, variable: str = 'zz') -> \
        Proof:
    """Replaces all occurrences of the given constant name in the given proof
    with the given variable name.

    Parameters:
        proof: valid proof in which to replace.
        constant: constant name that does not appear as a template constant name
            in any of the assumptions of the given proof.
        variable: variable name that does not appear anywhere in the given proof
            or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()
    # Task 12.7a
    new_assumptions = set()
    for assumption in proof.assumptions:
        new_assumption_formula = assumption.formula.substitute({constant: Term(variable)})
        new_assumption = Schema(new_assumption_formula, assumption.templates)
        new_assumptions.add(new_assumption)
    prover = Prover(new_assumptions)
    for line in proof.lines:
        new_line_formula = line.formula.substitute({constant: Term(variable)})
        if isinstance(line, Proof.AssumptionLine):
            new_instantiation_map = dict()
            new_assumption = line.assumption
            for key in line.instantiation_map:
                new_instantiation_map[key] = str(line.instantiation_map[key]).replace(constant, variable)
            if new_assumption not in new_assumptions:
                new_assumption = Schema(new_line_formula, new_assumption.templates)
            prover.add_instantiated_assumption(new_line_formula, new_assumption, new_instantiation_map)
        elif isinstance(line, Proof.MPLine):
            prover.add_mp(new_line_formula, line.antecedent_line_number, line.conditional_line_number)
        elif isinstance(line, Proof.TautologyLine):
            prover.add_tautology(new_line_formula)
        elif isinstance(line, Proof.UGLine):
            prover.add_ug(new_line_formula, line.nonquantified_line_number)
    return prover.qed()





def eliminate_existential_witness_assumption(proof: Proof,
                                             existential: Formula,
                                             constant: str) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is the existential
    witness of the former with the witnessing constant name `constant`, to a
    proof of a contradiction from the same assumptions without `witness`.

    Parameters:
        proof: valid proof, which does not contain the variable name ``'zz'`` in
            its lines or assumptions, of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        constant: constant name such that the formula `witness` obtained from
            from the statement quantified by `existential` by replacing all free
            occurrences of the` existential quantification variable name by the
            given constant name, is an assumption of the given proof, and such
            that this constant name does not appear in any assumption of the
            given proof except `witness`.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        given proof except `witness`.
    """
    assert proof.is_valid()
    assert Schema(existential) in proof.assumptions
    assert existential.root == 'E'
    assert is_constant(constant)
    witness = existential.statement.substitute({existential.variable:
                                                Term(constant)})
    assert Schema(witness) in proof.assumptions
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
        assert 'zz' not in assumption.formula.variables()
    for assumption in proof.assumptions - {Schema(witness)}:
        assert constant not in assumption.formula.constants()
    for line in proof.lines:
        assert 'zz' not in line.formula.variables()

    # Task 12.7b
    new_assumptions = set()
    exist_p_x_schema = ""
    x = existential.variable
    p_x = existential.statement
    contradiction = proof.conclusion
    for assumption in proof.assumptions:
        if witness == assumption.formula:  # delete R(c17)
            continue
        if existential == assumption.formula:  # gets schema for Ex[R(x)]
            if exist_p_x_schema != "":
                continue
            exist_p_x_schema = assumption
        new_assumption_formula = assumption.formula.substitute({constant: Term('zz')})
        new_assumption = Schema(new_assumption_formula, assumption.templates)
        new_assumptions.add(new_assumption)
    prover = Prover(new_assumptions)
    prove_of_contradiction_with_zz = replace_constant(proof, constant)
    # step 2 - prove ~p(zz)
    p_zz = witness.substitute({constant: Term('zz')})
    prove_not_zz = prove_by_way_of_contradiction(prove_of_contradiction_with_zz, p_zz)
    step2 = prover.add_proof(prove_not_zz.conclusion, prove_not_zz)
    not_p_x = prove_not_zz.conclusion.substitute({'zz': Term(existential.variable)})
    step2_2 = prover.add_free_instantiation(not_p_x, step2, {'zz': Term(existential.variable)})

    # step 3 - ~p(zz) => Ax[~p(x)]
    forall_x_not_p_x = "A{}[{}]".format(x, not_p_x)
    step3 = prover.add_ug(forall_x_not_p_x, step2_2)

    # optional alternative way (cant do because of AXIOMS)
    # ADDITIONAL_QUANTIFICATION_AXIOMS[1] = Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
    #            {'x', 'R'}),
    # not_exist_p_zz = "~Ezz[{}]".format(prove_not_zz.conclusion.first)
    # eq = equivalence_of(Formula.parse(not_exist_p_zz), Formula.parse(forall_x_not_p_x))
    # If we can use extra axioms so:
    # step4_1 = prover.add_instantiated_assumption(eq, ADDITIONAL_QUANTIFICATION_AXIOMS[1], {'x': 'zz', 'R': p_zz})
    # step4_2 = prover.add_tautology("({}->{})".format(eq, eq.second))
    # step4_3 = prover.add_mp(eq.second, step4_1, step4_2)
    # step4_4 = prover.add_mp(eq.second.second, step3, step4_3)  # ~Ezz[p(zz)]

    # step4 = Ax[~p(x)] => ~Ex[p(x)]
    step4_1 = prover.add_universal_instantiation(not_p_x, step3, x)

    step4_2 = prover.add_tautological_implication("({}->{})".format(p_x, contradiction), {step4_1})
    p_x_cause_contradiction_and_exist_x_p_x = "({}&{})".format(
        "A{}[{}]".format(x, "({}->{})".format(p_x, contradiction)), existential)
    prover.add_tautology("~{}".format(contradiction))
    step4_3 = prover.add_instantiated_assumption(
        "({}->{})".format(p_x_cause_contradiction_and_exist_x_p_x, contradiction), Prover.ES,
        {'x': x, 'R': p_x.substitute({x: Term('_')}), 'Q': contradiction})
    step4_4 = prover.add_ug("A{}[{}]".format(x, "({}->{})".format(p_x, contradiction)), step4_2)
    step4_5 = prover.add_tautology("~{}".format(contradiction))
    not_exist_p_zz = "~E{}[{}]".format(x, p_x)
    step4 = prover.add_tautological_implication(not_exist_p_zz, {step4_3, step4_4, step4_5})
    # step 5 - we have Ex[p(x)] + ~Ex[p(x)] => contradiction (and tautology)
    step5 = prover.add_assumption(existential)
    step6 = prover.add_tautological_and(step5, step4)
    return prover.qed()



def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentence from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the statement quantified by that sentence by replacing all
        occurrences of the quantification variable name with a new constant name
        obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.8
    new_sentences = set()
    new_sentences.update(sentences)
    constants = get_constants(sentences)
    for formula in sentences:
        if formula.root != 'E':
            continue
        # check if we have to add statement
        exist_constant = False
        for constant in constants:
            if formula.statement.substitute({formula.variable: Term(constant)}) in sentences:
                exist_constant = True
        if exist_constant:
            continue
        fresh_var = next(fresh_constant_name_generator)
        witness = formula.statement.substitute({formula.variable: Term(fresh_var)})
        new_sentences.add(witness)
    return new_sentences