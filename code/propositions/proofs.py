# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: propositions/proofs.py

"""Proofs by deduction in Propositional Logic."""

from __future__ import annotations
from typing import AbstractSet, FrozenSet, List, Mapping, Optional, Sequence, \
                   Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method

from propositions.syntax import *

#: A mapping from variable names to formulas.
SpecializationMap = Mapping[str, Formula]

@frozen
class InferenceRule:
    """An immutable inference rule in Propositional Logic, comprised of zero
    or more assumed propositional formulas, and a conclusion propositional
    formula.

    Attributes:
        assumptions (`~typing.Tuple`\\[`~propositions.syntax.Formula`, ...]):
            the assumptions of the rule.
        conclusion (`~propositions.syntax.Formula`): the conclusion of the rule.
    """
    assumptions: Tuple[Formula, ...]
    conclusion: Formula

    def __init__(self, assumptions: Sequence[Formula], conclusion: Formula):
        """Initializes an `InferenceRule` from its assumptions and conclusion.

        Parameters:
            assumptions: the assumptions for the rule.
            conclusion: the conclusion for the rule.
        """
        self.assumptions = tuple(assumptions)
        self.conclusion = conclusion

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes a string representation of the current inference rule.

        Returns:
            A string representation of the current inference rule.
        """
        return str([str(assumption) for assumption in self.assumptions]) + \
               ' ==> ' + "'" + str(self.conclusion) + "'"

    def __eq__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is an `InferenceRule` object that
            equals the current inference rule, ``False`` otherwise.
        """
        return isinstance(other, InferenceRule) and \
               self.assumptions == other.assumptions and \
               self.conclusion == other.conclusion

    def __ne__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not an `InferenceRule` object or
            does not does not equal the current inference rule, ``False``
            otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))
        
    def variables(self) -> Set[str]:
        """Finds all variable names in the current inference rule.

        Returns:
            A set of all variable names used in the assumptions and in the
            conclusion of the current inference rule.
        """
        # Task 4.1
        new_set = set()
        for formula in self.assumptions:
            new_set.update(formula.variables())
        new_set.update(self.conclusion.variables())
        return new_set

    def specialize(self, specialization_map: SpecializationMap) -> \
            InferenceRule:
        """Specializes the current inference rule by simultaneously substituting
        each variable name `v` that is a key in `specialization_map` with the
        formula `specialization_map[v]`.

        Parameters:
            specialization_map: mapping defining the specialization to be
                performed.

        Returns:
            The resulting inference rule.
        """        
        for variable in specialization_map:
            assert is_variable(variable)
        # Task 4.4
        conclusion = self.conclusion.substitute_variables(specialization_map)
        assumptions = []
        for assumption in self.assumptions:
            assumptions.append(assumption.substitute_variables(specialization_map))
        return InferenceRule(assumptions, conclusion)

    @staticmethod
    def _merge_specialization_maps(
            specialization_map1: Union[SpecializationMap, None],
            specialization_map2: Union[SpecializationMap, None]) -> \
            Union[SpecializationMap, None]:
        """Merges the given specialization maps while checking their
        consistency.

        Parameters:
            specialization_map1: first mapping to merge, or ``None``.
            specialization_map2: second mapping to merge, or ``None``.

        Returns:
            A single mapping containing all (key, value) pairs that appear in
            either of the given maps, or ``None`` if one of the given maps is
            ``None`` or if some key appears in both given maps but with
            different values.
        """
        if specialization_map1 is not None:
            for variable in specialization_map1:
                assert is_variable(variable)
        if specialization_map2 is not None:
            for variable in specialization_map2:
                assert is_variable(variable)
        # Task 4.5a
        if specialization_map2 is None:
            return None
        if specialization_map1 is None:
            return None

        new_dict = {}  # init new dictionary
        for key in specialization_map2.keys():
            new_dict[key] = specialization_map2[key]

        for key_from_dict1 in specialization_map1.keys():  # check values
            if key_from_dict1 in specialization_map2.keys():
                if specialization_map1[key_from_dict1] != specialization_map2[key_from_dict1]:
                    return None  # there is a collision between values with the same keys
                continue  # they equal so there is no problem
            new_dict[key_from_dict1] = specialization_map1[key_from_dict1]  # move one pair
        return new_dict

    @staticmethod
    def _formula_specialization_map(general: Formula, specialization: Formula) \
            -> Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the given formula
        specializes to the given specialization.

        Parameters:
            general: non-specialized formula for which to compute the map.
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of `general`.
        """
        # Task 4.5b

        if is_constant(general.root):
            if specialization.root != general.root:
                return None
            return {}

        if is_variable(general.root):  # base case - no branches
            new_dict = {general.root: specialization}
            return new_dict

        if is_unary(general.root):  # one branch
            if is_unary(specialization.root):
                return InferenceRule._formula_specialization_map(general.first, specialization.first)
            return None

        if is_binary(general.root):  # two_branches
            if not is_binary(specialization.root):  # case cant split
                return None
            if is_binary(specialization.root):  # case split wrong
                if specialization.root != general.root:
                    return None

            if general.first != specialization.first:  # change left branch
                new_dict_left = {general.first: specialization.first}
            answer_left = InferenceRule._formula_specialization_map(general.first, specialization.first)
            if general.second != specialization.second:  # change right branch
                new_dict_right = {general.second: specialization.second}
            answer_right = InferenceRule._formula_specialization_map(general.second, specialization.second)
            # merge branches
            return InferenceRule._merge_specialization_maps(answer_left, answer_right)

    def specialization_map(self, specialization: InferenceRule) -> \
            Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the current
        inference rule specializes to the given specialization.

        Parameters:
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of the current rule.
        """
        # Task 4.5c
        if len(self.assumptions) != len(specialization.assumptions):
            return None

        new_dict = {}
        i = 0
        for assumption in self.assumptions:
            if new_dict is None:
                return None
            temp_dict = InferenceRule._formula_specialization_map(assumption, specialization.assumptions[i])
            new_dict = InferenceRule._merge_specialization_maps(new_dict, temp_dict)
            i += 1

        temp_dict = InferenceRule._formula_specialization_map(self.conclusion, specialization.conclusion)
        new_dict = InferenceRule._merge_specialization_maps(new_dict, temp_dict)
        if new_dict == {} or new_dict is None:
            return None
        return new_dict

    def is_specialization_of(self, general: InferenceRule) -> bool:
        """Checks if the current inference rule is a specialization of the given
        inference rule.

        Parameters:
            general: non-specialized inference rule to check.

        Returns:
            ``True`` if the current inference rule is a specialization of
            `general`, ``False`` otherwise.
        """
        return general.specialization_map(self) is not None

@frozen
class Proof:
    """An immutable deductive proof in Propositional Logic, comprised of a
    statement in the form of an inference rule, a set of inference rules that
    may be used in the proof, and a list of lines that prove the statement via
    these inference rules.

    Attributes:
        statement (`InferenceRule`): the statement proven by the proof.
        rules (`~typing.AbstractSet`\\[`InferenceRule`]): the allowed rules of
            the proof.
        lines (`~typing.Tuple`\\[`Line`]): the lines of the proof.
    """
    statement: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]
    
    def __init__(self, statement: InferenceRule,
                 rules: AbstractSet[InferenceRule],
                 lines: Sequence[Proof.Line]):
        """Initializes a `Proof` from its statement, allowed inference rules,
        and lines.

        Parameters:
            statement: the statement to be proven by the proof.
            rules: the allowed rules for the proof.
            lines: the lines for the proof.
        """
        self.statement = statement
        self.rules = frozenset(rules)
        self.lines = tuple(lines)

    @frozen
    class Line:
        """An immutable line in a deductive proof, comprised of a formula that
        is justified either as an assumption of the proof, or as the conclusion
        of a specialization of an allowed inference rule of the proof, the
        assumptions of which are justified by previous lines in the proof.

        Attributes:
            formula (`~propositions.syntax.Formula`): the formula justified by
                the line.
            rule (`~typing.Optional`\\[`InferenceRule`]): the inference rule,
                out of those allowed in the proof, that has a specialization
                that concludes the formula; or ``None`` if the formula is
                justified as an assumption of the proof.
            assumptions (`~typing.Optional`\\[`~typing.Tuple`\\[`int`]): tuple
                of zero or more numbers of previous lines in the proof whose
                formulas are the respective assumptions of the specialization of
                the rule that concludes the formula, if the formula is not
                justified as an assumption of the proof.
        """
        formula: Formula
        rule: Optional[InferenceRule]
        assumptions: Optional[Tuple[int, ...]]

        def __init__(self, formula: Formula,
                     rule: Optional[InferenceRule] = None,
                     assumptions: Optional[Sequence[int]] = None):
            """Initializes a `~Proof.Line` from its formula, and optionally its
            rule and numbers of justifying previous lines.

            Parameters:
                formula: the formula to be justified by the line.
                rule: the inference rule, out of those allowed in the proof,
                    that has a specialization that concludes the formula; or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
                assumptions: numbers of previous lines in the proof whose
                    formulas are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
            """
            assert (rule is None and assumptions is None) or \
                   (rule is not None and assumptions is not None)
            self.formula = formula
            self.rule = rule
            if assumptions is not None:
                self.assumptions = tuple(assumptions)

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            if self.rule is None:
                return str(self.formula)
            else:
                r = str(self.formula) + '    (Inference Rule ' + str(self.rule)
                if len(self.assumptions) == 1:
                    r += ' on line ' + str(self.assumptions[0])
                elif len(self.assumptions) > 1:
                    r += ' on lines ' + ','.join(map(str, self.assumptions))
                r += ')'
                return r

        def is_assumption(self) -> bool:
            """Checks if the current proof line is justified as an assumption of
            the proof.

            Returns:
                ``True`` if the current proof line is justified as an assumption
                of the proof, ``False`` otherwise.
            """
            return self.rule is None
        
    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof of ' + str(self.statement) + ' via inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += 'Lines:\n'
        for i in range(len(self.lines)):
            r += ('%3d) ' % i) + str(self.lines[i]) + '\n'
        r += "QED\n"
        return r

    def rule_for_line(self, line_number: int) -> Union[InferenceRule, None]:
        """Computes the inference rule whose conclusion is the formula justified
        by the specified line, and whose assumptions are the formulas justified
        by the lines specified as the assumptions of that line.

        Parameters:
            line_number: number of the line according to which to compute the
                inference rule.

        Returns:
            The computed inference rule, with assumptions ordered in the order
            of their numbers in the specified line, or ``None`` if the specified
            line is justified as an assumption.
        """
        assert line_number < len(self.lines)
        # Task 4.6a
        line = self.lines[line_number]  # gets the current line. type: Line

        if line.is_assumption():  # if the line has no rule than is an assumption
            return None

        assumptions_of_line = list()  # list of formulas
        # for each assumption(number of previous line):
        # add the formula of the current line
        for previous_line_number in line.assumptions:
            if previous_line_number >= line_number:
                continue
            previous_line = self.lines[previous_line_number]
            assumptions_of_line.append(previous_line.formula)

        a = InferenceRule(assumptions_of_line, line.formula)
        return a

    def is_line_valid(self, line_number: int) -> bool:
        """Checks if the specified line validly follows from its justifications.

        Parameters:
            line_number: number of the line to check.

        Returns:
            If the specified line is justified as an assumption, then ``True``
            if the formula justified by this line is an assumption of the
            current proof, ``False`` otherwise. Otherwise (i.e., if the
            specified line is justified as a conclusion of an inference rule),
            ``True`` if the rule specified for that line is one of the allowed
            inference rules in the current proof, and it has a specialization
            that satisfies all of the following:

            1. The conclusion of that specialization is the formula justified by
               that line.
            2. The assumptions of this specialization are the formulas justified
               by the lines that are specified as the assumptions of that line
               (in the order of their numbers in that line), all of which must
               be previous lines.
        """
        assert line_number < len(self.lines)
        # Task 4.6b
        # justified by assumption of proof
        if self.lines[line_number].formula in self.statement.assumptions and self.lines[line_number].rule is None:
            return True
        # not an assumption of proof and has no rule (cant be justified)
        if self.lines[line_number].rule is None:
            return False
        # check if the inference rule is valid, i.e: one of the assumptions of proof
        if not self.lines[line_number].rule in self.rules:
            return False
        temp_inference_rule = self.rule_for_line(line_number)
        if temp_inference_rule.is_specialization_of(self.lines[line_number].rule):
            return True
        return False
        
    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        # Task 4.6c
        if len(self.lines) == 0 or self.statement is None:
            return False
        for i in range(len(self.lines)):
            if not self.is_line_valid(i):
                return False
        if self.lines[len(self.lines)-1].formula != self.statement.conclusion:
            return False
        return True

def prove_specialization(proof: Proof, specialization: InferenceRule) -> Proof:
    """Converts the given proof of an inference rule to a proof of the given
    specialization of that inference rule.

    Parameters:
        proof: valid proof to convert.
        specialization: specialization of the rule proven by the given proof.

    Returns:
        A valid proof of the given specialization via the same inference rules
        as the given proof.
    """
    assert proof.is_valid()
    assert specialization.is_specialization_of(proof.statement)
    # Task 5.1
    map_from_str_to_formula = proof.statement.specialization_map(specialization)  # map from proof statement to new one
    list_of_lines = list()
    for line in proof.lines:  # for each line we make a new one with the same inference rules but change formula
        new_formula = line.formula.substitute_variables(map_from_str_to_formula)
        if line.rule is None:
            new_line = Proof.Line(new_formula)
        else:
            new_line = Proof.Line(new_formula, line.rule, line.assumptions)
        list_of_lines.append(new_line)
    new_proof = Proof(specialization, proof.rules, list_of_lines)  # we change formulas in lines and in statements
    return new_proof

def _inline_proof_once(main_proof: Proof, line_number: int,
                       lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating the usage of (a specialization of)
    that "lemma" rule in the specified line in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        line_number: number of the line in `main_proof` that should be replaced.
        lemma_proof: valid proof of the inference rule of the specified line (an
            allowed inference rule of `main_proof`).

    Returns:
        A valid proof obtained by replacing the specified line in `main_proof`
        with a full (specialized) list of lines proving the formula of the
        specified line from the lines specified as the assumptions of that line,
        and updating justification line numbers specified throughout the proof
        to maintain the validity of the proof. The set of allowed inference
        rules in the returned proof is the union of the rules allowed in the two
        given proofs, but the "lemma" rule that is used in the specified line in
        `main_proof` is no longer used in the corresponding lines in the
        returned proof (and thus, this "lemma" rule is used one less time in the
        returned proof than in `main_proof`).
    """
    assert main_proof.is_valid()
    assert line_number < len(main_proof.lines)
    assert main_proof.lines[line_number].rule == lemma_proof.statement
    assert lemma_proof.is_valid()
    # Task 5.2a
    # first of all - make an Inference rule of the lemma
    # gets the assumptions of the lemma in the format of the proof
    new_assumptions_list = list()
    for assumption_line in main_proof.lines[line_number].assumptions:
        new_assumptions_list.append(main_proof.lines[assumption_line].formula)
    # rule that converts lemma
    rule_to_speciaize = InferenceRule(new_assumptions_list, main_proof.lines[line_number].formula)
    # fits lemma to the proof
    specified_lemma = prove_specialization(lemma_proof, rule_to_speciaize)

    # gets the lines of the new proof
    list_of_lines = list()
    # keep lines until the specific line. -1 because we dont want to write the start of the lemma
    for i in range(line_number):
        list_of_lines.append(main_proof.lines[i])   # add to the lines list
    # add the lines of the lemma - except the first one
    first_line_of_lemma = True
    for line in specified_lemma.lines:
        # if its the same formula like a line that is already in the proof - duplicate it
        if not(line.rule is None):   # not None - there is a rule for that
            new_line_formula = line.formula
            new_line_rule = line.rule
            new_line_assumptions = list()
            for assumption_num_line_in_lemma in range(len(line.assumptions)):
                # new_line_assumptions.append(line.assumptions[assumption_num_line_in_lemma] + line_number-1)  - changed!
                new_line_assumptions.append(line.assumptions[assumption_num_line_in_lemma] + line_number)
            new_line = Proof.Line(new_line_formula, new_line_rule, new_line_assumptions)
            list_of_lines.append(new_line)  # add to the lines list
        else:  # not rule - maybe an assumption of lemma but not of proof
            for proof_line in main_proof.lines:  # we check all the previous lines
                # prevent repeating of same lemma inside added lines
                if proof_line.rule == main_proof.lines[line_number].rule:
                    continue
                if proof_line.formula == line.formula:
                    list_of_lines.append(proof_line)  # add to the lines list
                    break
                if line.formula in main_proof.statement.assumptions:
                    list_of_lines.append(line)
                    break

    # keep lines after the specific line - the lemma end with the second
    for i in range(line_number+1, len(main_proof.lines)):
        if main_proof.lines[i].rule is None:   # nothing to update - number still the same
            list_of_lines.append(main_proof.lines[i])
        else:    # we need to update the number of lines used by old lines
            new_line_formula = main_proof.lines[i].formula
            new_line_rule = main_proof.lines[i].rule
            new_line_assumptions = list(main_proof.lines[i].assumptions)
            for j in range(len(main_proof.lines[i].assumptions)):
                # we jump the line number by the len of lemma -2 because the first and last lines in the lemma remains
                if main_proof.lines[i].assumptions[j] >= line_number:
                    new_line_assumptions[j] += len(specified_lemma.lines)-1
            new_line = Proof.Line(new_line_formula, new_line_rule, new_line_assumptions)
            list_of_lines.append(new_line)   # add to the lines list

    combined_set = set()
    combined_set.update(main_proof.rules)
    combined_set.update(lemma_proof.rules)

    new_proof = Proof(main_proof.statement, combined_set, list_of_lines)
    return new_proof

def inline_proof(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specializations
    of) that "lemma" rule in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.

    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the
        rules allowed in the two given proofs but without the "lemma" rule
        proved by `lemma_proof`.
    """
    assert main_proof.is_valid()
    assert lemma_proof.is_valid()
    # Task 5.2b
    # first of all - we make an Inference Rule from our lemma:
    rule_represents_lemma = InferenceRule(lemma_proof.statement.assumptions, lemma_proof.statement.conclusion)
    # we search for the relevant rule - supposed to be one
    rule_in_proof_similar_to_lemma = None
    for rule in main_proof.rules:
        if rule.is_specialization_of(rule_represents_lemma):
            rule_in_proof_similar_to_lemma = rule
            break
    # we find the locations when he used - keep them in list ordered from big to small
    list_of_lines_using_lemma = list()
    for i in range(len(main_proof.lines)):
        if main_proof.lines[i].rule == rule_in_proof_similar_to_lemma:
            list_of_lines_using_lemma.append(i)

    # main loop now
    # for each use of the lemma we going to insert the lemma:
    # for that we will make a new proof each time - that identical to the last version of our proof - than change it
    temp_proof_statement = main_proof.statement
    temp_proof_rules = main_proof.rules
    temp_proof_lines = main_proof.lines
    new_proof = None
    num_lines_inserted = len(lemma_proof.lines)-1
    counter_of_insertions = -1
    for num_line in list_of_lines_using_lemma:
        counter_of_insertions += 1
        temp_proof = Proof(temp_proof_statement, temp_proof_rules, temp_proof_lines)
        new_proof = _inline_proof_once(temp_proof, num_line + (num_lines_inserted * counter_of_insertions), lemma_proof)
        temp_proof_statement = new_proof.statement
        temp_proof_rules = new_proof.rules
        temp_proof_lines = new_proof.lines
    # now we supposed to have new proof with the right replaces - we just need to remove the lemma from the rules
    rules_without_the_lemma = list()
    for rule in temp_proof_rules:
        if not(rule == rule_in_proof_similar_to_lemma):
            rules_without_the_lemma.append(rule)
    new_proof = Proof(temp_proof_statement, rules_without_the_lemma, temp_proof_lines)
    return new_proof
