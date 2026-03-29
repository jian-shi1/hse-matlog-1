# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2025
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
    """Computes the formulas that capture the given model: ``'``\\ `x`\\ ``'``
    for each variable name `x` that is assigned the value ``True`` in the given
    model, and ``'~``\\ `x`\\ ``'`` for each variable name `x` that is assigned
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
    return [Formula(variable) if model[variable] else
            Formula('~', Formula(variable))
            for variable in sorted(model)]

def prove_in_model(formula: Formula, model:Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If `formula` evaluates to ``True`` in the given model, then a valid
        proof of `formula`; otherwise a valid proof of ``'~``\\ `formula`\\ ``'``.
        The returned proof is from the formulas that capture the given model, in
        the order returned by `formulas_capturing_model`\\ ``(``\\ `model`\\ ``)``,
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
    assumptions = formulas_capturing_model(model)
    value = evaluate(formula, model)
    conclusion = formula if value else Formula('~', formula)
    if is_variable(formula.root):
        return Proof(InferenceRule(assumptions, conclusion),
                     AXIOMATIC_SYSTEM, [Proof.Line(conclusion)])
    if formula.root == '~':
        if value:
            return prove_in_model(formula.first, model)
        return prove_corollary(prove_in_model(formula.first, model),
                               conclusion, NN)
    assert formula.root == '->'
    if value:
        if not evaluate(formula.first, model):
            return prove_corollary(prove_in_model(formula.first, model),
                                   formula, I2)
        return prove_corollary(prove_in_model(formula.second, model),
                               formula, I1)
    return combine_proofs(prove_in_model(formula.first, model),
                          prove_in_model(formula.second, model),
                          conclusion, NI)

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
            with the last assumption being ``'~``\\ `assumption`\\ ``'`` instead
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
    return combine_proofs(remove_assumption(proof_from_affirmation),
                          remove_assumption(proof_from_negation),
                          proof_from_affirmation.statement.conclusion, R)

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
        `formulas_capturing_model`\\ ``(``\\ `model`\\ ``)``, via
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
    if len(model) == len(tautology.variables()):
        return prove_in_model(tautology, model)
    variable = sorted(tautology.variables())[len(model)]
    model_true = dict(model)
    model_true[variable] = True
    model_false = dict(model)
    model_false[variable] = False
    return reduce_assumption(prove_tautology(tautology, frozendict(model_true)),
                             prove_tautology(tautology,
                                             frozendict(model_false)))

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
    if is_tautology(formula):
        return prove_tautology(formula)
    for model in all_models(sorted(formula.variables())):
        if not evaluate(formula, model):
            return model
    assert False

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
    formula = rule.conclusion
    for assumption in reversed(rule.assumptions):
        formula = Formula('->', assumption, formula)
    return formula

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
    encoded = encode_as_formula(rule)
    proof = prove_tautology(encoded)
    if len(rule.assumptions) == 0:
        return proof
    lines = [Proof.Line(assumption) for assumption in rule.assumptions]
    shift = len(lines)
    for line in proof.lines:
        if line.is_assumption():
            lines.append(line)
        else:
            lines.append(Proof.Line(line.formula, line.rule,
                                    [index + shift
                                     for index in line.assumptions]))
    current_formula = encoded
    current_line = len(lines) - 1
    for index, assumption in enumerate(rule.assumptions):
        assert current_formula.root == '->'
        assert current_formula.first == assumption
        current_formula = current_formula.second
        lines.append(Proof.Line(current_formula, MP, [index, current_line]))
        current_line = len(lines) - 1
    return Proof(rule, AXIOMATIC_SYSTEM, lines)

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
    formulas = tuple(formulas)
    variables = sorted(set().union(*(formula.variables() for formula in
                                     formulas)))
    for model in all_models(variables):
        if all(evaluate(formula, model) for formula in formulas):
            return model
    return prove_sound_inference(
        InferenceRule(formulas, Formula.parse('~(p->p)')))

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
        proof of `formula`; otherwise a valid proof of ``'~``\\ `formula`\\ ``'``.
        The returned proof is from the formulas that capture the given model, in
        the order returned by `formulas_capturing_model`\\ ``(``\\ `model`\\ ``)``,
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
    assumptions = formulas_capturing_model(model)
    value = evaluate(formula, model)
    conclusion = formula if value else Formula('~', formula)
    if is_variable(formula.root):
        return Proof(InferenceRule(assumptions, conclusion),
                     AXIOMATIC_SYSTEM_FULL, [Proof.Line(conclusion)])
    if is_constant(formula.root):
        rule = T if formula.root == 'T' else NF
        return Proof(InferenceRule(assumptions, conclusion),
                     AXIOMATIC_SYSTEM_FULL,
                     [Proof.Line(conclusion, rule, [])])
    if formula.root == '~':
        if value:
            return prove_in_model_full(formula.first, model)
        return prove_corollary(prove_in_model_full(formula.first, model),
                               conclusion, NN)
    if formula.root == '->':
        if value:
            if not evaluate(formula.first, model):
                return prove_corollary(prove_in_model_full(formula.first,
                                                           model),
                                       formula, I2)
            return prove_corollary(prove_in_model_full(formula.second, model),
                                   formula, I1)
        return combine_proofs(prove_in_model_full(formula.first, model),
                              prove_in_model_full(formula.second, model),
                              conclusion, NI)
    if formula.root == '&':
        if value:
            return combine_proofs(prove_in_model_full(formula.first, model),
                                  prove_in_model_full(formula.second, model),
                                  formula, A)
        if not evaluate(formula.first, model):
            return prove_corollary(prove_in_model_full(formula.first, model),
                                   conclusion, NA2)
        return prove_corollary(prove_in_model_full(formula.second, model),
                               conclusion, NA1)
    assert formula.root == '|'
    if value:
        if evaluate(formula.first, model):
            return prove_corollary(prove_in_model_full(formula.first, model),
                                   formula, O2)
        return prove_corollary(prove_in_model_full(formula.second, model),
                               formula, O1)
    return combine_proofs(prove_in_model_full(formula.first, model),
                          prove_in_model_full(formula.second, model),
                          conclusion, NO)