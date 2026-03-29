# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
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
AE1_RULE = InferenceRule([Formula.parse('(x&y)')],Formula.parse('y'))
#: Conjunction elimination (left) inference rule
AE2_RULE = InferenceRule([Formula.parse('(x&y)')],Formula.parse('x'))

def prove_and_commutativity() -> Proof:
    """Proves ``'(q&p)'`` from ``'(p&q)'`` via `A_RULE`, `AE1_RULE`, and
    `AE2_RULE`.

    Returns:
        A valid proof of ``'(q&p)'`` from the single assumption ``'(p&q)'`` via
        the inference rules `A_RULE`, `AE1_RULE`, and `AE2_RULE`.
    """
    return Proof(
        InferenceRule([Formula.parse('(p&q)')], Formula.parse('(q&p)')),
        {A_RULE, AE1_RULE, AE2_RULE},
        [Proof.Line(Formula.parse('(p&q)')),
         Proof.Line(Formula.parse('q'), AE1_RULE, [0]),
         Proof.Line(Formula.parse('p'), AE2_RULE, [0]),
         Proof.Line(Formula.parse('(q&p)'), A_RULE, [1, 2])])

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
    return Proof(
        I0,
        {MP, I1, D},
        [Proof.Line(Formula.parse('(p->((p->p)->p))'), I1, []),
         Proof.Line(Formula.parse('(p->(p->p))'), I1, []),
         Proof.Line(
             Formula.parse(
                 '((p->((p->p)->p))->((p->(p->p))->(p->p)))'),
             D, []),
         Proof.Line(Formula.parse('((p->(p->p))->(p->p))'), MP, [0, 2]),
         Proof.Line(Formula.parse('(p->p)'), MP, [1, 3])])

#: Hypothetical syllogism
HS = InferenceRule([Formula.parse('(p->q)'), Formula.parse('(q->r)')],
                   Formula.parse('(p->r)'))

def _add_assumptionless_proof(lines: list[Proof.Line], proof: Proof) -> int:
    assert proof.is_valid()
    assert len(proof.statement.assumptions) == 0
    shift = len(lines)
    for line in proof.lines:
        if line.is_assumption():
            lines.append(line)
        else:
            lines.append(Proof.Line(line.formula, line.rule,
                                    [index + shift for index in
                                     line.assumptions]))
    return len(lines) - 1

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
    proof = Proof(
        InferenceRule(
            [Formula.parse('(p->q)'), Formula.parse('(q->r)'), Formula.parse('p')],
            Formula.parse('r')
        ),
        {MP},
        [
            Proof.Line(Formula.parse('(p->q)')),
            Proof.Line(Formula.parse('(q->r)')),
            Proof.Line(Formula.parse('p')),
            Proof.Line(Formula.parse('q'), MP, [2, 0]),
            Proof.Line(Formula.parse('r'), MP, [3, 1])
        ]
    )
    return remove_assumption(proof)

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
    proof = Proof(
        InferenceRule([Formula.parse('~p')], Formula.parse('(p->q)')),
        {MP, I1, N},
        [Proof.Line(Formula.parse('~p')),
         Proof.Line(Formula.parse('(~p->(~q->~p))'), I1, []),
         Proof.Line(Formula.parse('(~q->~p)'), MP, [0, 1]),
         Proof.Line(Formula.parse('((~q->~p)->(p->q))'), N, []),
         Proof.Line(Formula.parse('(p->q)'), MP, [2, 3])])
    return remove_assumption(proof)

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
    proof = Proof(
        InferenceRule([Formula.parse('~~p'), Formula.parse('~p')],
                      Formula.parse('~(p->p)')),
        {MP, I0, I1, D, N},
        [Proof.Line(Formula.parse('~~p')),
         Proof.Line(Formula.parse('~p'))])
    lines = list(proof.lines)
    i2_proof = prove_specialization(
        prove_I2(),
        InferenceRule([], Formula.parse('(~~p->(~p->~(p->p)))')))
    i2_line = _add_assumptionless_proof(lines, i2_proof)
    lines.append(Proof.Line(Formula.parse('(~p->~(p->p))'), MP, [0, i2_line]))
    lines.append(Proof.Line(Formula.parse('~(p->p)'), MP, [1, len(lines) - 1]))
    return remove_assumption(prove_by_way_of_contradiction(
        Proof(proof.statement, {MP, I0, I1, D, N}, lines)))

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
    triple_negation = prove_specialization(
        _prove_NNE(), InferenceRule([], Formula.parse('(~~~p->~p)')))
    return prove_corollary(triple_negation, Formula.parse('(p->~~p)'), N)

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
    lines = [Proof.Line(Formula.parse('(p->q)')),
             Proof.Line(Formula.parse('~q')),
             Proof.Line(Formula.parse('~~p'))]
    nne_line = _add_assumptionless_proof(lines, _prove_NNE())
    lines.append(Proof.Line(Formula.parse('p'), MP, [2, nne_line]))
    p_line = len(lines) - 1
    lines.append(Proof.Line(Formula.parse('q'), MP, [p_line, 0]))
    q_line = len(lines) - 1
    i2_proof = prove_specialization(
        prove_I2(),
        InferenceRule([], Formula.parse('(~q->(q->~(p->p)))')))
    i2_line = _add_assumptionless_proof(lines, i2_proof)
    lines.append(Proof.Line(Formula.parse('(q->~(p->p))'), MP, [1, i2_line]))
    q_to_contradiction_line = len(lines) - 1
    lines.append(Proof.Line(Formula.parse('~(p->p)'), MP,
                            [q_line, q_to_contradiction_line]))
    proof = Proof(
        InferenceRule([Formula.parse('(p->q)'), Formula.parse('~q'),
                       Formula.parse('~~p')], Formula.parse('~(p->p)')),
        {MP, I0, I1, D, N},
        lines)
    return remove_assumption(remove_assumption(
        prove_by_way_of_contradiction(proof)))

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
    lines = [Proof.Line(Formula.parse('p')),
             Proof.Line(Formula.parse('~q')),
             Proof.Line(Formula.parse('~~(p->q)'))]
    nne_proof = prove_specialization(
        _prove_NNE(), InferenceRule([], Formula.parse('(~~(p->q)->(p->q))')))
    nne_line = _add_assumptionless_proof(lines, nne_proof)
    lines.append(Proof.Line(Formula.parse('(p->q)'), MP, [2, nne_line]))
    p_implies_q_line = len(lines) - 1
    lines.append(Proof.Line(Formula.parse('q'), MP, [0, p_implies_q_line]))
    q_line = len(lines) - 1
    i2_proof = prove_specialization(
        prove_I2(),
        InferenceRule([], Formula.parse('(~q->(q->~(p->p)))')))
    i2_line = _add_assumptionless_proof(lines, i2_proof)
    lines.append(Proof.Line(Formula.parse('(q->~(p->p))'), MP, [1, i2_line]))
    q_to_contradiction_line = len(lines) - 1
    lines.append(Proof.Line(Formula.parse('~(p->p)'), MP,
                            [q_line, q_to_contradiction_line]))
    proof = Proof(
        InferenceRule([Formula.parse('p'), Formula.parse('~q'),
                       Formula.parse('~~(p->q)')],
                      Formula.parse('~(p->p)')),
        {MP, I0, I1, D, N},
        lines)
    return remove_assumption(remove_assumption(
        prove_by_way_of_contradiction(proof)))

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
    lines = [Proof.Line(Formula.parse('(~p->p)')),
             Proof.Line(Formula.parse('~p')),
             Proof.Line(Formula.parse('p'), MP, [1, 0])]
    i2_proof = prove_specialization(
        prove_I2(),
        InferenceRule([], Formula.parse('(~p->(p->~(p->p)))')))
    i2_line = _add_assumptionless_proof(lines, i2_proof)
    lines.append(Proof.Line(Formula.parse('(p->~(p->p))'), MP, [1, i2_line]))
    lines.append(Proof.Line(Formula.parse('~(p->p)'), MP, [2, len(lines) - 1]))
    proof = Proof(
        InferenceRule([Formula.parse('(~p->p)'), Formula.parse('~p')],
                      Formula.parse('~(p->p)')),
        {MP, I0, I1, D, N},
        lines)
    return prove_by_way_of_contradiction(proof)

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
    neg_q_lines = [Proof.Line(Formula.parse('(q->p)')),
                   Proof.Line(Formula.parse('(~q->p)')),
                   Proof.Line(Formula.parse('~p')),
                   Proof.Line(Formula.parse('~~q'))]
    nne_proof = prove_specialization(
        _prove_NNE(), InferenceRule([], Formula.parse('(~~q->q)')))
    nne_line = _add_assumptionless_proof(neg_q_lines, nne_proof)
    neg_q_lines.append(Proof.Line(Formula.parse('q'), MP, [3, nne_line]))
    q_line = len(neg_q_lines) - 1
    neg_q_lines.append(Proof.Line(Formula.parse('p'), MP, [q_line, 0]))
    p_line = len(neg_q_lines) - 1
    i2_proof = prove_specialization(
        prove_I2(),
        InferenceRule([], Formula.parse('(~p->(p->~(p->p)))')))
    i2_line = _add_assumptionless_proof(neg_q_lines, i2_proof)
    neg_q_lines.append(Proof.Line(Formula.parse('(p->~(p->p))'), MP,
                                  [2, i2_line]))
    p_to_contradiction_line = len(neg_q_lines) - 1
    neg_q_lines.append(Proof.Line(Formula.parse('~(p->p)'), MP,
                                  [p_line, p_to_contradiction_line]))
    neg_q_proof = prove_by_way_of_contradiction(
        Proof(InferenceRule([Formula.parse('(q->p)'),
                             Formula.parse('(~q->p)'),
                             Formula.parse('~p'),
                             Formula.parse('~~q')],
                            Formula.parse('~(p->p)')),
              {MP, I0, I1, D, N},
              neg_q_lines))
    main_lines = list(neg_q_proof.lines)
    main_lines.append(Proof.Line(Formula.parse('(~q->p)')))
    main_lines.append(Proof.Line(Formula.parse('p'), MP,
                                 [len(main_lines) - 2, len(main_lines) - 1]))
    neg_proof = remove_assumption(
        Proof(InferenceRule([Formula.parse('(q->p)'), Formula.parse('(~q->p)'),
                             Formula.parse('~p')], Formula.parse('p')),
              {MP, I0, I1, D, N},
              main_lines))
    main_lines = list(neg_proof.lines)
    main_lines.append(Proof.Line(Formula.parse('p'), _CM,
                                 [len(main_lines) - 1]))
    main_proof = Proof(
        InferenceRule([Formula.parse('(q->p)'), Formula.parse('(~q->p)')],
                      Formula.parse('p')),
        neg_proof.rules.union({_CM}),
        main_lines)
    return remove_assumption(remove_assumption(
        inline_proof(main_proof, _prove_CM())))

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
    proof = Proof(
        InferenceRule([Formula.parse('(~q->~p)'), Formula.parse('p')],
                      Formula.parse('q')),
        {MP, I1, N_ALTERNATIVE},
        [Proof.Line(Formula.parse('(~q->~p)')),
         Proof.Line(Formula.parse('p')),
         Proof.Line(Formula.parse('(p->(~q->p))'), I1, []),
         Proof.Line(Formula.parse('(~q->p)'), MP, [1, 2]),
         Proof.Line(Formula.parse('((~q->~p)->((~q->p)->q))'),
                    N_ALTERNATIVE, []),
         Proof.Line(Formula.parse('((~q->p)->q)'), MP, [0, 4]),
         Proof.Line(Formula.parse('q'), MP, [3, 5])])
    return remove_assumption(remove_assumption(proof))

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
    main_proof = Proof(
        NA1,
        {MP, AE1, _CP},
        [Proof.Line(Formula.parse('((p&q)->q)'), AE1, []),
         Proof.Line(Formula.parse('(((p&q)->q)->(~q->~(p&q)))'), _CP, []),
         Proof.Line(Formula.parse('(~q->~(p&q))'), MP, [0, 1])])
    return inline_proof(main_proof, _prove_CP())

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
    main_proof = Proof(
        NA2,
        {MP, AE2, _CP},
        [Proof.Line(Formula.parse('((p&q)->p)'), AE2, []),
         Proof.Line(Formula.parse('(((p&q)->p)->(~p->~(p&q)))'), _CP, []),
         Proof.Line(Formula.parse('(~p->~(p&q))'), MP, [0, 1])])
    return inline_proof(main_proof, _prove_CP())

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
    lines = [Proof.Line(Formula.parse('~p')),
             Proof.Line(Formula.parse('~q')),
             Proof.Line(Formula.parse('~~(p|q)'))]
    nne_line = _add_assumptionless_proof(
        lines,
        prove_specialization(_prove_NNE(),
                             InferenceRule([],
                                           Formula.parse('(~~(p|q)->(p|q))'))))
    lines.append(Proof.Line(Formula.parse('(p|q)'), MP, [2, nne_line]))
    p_or_q_line = len(lines) - 1
    i2_p_line = _add_assumptionless_proof(
        lines,
        prove_specialization(
            prove_I2(),
            InferenceRule([], Formula.parse('(~p->(p->~(p->p)))'))))
    lines.append(Proof.Line(Formula.parse('(p->~(p->p))'), MP, [0, i2_p_line]))
    p_to_contradiction_line = len(lines) - 1
    i2_q_line = _add_assumptionless_proof(
        lines,
        prove_specialization(
            prove_I2(),
            InferenceRule([], Formula.parse('(~q->(q->~(p->p)))'))))
    lines.append(Proof.Line(Formula.parse('(q->~(p->p))'), MP, [1, i2_q_line]))
    q_to_contradiction_line = len(lines) - 1
    lines.append(Proof.Line(
        Formula.parse('((p->~(p->p))->((q->~(p->p))->((p|q)->~(p->p))))'),
        OE, []))
    lines.append(Proof.Line(
        Formula.parse('((q->~(p->p))->((p|q)->~(p->p)))'),
        MP, [p_to_contradiction_line, len(lines) - 1]))
    lines.append(Proof.Line(Formula.parse('((p|q)->~(p->p))'),
                            MP, [q_to_contradiction_line, len(lines) - 1]))
    lines.append(Proof.Line(Formula.parse('~(p->p)'),
                            MP, [p_or_q_line, len(lines) - 1]))
    proof = Proof(
        InferenceRule([Formula.parse('~p'), Formula.parse('~q'),
                       Formula.parse('~~(p|q)')],
                      Formula.parse('~(p->p)')),
        {MP, I0, I1, D, N, OE},
        lines)
    return remove_assumption(remove_assumption(
        prove_by_way_of_contradiction(proof)))