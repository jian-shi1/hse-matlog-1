# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    if is_variable(formula.root):
        return Formula(formula.root)
    if is_constant(formula.root):
        p = Formula('p')
        if formula.root == 'T':
            return Formula('|', p, Formula('~', p))
        return Formula('&', p, Formula('~', p))
    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first))
    assert is_binary(formula.root)
    first = to_not_and_or(formula.first)
    second = to_not_and_or(formula.second)
    if formula.root == '&' or formula.root == '|':
        return Formula(formula.root, first, second)
    if formula.root == '->':
        return Formula('|', Formula('~', first), second)
    if formula.root == '<->':
        return Formula('|',
                       Formula('&', first, second),
                       Formula('&', Formula('~', first), Formula('~', second)))
    if formula.root == '+':
        return Formula('|',
                       Formula('&', first, Formula('~', second)),
                       Formula('&', Formula('~', first), second))
    if formula.root == '-&':
        return Formula('~', Formula('&', first, second))
    if formula.root == '-|':
        return Formula('~', Formula('|', first, second))
    raise ValueError('Unknown operator: ' + formula.root)

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    def convert(f: Formula) -> Formula:
        if is_variable(f.root):
            return Formula(f.root)
        if is_unary(f.root):
            return Formula('~', convert(f.first))
        if is_binary(f.root) and f.root == '&':
            return Formula('&', convert(f.first), convert(f.second))
        if is_binary(f.root) and f.root == '|':
            left = convert(f.first)
            right = convert(f.second)
            return Formula('~',
                           Formula('&',
                                   Formula('~', left),
                                   Formula('~', right)))
        if is_constant(f.root):
            return convert(to_not_and_or(f))
        assert False

    return convert(to_not_and_or(formula))

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    def convert(f: Formula) -> Formula:
        if is_variable(f.root):
            return Formula(f.root)
        if is_unary(f.root):
            inner = convert(f.first)
            return Formula('-&', inner, inner)
        if is_binary(f.root) and f.root == '&':
            left = convert(f.first)
            right = convert(f.second)
            nand = Formula('-&', left, right)
            return Formula('-&', nand, nand)
        if is_constant(f.root):
            return convert(to_not_and(f))
        assert False

    return convert(to_not_and(formula))

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    def convert(f: Formula) -> Formula:
        if is_variable(f.root):
            return Formula(f.root)
        if is_unary(f.root):
            return Formula('~', convert(f.first))
        if is_binary(f.root) and f.root == '&':
            left = convert(f.first)
            right = convert(f.second)
            return Formula('~', Formula('->', left, Formula('~', right)))
        if is_binary(f.root) and f.root == '|':
            left = convert(f.first)
            right = convert(f.second)
            return Formula('->', Formula('~', left), right)
        if is_constant(f.root):
            return convert(to_not_and_or(f))
        assert False

    return convert(to_not_and_or(formula))

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    def convert(f: Formula) -> Formula:
        if is_variable(f.root):
            return Formula(f.root)
        if is_constant(f.root):
            return Formula('F') if f.root == 'F' else \
                Formula('->', Formula('F'), Formula('F'))
        if is_unary(f.root):
            inner = convert(f.first)
            return Formula('->', inner, Formula('F'))
        if is_binary(f.root) and f.root == '->':
            return Formula('->', convert(f.first), convert(f.second))
        assert False

    return convert(to_implies_not(formula))