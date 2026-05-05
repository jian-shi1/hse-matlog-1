# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: test_chapter09.py

"""Tests all Chapter 9 tasks."""

from predicates.syntax_test import *
from predicates.proofs_test import *


def test_combined(debug=False):
    test_is_valid(debug)

def test_task10(debug=False):
    test_from_propositional_skeleton(debug)

def test_task11(debug=False):
    test_axiom_specialization_map_to_schema_instantiation_map(debug)
    test_prove_from_skeleton_proof(debug)

def test_task12(debug=False):
    test_prove_tautology(debug)

test_combined(True)
