# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: test_chapter05.py

"""Tests all Chapter 5 tasks."""

from propositions.proofs_test import *
from propositions.deduction_test import *
from propositions.some_proofs_test import *

def pretest_validity(debug=False):
    test_is_valid(debug)

def test_task7(debug=False):
    test_prove_by_way_of_contradiction(debug)

pretest_validity(False)
test_task7(True)
