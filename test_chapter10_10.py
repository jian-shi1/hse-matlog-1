# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: test_chapter10.py

"""Tests all Chapter 10 tasks."""

from predicates.prover_test import *
from predicates.some_proofs_test import *

def test_task10(debug=False):
    test_prove_group_unique_zero(debug)

test_task10(True)
