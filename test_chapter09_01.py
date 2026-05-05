# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: test_chapter09.py

"""Tests all Chapter 9 tasks."""

from predicates.syntax_test import *
from predicates.proofs_test import *

def test_task1(debug=False):
    test_term_substitute(debug)


test_task1(True)
