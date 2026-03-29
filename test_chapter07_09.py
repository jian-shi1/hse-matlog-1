# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: test_chapter07.py

"""Tests all Chapter 7 tasks."""

from predicates.syntax_test import *
from predicates.semantics_test import *


def test_task9(debug=False):
    test_is_model_of(debug)

test_task9(True)
