# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: test_chapter07.py

from predicates.syntax_test import *
from predicates.semantics_test import *

def test_task1(debug=False):
    test_term_repr(debug)

test_task1(True)
