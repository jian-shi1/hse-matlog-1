# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: test_chapter04.py

from propositions.proofs_test import *
from propositions.semantics_test import *
from propositions.some_proofs_test import *
from propositions.soundness_test import *


def test_task6(debug=False):
    test_rule_for_line(debug)
    test_is_line_valid(debug)
    test_is_valid(debug)
    
test_task6(True)
