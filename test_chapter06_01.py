from propositions.proofs_test import test_is_valid
from propositions.tautology_test import *
from propositions.some_proofs_test import *

def pretest_validity(debug=False):
    test_is_valid(debug)

def test_task1(debug=False):
    test_formulas_capturing_model(debug)
    test_prove_in_model(debug)

pretest_validity(False)
test_task1(True)
