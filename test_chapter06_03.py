from propositions.proofs_test import test_is_valid
from propositions.tautology_test import *
from propositions.some_proofs_test import *

def pretest_validity(debug=False):
    test_is_valid(debug)

def test_task3(debug=False):
    test_prove_tautology(debug)
    test_proof_or_counterexample(debug)

pretest_validity(False)
test_task3(True)
