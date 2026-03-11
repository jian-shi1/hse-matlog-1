from propositions.proofs_test import test_is_valid
from propositions.tautology_test import *
from propositions.some_proofs_test import *


def test_task7(debug=False):
    test_prove_I2(debug)
    test_prove_NNE(debug)
    test_prove_NN(debug)
    test_prove_CP(debug)
    test_prove_NI(debug)
    test_prove_CM(debug)
    test_prove_R(debug)

def test_task8(debug=False):
    test_prove_N(debug)

test_task7(True)
test_task8(True)