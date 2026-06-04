from predicates.deduction_test import *
from predicates.prenex_test import *
from predicates.some_proofs_test import *
from predicates.syntax_test import *
from predicates.completeness_test import *


def test_task12_2(debug=False):
    test_find_unsatisfied_quantifier_free_sentence(debug)

test_task12_2(True)
