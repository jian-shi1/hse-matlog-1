from predicates.deduction_test import *
from predicates.prenex_test import *
from predicates.some_proofs_test import *
from predicates.syntax_test import *
from predicates.completeness_test import *


def test_task12_1(debug=False):
    test_is_primitively_closed(debug)
    test_is_universally_closed(debug)
    test_is_existentially_closed(debug)

test_task12_1(True)
