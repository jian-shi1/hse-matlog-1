from predicates.deduction_test import *
from predicates.prenex_test import *
from predicates.some_proofs_test import *
from predicates.syntax_test import *
from predicates.completeness_test import *

def test_task11_3(debug=False):
    test_is_quantifier_free(debug)
    test_is_in_prenex_normal_form(debug)

test_task11_3(True)
