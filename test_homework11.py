from predicates.deduction_test import *
from predicates.prenex_test import *
from predicates.some_proofs_test import *
from predicates.syntax_test import *
from predicates.completeness_test import *

def test_task11_1(debug=False):
    test_remove_assumption(debug)

def test_task11_2(debug=False):
    test_prove_by_way_of_contradiction(debug)

def test_task11_3(debug=False):
    test_is_quantifier_free(debug)
    test_is_in_prenex_normal_form(debug)

def test_task12_1(debug=False):
    test_is_primitively_closed(debug)
    test_is_universally_closed(debug)
    test_is_existentially_closed(debug)

def test_task12_2(debug=False):
    test_find_unsatisfied_quantifier_free_sentence(debug)


test_task11_1(True)
test_task11_2(True)
test_task11_3(True)
test_task12_1(True)
test_task12_2(True)
