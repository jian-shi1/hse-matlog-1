# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2025
# File name: predicates/functions.py

"""Syntactic conversion of predicate-logic formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator, is_z_and_number

from predicates.syntax import *
from predicates.semantics import *

def _quantify(quantifier: str, variables: List[str], formula: Formula) -> Formula:
    for variable in reversed(variables):
        formula = Formula(quantifier, variable, formula)
    return formula

def _relation_formula_from_step(step: Formula) -> Formula:
    variable = step.arguments[0]
    function_term = step.arguments[1]
    return Formula(function_name_to_relation_name(function_term.root),
                   [variable] + list(function_term.arguments))

def _replace_functions_in_atomic_formula(formula: Formula) -> Formula:
    arguments = []
    steps = []
    for argument in formula.arguments:
        if is_function(argument.root):
            argument_steps = _compile_term(argument)
            steps.extend(argument_steps)
            arguments.append(argument_steps[-1].arguments[0])
        else:
            arguments.append(argument)
    formula = Formula(formula.root, arguments)
    for step in reversed(steps):
        formula = Formula('E', step.arguments[0].root,
                          Formula('&', _relation_formula_from_step(step),
                                  formula))
    return formula

def _replace_equality_with_same_in_formula(formula: Formula) -> Formula:
    if is_equality(formula.root):
        return Formula('SAME', list(formula.arguments))
    if is_relation(formula.root):
        return formula
    if is_unary(formula.root):
        return Formula(formula.root,
                       _replace_equality_with_same_in_formula(formula.first))
    if is_binary(formula.root):
        return Formula(formula.root,
                       _replace_equality_with_same_in_formula(formula.first),
                       _replace_equality_with_same_in_formula(formula.second))
    return Formula(formula.root, formula.variable,
                   _replace_equality_with_same_in_formula(formula.statement))

def _conjunction(formulas: List[Formula]) -> Formula:
    conjunction = formulas[0]
    for formula in formulas[1:]:
        conjunction = Formula('&', conjunction, formula)
    return conjunction

def _function_relation_existence_formula(function: str, arity: int) -> Formula:
    relation = function_name_to_relation_name(function)
    arguments = [Term(f'x{i}') for i in range(1, arity + 1)]
    output = Term('y')
    formula = Formula(relation, [output] + arguments)
    formula = Formula('E', output.root, formula)
    return _quantify('A', [argument.root for argument in arguments], formula)

def _function_relation_uniqueness_formula(function: str, arity: int) -> Formula:
    relation = function_name_to_relation_name(function)
    arguments = [Term(f'x{i}') for i in range(1, arity + 1)]
    first_output = Term('y1')
    second_output = Term('y2')
    formula = Formula(
        '->',
        Formula('&',
                Formula(relation, [first_output] + arguments),
                Formula(relation, [second_output] + arguments)),
        Formula('=', [first_output, second_output]))
    return _quantify('A', [argument.root for argument in arguments] +
                     [first_output.root, second_output.root], formula)

def _relation_respects_same_formula(relation: str, arity: int) -> Formula:
    first_arguments = [Term(f'x{i}') for i in range(1, arity + 1)]
    second_arguments = [Term(f'y{i}') for i in range(1, arity + 1)]
    assumptions = [Formula('SAME', [first, second]) for first, second in
                   zip(first_arguments, second_arguments)]
    assumptions.append(Formula(relation, first_arguments))
    formula = Formula('->', _conjunction(assumptions),
                      Formula(relation, second_arguments))
    return _quantify('A', [argument.root for argument in first_arguments] +
                     [argument.root for argument in second_arguments], formula)

def _all_function_names(formulas: AbstractSet[Formula]) -> Set[Tuple[str, int]]:
    functions = set()
    for formula in formulas:
        functions.update(formula.functions())
    return functions

def _all_relation_names(formulas: AbstractSet[Formula]) -> Set[Tuple[str, int]]:
    relations = set()
    for formula in formulas:
        relations.update(formula.relations())
    return relations

def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]

def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\\ ``(``\\ `function`\\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]

def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function interpretations, replacing each function interpretation with a
    canonically corresponding relation interpretation.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            interpretations in this model.

    Returns:
        A model obtained from the given model by replacing every function
        interpretation of a function name with a relation interpretation of the
        canonically corresponding relation name, such that the relation
        interpretation contains any tuple
        ``(``\\ `x1`\\ ``,``...\\ ``,``\\ `xn`\\ ``)``  if and only if `x1` is the
        output of the function interpretation for the arguments
        ``(``\\ `x2`\\ ``,``...\\ ``,``\\ `xn`\\ ``)``.
    """
    for function in model.function_interpretations:
        assert function_name_to_relation_name(function) not in \
               model.relation_interpretations
    # Task 8.1
    relation_interpretations = dict(model.relation_interpretations)
    for function, interpretation in model.function_interpretations.items():
        relation_interpretations[function_name_to_relation_name(function)] = {
            (value,) + arguments for arguments, value in interpretation.items()}
    return Model(model.universe, model.constant_interpretations,
                 relation_interpretations)

def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function interpretations to a
    canonically corresponding model with interpretations for the given function
    names, having each new function interpretation replace a canonically
    corresponding relation interpretation.

    Parameters:
        model: model to convert, that contains no function interpretations.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has an interpretation in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\\ ``(``\\ `model`\\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    assert len(model.function_interpretations) == 0
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_interpretations
        assert function_name_to_relation_name(function) in \
               model.relation_interpretations
    # Task 8.2
    relation_interpretations = dict(model.relation_interpretations)
    function_interpretations = {}
    for function in original_functions:
        relation = function_name_to_relation_name(function)
        relation_arity = model.relation_arities[relation]
        if relation_arity < 2 or len(model.universe) == 0:
            return None
        function_arity = relation_arity - 1
        function_interpretation = {}
        for arguments in relation_interpretations[relation]:
            value = arguments[0]
            input_arguments = arguments[1:]
            if input_arguments in function_interpretation:
                return None
            function_interpretation[input_arguments] = value
        if len(function_interpretation) != len(model.universe) ** function_arity:
            return None
        function_interpretations[function] = function_interpretation
        del relation_interpretations[relation]
    return Model(model.universe, model.constant_interpretations,
                 relation_interpretations, function_interpretations)

def _compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and which
            contains no variable names that are ``z`` followed by a number.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\\ `y`\\ ``=``\\ `f`\\ ``(``\\ `x1`\\ ``,``...\\ ``,``\\ `xn`\\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\\ ``(``\\ `~logic_utils.fresh_variable_name_generator`\\ ``)``, `f`
        is a function name, and each of the `x`\\ `i` is either a constant name
        or a variable name. If `x`\\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable name of the
        last returned step evaluates in that model to the value of the given
        term.
    """
    assert is_function(term.root)
    for variable in term.variables():
        assert not is_z_and_number(variable)
    # Task 8.3
    steps = []
    arguments = []
    for argument in term.arguments:
        if is_function(argument.root):
            argument_steps = _compile_term(argument)
            steps.extend(argument_steps)
            arguments.append(argument_steps[-1].arguments[0])
        else:
            arguments.append(argument)
    variable = Term(next(fresh_variable_name_generator))
    steps.append(Formula('=', [variable, Term(term.root, arguments)]))
    return steps

def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function interpretations.

    Parameters:
        formula: formula to convert, which contains no variable names that are
            ``z`` followed by a number, and such that there exist no canonically
            corresponding function name and relation name that are both invoked
            in this formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\\ ``(``\\ `model`\\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function,arity in formula.functions()}.intersection(
                    {relation for relation,arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert not is_z_and_number(variable)
    # Task 8.4
    if is_equality(formula.root) or is_relation(formula.root):
        return _replace_functions_in_atomic_formula(formula)
    if is_unary(formula.root):
        return Formula(formula.root,
                       replace_functions_with_relations_in_formula(
                           formula.first))
    if is_binary(formula.root):
        return Formula(formula.root,
                       replace_functions_with_relations_in_formula(
                           formula.first),
                       replace_functions_with_relations_in_formula(
                           formula.second))
    return Formula(formula.root, formula.variable,
                   replace_functions_with_relations_in_formula(
                       formula.statement))

def replace_functions_with_relations_in_formulas(formulas:
                                                 AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function interpretations.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with interpretations for the functions
       names of the former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, which contain no variable names that are
            ``z`` followed by a number, and such that there exist no canonically
            corresponding function name and relation name that are both invoked
            in these formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas hold in a model `model` if and only if the
           returned formulas hold in
           `replace_functions_with_relations_in_model`\\ ``(``\\ `model`\\ ``)``.
        2. The returned formulas hold in a model `model` if and only if
           `replace_relations_with_functions_in_model`\\ ``(``\\ `model`\\ ``,``\\ `original_functions`\\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len({function_name_to_relation_name(function) for function, arity in
                _all_function_names(formulas)}.intersection(
                    {relation for relation, arity in
                     _all_relation_names(formulas)})) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert not is_z_and_number(variable)
    # Task 8.5
    original_functions = _all_function_names(formulas)
    new_formulas = {replace_functions_with_relations_in_formula(formula) for
                    formula in formulas}
    for function, arity in original_functions:
        new_formulas.add(_function_relation_existence_formula(function, arity))
        new_formulas.add(_function_relation_uniqueness_formula(function, arity))
    return new_formulas
        
def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model of the returned formulas, the
       interpretation of the relation name ``'SAME'`` is reflexive,
       symmetric, and transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model of the returned formulas, the interpretation of this
       relation name respects the interpretation of the relation name
       ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation,arity in formula.relations()}
    # Task 8.6
    x = Term('x')
    y = Term('y')
    z = Term('z')
    new_formulas = {_replace_equality_with_same_in_formula(formula) for
                    formula in formulas}
    new_formulas.add(Formula('A', 'x', Formula('SAME', [x, x])))
    new_formulas.add(Formula('A', 'x',
                             Formula('A', 'y',
                                     Formula('->',
                                             Formula('SAME', [x, y]),
                                             Formula('SAME', [y, x])))))
    new_formulas.add(Formula('A', 'x',
                             Formula('A', 'y',
                                     Formula('A', 'z',
                                             Formula('->',
                                                     Formula('&',
                                                             Formula('SAME',
                                                                     [x, y]),
                                                             Formula('SAME',
                                                                     [y, z])),
                                                     Formula('SAME',
                                                             [x, z]))))))
    for relation, arity in _all_relation_names(formulas):
        new_formulas.add(_relation_respects_same_formula(relation, arity))
    return new_formulas
        
def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds an interpretation of the relation name ``'SAME'`` in the given
    model, that canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no interpretation of the relation name
            ``'SAME'``, to add the interpretation to.

    Returns:
        A model obtained from the given model by adding an interpretation of the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\\ `x`\\ ``,``\\ `x`\\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_interpretations
    # Task 8.7
    relation_interpretations = dict(model.relation_interpretations)
    relation_interpretations['SAME'] = {(value, value) for value in
                                        model.universe}
    return Model(model.universe, model.constant_interpretations,
                 relation_interpretations, model.function_interpretations)
    
def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    interpretation of ``'SAME'`` in the given model, in the sense that any set
    of formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function interpretations, and
            contains an interpretation of the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the
            interpretations of all other relation names.

    Returns:
        A model that is a model of any set `formulas` if and only if the given
        model is a model of
        `replace_equality_with_SAME`\\ ``(``\\ `formulas`\\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        interpretation of ``'SAME'`` in the given model.
    """
    assert 'SAME' in model.relation_interpretations and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_interpretations) == 0
    # Task 8.8
    equivalence_classes = {}
    universe = set()
    for value in model.universe:
        if value in equivalence_classes:
            continue
        universe.add(value)
        for equivalent in model.universe:
            if (value, equivalent) in model.relation_interpretations['SAME']:
                equivalence_classes[equivalent] = value
    constant_interpretations = {
        constant: equivalence_classes[value]
        for constant, value in model.constant_interpretations.items()}
    relation_interpretations = {}
    for relation, interpretation in model.relation_interpretations.items():
        if relation == 'SAME':
            continue
        relation_interpretations[relation] = {
            tuple(equivalence_classes[value] for value in arguments)
            for arguments in interpretation}
    return Model(universe, constant_interpretations, relation_interpretations)