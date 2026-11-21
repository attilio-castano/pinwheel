"""Suggest small Boolean proof obligations without changing artifact statements.

Shared one-bit subtrees containing wider data are replaced consistently with
independent bit variables. This is generalization, not an equivalence claim:
correlations can be lost and the stronger obligation may be false. A caller may
use an untrusted oracle to reject unhelpful suggestions, but acceptance always
requires Lean to prove the stronger lemma and instantiate the original theorem.
Only kernel reduction (`decide +kernel`) is emitted; no native decision axiom.
"""
from __future__ import annotations

from typing import NamedTuple


class BooleanAbstraction(NamedTuple):
    pair: dict
    arguments: tuple
    cuts: tuple
    bits: int


def _nodes(tree):
    yield tree
    for child in tree[2]:
        yield from _nodes(child)


def _contains_wide(tree):
    return any(node[0] > 1 for node in _nodes(tree))


def substitute_variables(tree, arguments):
    """Reconstruct a generalized tree; useful for checking instantiation."""
    width, op, children, value = tree
    if op == "var":
        result = arguments[value]
        if result[0] != width:
            raise ValueError("Abstraction argument has the wrong width")
        return result
    return width, op, tuple(substitute_variables(child, arguments) for child in children), value


def suggest(pair, *, max_bits=12):
    """Return a stronger all-one-bit obligation, or None if it is not small.

    Maximal shared predicates absorb validity gates around decoded wide fields,
    rather than leaving the finite decision procedure to enumerate payload/tag
    bits. Pure Boolean fragments are deliberately retained: independently
    abstracting `~reset` while retaining `reset` would erase basic correlations.
    The original input/state variables and statement are never modified.
    """
    if type(max_bits) is not int or max_bits <= 0:
        raise ValueError("max_bits must be a positive integer")
    left, right = pair["left"], pair["right"]
    if left[0] != 1 or right[0] != 1 or left == right:
        return None
    shared = set(_nodes(left)) & set(_nodes(right))
    candidates = {node for node in shared if node[0] == 1 and node[1] != "var" and _contains_wide(node)}
    candidates.discard(left)
    candidates.discard(right)
    if not candidates:
        return None
    # Keep only outermost common predicates; do not generate independent
    # variables for both a predicate and its decoded comparison children.
    nested = {child for node in candidates for child in _nodes(node) if child != node and child in candidates}
    cuts = candidates - nested
    arguments, indices = [], {}

    def variable(argument):
        if argument not in indices:
            indices[argument] = len(arguments)
            arguments.append(argument)
        return argument[0], "var", (), indices[argument]

    def transform(tree):
        if tree in cuts or tree[1] == "var":
            return variable(tree)
        width, op, children, value = tree
        return width, op, tuple(transform(child) for child in children), value

    abstract_left, abstract_right = transform(left), transform(right)
    if any(argument[0] != 1 for argument in arguments) or len(arguments) > max_bits:
        return None
    # These equalities are syntactic checks. The generated original theorem
    # application performs the corresponding definitional check in Lean.
    if substitute_variables(abstract_left, arguments) != left or substitute_variables(abstract_right, arguments) != right:
        raise AssertionError("Abstraction failed to preserve its original instantiation")
    result = {"left": abstract_left, "right": abstract_right,
              "variables": tuple((1, "argument", k) for k in range(len(arguments)))}
    return BooleanAbstraction(result, tuple(arguments), tuple(node for node in arguments if node in cuts), len(arguments))


def lean_lemmas(pair, suggestion, name, render_tree):
    """Prove a stronger lemma, then preserve the exact public theorem type.

    Compile failure is failure; this helper neither asserts an axiom nor changes
    the theorem that artifact links instantiate. The caller chooses whether to
    fall back to its ordinary proof search when a suggestion cannot be proved.
    """
    if substitute_variables(suggestion.pair["left"], suggestion.arguments) != pair["left"] or \
            substitute_variables(suggestion.pair["right"], suggestion.arguments) != pair["right"]:
        raise ValueError("Suggestion does not instantiate to this original pair")
    original_variables = " ".join(f"(x{k} : BitVec {width})" for k, (width, _, _) in enumerate(pair["variables"]))
    abstract_variables = " ".join(f"(x{k} : BitVec 1)" for k in range(suggestion.bits))
    abstract_names = " ".join(f"x{k}" for k in range(suggestion.bits))
    arguments = " ".join("(" + render_tree(argument) + ")" for argument in suggestion.arguments)
    auxiliary = name + "_boolean"
    return (f"theorem {auxiliary} {abstract_variables} :\n"
            f"    {render_tree(suggestion.pair['left'])} = {render_tree(suggestion.pair['right'])} := by\n"
            f"  {'revert ' + abstract_names + '; ' if abstract_names else ''}decide +kernel\n\n"
            f"theorem {name} {original_variables} :\n"
            f"    {render_tree(pair['left'])} = {render_tree(pair['right'])} := by\n"
            f"  exact {auxiliary} {arguments}\n")
