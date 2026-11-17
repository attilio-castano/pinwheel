"""Kernel-checkable finite labels for wide mux-tree equality proposals.

The data fragment must consist of muxes and opaque variable/literal/slice
leaves. Numeric labels are deliberately NOT used for data bitwise operators:
arbitrary payload interpretation does not preserve those operators. Shared
wide predicates are generalized to independent bits only for proof search.
The emitted original theorem is recovered by a proved mux homomorphism.
"""
from __future__ import annotations

from typing import NamedTuple


class MuxAbstraction(NamedTuple):
    pair: dict
    arguments: tuple
    leaves: tuple
    left_shadow: tuple
    right_shadow: tuple
    tag_width: int
    bits: int


def _nodes(tree):
    yield tree
    for child in tree[2]:
        yield from _nodes(child)


def _data_leaves(tree, width, result):
    if tree[0] != width:
        return False
    if tree[1] == "mux":
        return (len(tree[2]) == 3 and tree[2][0][0] == 1 and
                _data_leaves(tree[2][1], width, result) and
                _data_leaves(tree[2][2], width, result))
    if tree[1] not in ("var", "lit", "slice"):
        return False
    if tree not in result:
        result.append(tree)
    return True


def _shadow(tree, leaves, tag_width):
    if tree[1] == "mux":
        condition, yes, no = tree[2]
        return tag_width, "mux", (condition, _shadow(yes, leaves, tag_width),
                                  _shadow(no, leaves, tag_width)), tree[3]
    return tag_width, "lit", (), leaves.index(tree)


def _control_nodes(tree):
    if tree[1] == "mux":
        yield from _nodes(tree[2][0])
        yield from _control_nodes(tree[2][1])
        yield from _control_nodes(tree[2][2])


def _instantiate(tree, arguments):
    width, op, children, value = tree
    if op == "var":
        argument = arguments[value]
        if argument[0] != width:
            raise ValueError("Wrong-width predicate argument")
        return argument
    return width, op, tuple(_instantiate(child, arguments) for child in children), value


def suggest(pair, *, max_bits=13, max_leaves=16):
    """Propose a small label equality, or decline unsupported/large data trees.

    A proposal can be false after predicate generalization. An oracle may
    discard it; only compiling the emitted Lean lemmas can establish it.
    """
    if any(type(n) is not int or n <= 0 for n in (max_bits, max_leaves)):
        raise ValueError("Limits must be positive integers")
    left, right = pair["left"], pair["right"]
    width = left[0]
    if width <= 1 or right[0] != width or left == right:
        return None
    leaves = []
    if not _data_leaves(left, width, leaves) or not _data_leaves(right, width, leaves):
        return None
    if len(leaves) > max_leaves:
        return None
    tag_width = max(1, (len(leaves) - 1).bit_length())
    lhs, rhs = _shadow(left, leaves, tag_width), _shadow(right, leaves, tag_width)
    # A one-bit label is still data. Only predicates reached through an actual
    # mux condition may be generalized, even when two data leaves use one bit.
    shared = set(_control_nodes(left)) & set(_control_nodes(right))
    candidates = {node for node in shared if node[0] == 1 and node[1] != "var" and
                  any(child[0] > 1 for child in _nodes(node))}
    nested = {child for node in candidates for child in _nodes(node)
              if child != node and child in candidates}
    cuts = candidates - nested
    arguments = []

    def abstract(tree):
        if tree in cuts or tree[1] == "var":
            if tree not in arguments:
                arguments.append(tree)
            return tree[0], "var", (), arguments.index(tree)
        width, op, children, value = tree
        return width, op, tuple(abstract(child) for child in children), value

    abstract_left, abstract_right = abstract(lhs), abstract(rhs)
    if any(argument[0] != 1 for argument in arguments) or len(arguments) > max_bits:
        return None
    shadow_pair = {"left": abstract_left, "right": abstract_right,
                   "variables": tuple((1, "argument", k) for k in range(len(arguments)))}
    return MuxAbstraction(shadow_pair, tuple(arguments), tuple(leaves), lhs, rhs,
                          tag_width, len(arguments))


def lean_lemmas(pair, suggestion, name, render_tree):
    """Preserve the exact original statement via checked label interpretation."""
    leaves = []
    width = pair["left"][0]
    if not _data_leaves(pair["left"], width, leaves) or not _data_leaves(pair["right"], width, leaves):
        raise ValueError("Unsupported data operator in mux abstraction")
    if (tuple(leaves) != suggestion.leaves or len(leaves) > 2**suggestion.tag_width or
            _shadow(pair["left"], leaves, suggestion.tag_width) != suggestion.left_shadow or
            _shadow(pair["right"], leaves, suggestion.tag_width) != suggestion.right_shadow or
            _instantiate(suggestion.pair["left"], suggestion.arguments) != suggestion.left_shadow or
            _instantiate(suggestion.pair["right"], suggestion.arguments) != suggestion.right_shadow or
            suggestion.bits != len(suggestion.arguments) or
            any(argument[0] != 1 for argument in suggestion.arguments)):
        raise ValueError("Mux proposal does not instantiate to this original statement")
    original_variables = " ".join(f"(x{k} : BitVec {width})"
                                  for k, (width, _, _) in enumerate(pair["variables"]))
    abstract_variables = " ".join(f"(x{k} : BitVec 1)" for k in range(suggestion.bits))
    names = " ".join(f"x{k}" for k in range(suggestion.bits))
    arguments = " ".join("(" + render_tree(argument) + ")" for argument in suggestion.arguments)
    lookup = render_tree(leaves[-1])
    for k, leaf in reversed(list(enumerate(leaves[:-1]))):
        lookup = (f"(if tag = ({k}#{suggestion.tag_width}) then "
                  f"{render_tree(leaf)} else {lookup})")
    auxiliary, lifting = name + "_labels", name + "_map_mux"

    def lift(tree, indent):
        if tree[1] != "mux":
            return " " * indent + "rfl\n"
        return (" " * indent + f"apply {lifting}\n" + " " * indent + "·\n" +
                lift(tree[2][1], indent + 2) + " " * indent + "·\n" +
                lift(tree[2][2], indent + 2))

    return (f"theorem {auxiliary} {abstract_variables} :\n"
            f"    {render_tree(suggestion.pair['left'])} = {render_tree(suggestion.pair['right'])} := by\n"
            f"  {'revert ' + names + '; ' if names else ''}decide +kernel\n\n"
            f"theorem {lifting} {{α β : Type}} (f : α → β) (p : Prop) [Decidable p]\n"
            "    {a b : α} {c d : β} (ha : f a = c) (hb : f b = d) :\n"
            "    f (if p then a else b) = (if p then c else d) := by\n"
            "  by_cases h : p <;> simp_all\n\n"
            f"theorem {name} {original_variables} :\n"
            f"    {render_tree(pair['left'])} = {render_tree(pair['right'])} := by\n"
            f"  have h := {auxiliary} {arguments}\n"
            f"  let lookup := fun (tag : BitVec {suggestion.tag_width}) => {lookup}\n"
            f"  have hl : lookup ({render_tree(suggestion.left_shadow)}) = {render_tree(pair['left'])} := by\n"
            f"{lift(pair['left'], 4)}"
            f"  have hr : lookup ({render_tree(suggestion.right_shadow)}) = {render_tree(pair['right'])} := by\n"
            f"{lift(pair['right'], 4)}"
            "  exact hl.symm.trans ((congrArg lookup h).trans hr)\n")
