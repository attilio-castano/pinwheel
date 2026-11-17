"""Sound proof proposals for mux/OR payload networks using set-valued labels.

Each opaque payload gets a distinct one-hot label; zero gets the empty set.
Label union is interpreted as bitwise OR of the represented payloads. Generated
Lean proves that interpretation preserves OR, mux, De Morgan expressions, and
double negation, then recovers the exact original theorem. Arbitrary AND, XOR,
arithmetic, and complement of data are deliberately unsupported.
"""
from __future__ import annotations

from typing import NamedTuple


class UnionAbstraction(NamedTuple):
    pair: dict
    arguments: tuple
    leaves: tuple
    left_shadow: tuple
    right_shadow: tuple
    bits: int


def _shape(tree, width):
    if tree[0] != width:
        raise ValueError("Wrong-width data expression")
    _, op, children, value = tree
    if op == "mux" and len(children) == 3 and children[0][0] == 1:
        return "mux", children
    if op == "or" and len(children) == 2:
        return "or", children
    if op == "not" and len(children) == 1:
        child = children[0]
        if child[0] != width:
            raise ValueError("Wrong-width complemented expression")
        if child[1] == "not" and len(child[2]) == 1:
            return "double_not", child[2]
        if child[1] == "and" and len(child[2]) == 2:
            return "demorgan", tuple((width, "not", (part,), None) for part in child[2])
    if op == "lit" and value == 0:
        return "zero", ()
    if op in ("var", "slice", "lit"):
        return "leaf", ()
    raise ValueError("Unsupported data operator: " + op)


def _data_children(kind, children):
    return children[1:] if kind == "mux" else children


def _leaves(left, right):
    found, width = [], left[0]

    def walk(tree):
        kind, children = _shape(tree, width)
        if kind == "leaf" and tree not in found:
            found.append(tree)
        for child in _data_children(kind, children):
            walk(child)

    walk(left)
    walk(right)
    return tuple(found)


def _shadow(tree, leaves, width):
    kind, children = _shape(tree, width)
    size = len(leaves)
    if kind == "mux":
        return size, "mux", (children[0], _shadow(children[1], leaves, width),
                             _shadow(children[2], leaves, width)), None
    if kind == "double_not":
        return _shadow(children[0], leaves, width)
    if kind in ("or", "demorgan"):
        return size, "or", tuple(_shadow(child, leaves, width) for child in children), None
    return size, "lit", (), 0 if kind == "zero" else 1 << leaves.index(tree)


def _nodes(tree):
    yield tree
    for child in tree[2]:
        yield from _nodes(child)


def _controls(tree, width):
    kind, children = _shape(tree, width)
    if kind == "mux":
        yield from _nodes(children[0])
    for child in _data_children(kind, children):
        yield from _controls(child, width)


def _instantiate(tree, arguments):
    width, op, children, value = tree
    if op == "var":
        argument = arguments[value]
        if argument[0] != width:
            raise ValueError("Wrong-width predicate argument")
        return argument
    return width, op, tuple(_instantiate(child, arguments) for child in children), value


def suggest(pair, *, max_bits=13, max_leaves=16):
    """Suggest a stronger finite set equality; compilation remains mandatory."""
    if any(type(n) is not int or n <= 0 for n in (max_bits, max_leaves)):
        raise ValueError("Limits must be positive integers")
    left, right = pair["left"], pair["right"]
    width = left[0]
    if width <= 1 or right[0] != width or left == right:
        return None
    try:
        leaves = _leaves(left, right)
    except ValueError:
        return None
    if not leaves or len(leaves) > max_leaves:
        return None
    lhs, rhs = _shadow(left, leaves, width), _shadow(right, leaves, width)
    shared = set(_controls(left, width)) & set(_controls(right, width))
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
        return tree[0], tree[1], tuple(abstract(child) for child in tree[2]), tree[3]

    abstract_left, abstract_right = abstract(lhs), abstract(rhs)
    if any(argument[0] != 1 for argument in arguments) or len(arguments) > max_bits:
        return None
    shadow_pair = {"left": abstract_left, "right": abstract_right,
                   "variables": tuple((1, "argument", k) for k in range(len(arguments)))}
    return UnionAbstraction(shadow_pair, tuple(arguments), leaves, lhs, rhs, len(arguments))


def lean_lemmas(pair, suggestion, name, render_tree):
    """Emit a set identity, its OR interpretation, and the original equality."""
    width = pair["left"][0]
    leaves = _leaves(pair["left"], pair["right"])
    if (not leaves or leaves != suggestion.leaves or
            _shadow(pair["left"], leaves, width) != suggestion.left_shadow or
            _shadow(pair["right"], leaves, width) != suggestion.right_shadow or
            _instantiate(suggestion.pair["left"], suggestion.arguments) != suggestion.left_shadow or
            _instantiate(suggestion.pair["right"], suggestion.arguments) != suggestion.right_shadow or
            suggestion.bits != len(suggestion.arguments) or
            any(argument[0] != 1 for argument in suggestion.arguments)):
        raise ValueError("Union proposal does not instantiate to this original statement")
    size = len(leaves)
    original_variables = " ".join(f"(x{k} : BitVec {width})"
                                  for k, (width, _, _) in enumerate(pair["variables"]))
    abstract_variables = " ".join(f"(x{k} : BitVec 1)" for k in range(suggestion.bits))
    names = " ".join(f"x{k}" for k in range(suggestion.bits))
    arguments = " ".join("(" + render_tree(argument) + ")" for argument in suggestion.arguments)
    data_names = " ".join(f"d{k}" for k in range(size))
    data_arguments = " ".join("(" + render_tree(leaf) + ")" for leaf in leaves)
    interpretation = " ||| ".join(f"(if tag.getLsbD {k} then d{k} else 0)" for k in range(size))
    auxiliary, interp = name + "_sets", name + "_interpret"
    gate_or, interp_or = name + "_gate_or", name + "_interpret_or"
    map_mux, map_or = name + "_map_mux", name + "_map_or"
    map_dm, map_nn = name + "_map_demorgan", name + "_map_double_not"

    def lift(tree, indent):
        kind, children = _shape(tree, width)
        if kind in ("leaf", "zero"):
            return " " * indent + f"simp [lookup, {interp}]\n"
        lemma = {"mux": map_mux, "or": map_or + " hlookup",
                 "demorgan": map_dm + " hlookup", "double_not": map_nn}[kind]
        return (" " * indent + f"apply {lemma}\n" +
                "".join(" " * indent + "·\n" + lift(child, indent + 2)
                        for child in _data_children(kind, children)))

    return (f"theorem {auxiliary} {abstract_variables} :\n"
            f"    {render_tree(suggestion.pair['left'])} = {render_tree(suggestion.pair['right'])} := by\n"
            f"  {'revert ' + names + '; ' if names else ''}decide +kernel\n\n"
            f"theorem {map_mux} {{α β : Type}} (f : α → β) (p : Prop) [Decidable p]\n"
            "    {a b : α} {c d : β} (ha : f a = c) (hb : f b = d) :\n"
            "    f (if p then a else b) = (if p then c else d) := by\n"
            "  by_cases h : p <;> simp_all\n\n"
            f"theorem {gate_or} (a b : Bool) (x : BitVec w) :\n"
            "    (if a || b then x else 0) = ((if a then x else 0) ||| (if b then x else 0)) := by\n"
            "  cases a <;> cases b <;> simp\n\n"
            f"def {interp} ({data_names} : BitVec {width}) (tag : BitVec {size}) : BitVec {width} :=\n"
            f"  {interpretation}\n\n"
            f"theorem {interp_or} ({data_names} : BitVec {width}) (a b : BitVec {size}) :\n"
            f"    {interp} {data_names} (a ||| b) = {interp} {data_names} a ||| {interp} {data_names} b := by\n"
            f"  simp only [{interp}, BitVec.getLsbD_or, {gate_or}]\n"
            "  all_goals ac_rfl\n\n"
            f"theorem {map_or} {{f : BitVec n → BitVec w}}\n"
            "    (hf : ∀ a b, f (a ||| b) = f a ||| f b) {a b : BitVec n} {c d : BitVec w}\n"
            "    (ha : f a = c) (hb : f b = d) : f (a ||| b) = c ||| d := by\n"
            "  rw [hf, ha, hb]\n\n"
            f"theorem {map_dm} {{f : BitVec n → BitVec w}}\n"
            "    (hf : ∀ a b, f (a ||| b) = f a ||| f b) {a b : BitVec n} {c d : BitVec w}\n"
            "    (ha : f a = ~~~c) (hb : f b = ~~~d) : f (a ||| b) = ~~~(c &&& d) := by\n"
            "  rw [hf, ha, hb]\n"
            "  simp only [BitVec.not_and, BitVec.not_not]\n\n"
            f"theorem {map_nn} {{f : BitVec n → BitVec w}} {{a : BitVec n}} {{c : BitVec w}}\n"
            "    (h : f a = c) : f a = ~~~(~~~c) := by\n"
            "  simpa only [BitVec.not_not] using h\n\n"
            f"theorem {name} {original_variables} :\n"
            f"    {render_tree(pair['left'])} = {render_tree(pair['right'])} := by\n"
            f"  have h := {auxiliary} {arguments}\n"
            f"  let lookup := {interp} {data_arguments}\n"
            f"  have hlookup : ∀ (a b : BitVec {size}), lookup (a ||| b) = lookup a ||| lookup b := by\n"
            f"    intro a b; exact {interp_or} {data_arguments} a b\n"
            f"  have hl : lookup ({render_tree(suggestion.left_shadow)}) = {render_tree(pair['left'])} := by\n"
            f"{lift(pair['left'], 4)}"
            f"  have hr : lookup ({render_tree(suggestion.right_shadow)}) = {render_tree(pair['right'])} := by\n"
            f"{lift(pair['right'], 4)}"
            "  exact hl.symm.trans ((congrArg lookup h).trans hr)\n")
