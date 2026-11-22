"""Reconstruct propositional mux equivalences with ordinary Lean proof terms.

Each SAT variable denotes a specific proposition about the two original
bitvector graphs. An abstract counterexample means this proof strategy does
not apply. The solver's RUP hints choose premises for implications which
Lean checks, including the clauses relating each mux to its real inputs.
"""
from pathlib import Path
import subprocess
import tempfile


def negation(lit):
    return f"¬p{lit}" if lit > 0 else f"p{-lit}"


def clause_type(clause):
    return " → ".join([*(negation(lit) for lit in clause), "False"])


def resolution(clauses, proof):
    """Turn unit propagation into function application under the negated clause."""
    derived = {}
    for line in proof.splitlines():
        fields = line.split()
        if not fields:
            continue
        if len(fields) < 2:
            raise ValueError("Incomplete proof line")
        if fields[1] == "d":
            continue
        index, *row = map(int, fields)
        end = row.index(0)
        conclusion, hints = row[:end], row[end + 1:-1]
        if row[-1] != 0 or any(h <= 0 for h in hints) or index in clauses:
            raise ValueError("Expected a fresh RUP addition")
        known = {-lit: f"a{k}" for k, lit in enumerate(conclusion)}
        body, used = [], set()
        for step, hint in enumerate(hints):
            clause = clauses[hint]
            missing = {lit for lit in clause if -lit not in known}
            if len(missing) > 1:
                raise ValueError("Non-unit premise in the SAT proof")
            unit = next(iter(missing), None)
            args = ["u" if lit == unit else known[-lit] for lit in clause]
            use = " ".join([f"c{hint}", *args])
            used.add(hint)
            if unit is None:
                body.append("exact " + use)
                break
            name = f"s{step}"
            # A positive literal needs classical double-negation elimination.
            intro = "Classical.byContradiction (fun u => " if unit > 0 else "(fun u => "
            body.append(f"have {name} : {negation(-unit)} := {intro}{use})")
            known[unit] = name
        else:
            raise ValueError("RUP hints did not close the clause")
        clauses[index] = conclusion
        derived[index] = (body, used)
        if not conclusion:
            return index, derived
    raise ValueError("Missing empty clause")


class GuardProblem:
    def __init__(self, rb, pair):
        self.rb = rb
        self.pair = pair
        self.words = []
        self.word_ids = {}
        self.canonical = {}
        self.propositions = []
        self.ids = {}
        self.initial = []
        self.facts = []
        self.equalities = {}
        self.constants = {v: self.prop(v, str(v)) for v in (True, False)}
        self.add([self.constants[True]], "fun hn => hn True.intro")
        self.add([-self.constants[False]], "fun hf => hf")

    def word(self, term):
        # Intern by graph identity first: hashing a shared tree recursively
        # would cost its fully expanded size.
        key = id(term)
        if key not in self.word_ids:
            width, op, args, value = term
            children = tuple(self.word(child) for child in args)
            signature = width, op, children, value
            if signature in self.canonical:
                self.word_ids[key] = self.canonical[signature]
                return self.word_ids[key]
            name = f"x{value}" if op == "var" else f"d{len(self.words)}"
            if op != "var":
                expr = self.rb.Graph.expression(None, self.rb.Node(width, op, children, value), str)
                self.words.append(f"let {name} : BitVec {width} := {expr}")
            self.canonical[signature] = name
            self.word_ids[key] = name
        return self.word_ids[key]

    def prop(self, key, definition):
        if key not in self.ids:
            self.propositions.append(definition)
            self.ids[key] = len(self.propositions)
        return self.ids[key]

    def add(self, lits, evidence):
        self.initial.append((lits, evidence))

    def gate(self, q, guard, yes, no, proof):
        h = f"g{q}"
        self.facts.append(f"have {h} := Readback.Guard.clauses ({proof} : p{q} ↔ if p{guard} then p{yes} else p{no})")
        for lits, field in (([-guard,-yes,q], ".1"), ([-guard,yes,-q], ".2.1"),
                            ([guard,-no,q], ".2.2.1"), ([guard,no,-q], ".2.2.2")):
            self.add(lits, h + field)

    def predicate(self, term, rhs):
        # rhs is another word, the literal one (truth), or a fresh observation z.
        left = self.word(term)
        right = self.word(rhs) if isinstance(rhs, tuple) else rhs
        key = (left, right)
        if key in self.ids:
            return self.ids[key]
        _, op, children, value = term
        q = self.prop(key, f"{left} = {right}")
        if rhs == "1" and op == "lit" or isinstance(rhs, tuple) and (left == right or op == rhs[1] == "lit"):
            holds = value % 2 == 1 if rhs == "1" else left == right
            self.add([q] if holds else [-q], "fun hn => hn rfl" if holds else "by decide +kernel")
            return q
        if rhs == "1" and op == "eq":
            inner = self.predicate(children[0], children[1])
            relation = "Readback.Guard.ofDecide (" + self.word(children[0]) + " = " + self.word(children[1]) + ")"
            self.add([-q,inner], f"fun h hn => hn (({relation}).mp h)")
            self.add([q,-inner], f"fun hn h => hn (({relation}).mpr h)")
            return q
        if op == "mux":
            g, a, b = children
            children_ids = self.truth(g), self.predicate(a,rhs), self.predicate(b,rhs)
            proof = f"Readback.Guard.mux {self.word(g)} {self.word(a)} {self.word(b)} {right}"
        elif rhs == "1" and op in ("and", "or", "not"):
            a = self.truth(children[0])
            yes, no = self.constants[True], self.constants[False]
            if op == "and":
                children_ids = a, self.truth(children[1]), no
            elif op == "or":
                children_ids = a, yes, self.truth(children[1])
            else:
                children_ids = a, no, yes
            lemma = {"and":"band", "or":"bor", "not":"inv"}[op]
            proof = "Readback.Guard." + lemma + " " + " ".join(self.word(c) for c in children)
        else:
            if isinstance(rhs, tuple) or rhs == "z":
                self.equalities[key] = q
            return q
        self.gate(q, *children_ids, proof=proof)
        return q

    def truth(self, term):
        return self.predicate(term, "1")

    def goal(self):
        w = self.pair["left"][0]
        rhs = "1" if w == 1 else "z"
        left, right = (self.predicate(self.pair[k], rhs) for k in ("left","right"))
        for (a,b), eq in self.equalities.items():
            if (a,"z") in self.equalities and (b,"z") in self.equalities:
                az, bz = self.equalities[a,"z"], self.equalities[b,"z"]
                self.add([-eq,-az,bz], "fun hab haz hn => hn (hab.symm.trans haz)")
                self.add([-eq,az,-bz], "fun hab hn hbz => hn (hab.trans hbz)")
        return left, right

    def introduction(self):
        if self.pair["left"][0] == 1:
            return ["apply Readback.Guard.ext"]
        return ["apply Readback.Guard.extWord", "intro z"]

    def prove(self, cadical, name):
        left,right = self.goal()
        self.add([left,right], "fun hl hr => mismatch ⟨fun h => (hl h).elim, fun h => (hr h).elim⟩")
        self.add([-left,-right], "fun hl hr => mismatch ⟨fun _ => hr, fun _ => hl⟩")
        clauses = {i: c for i,(c,_) in enumerate(self.initial,1)}
        with tempfile.TemporaryDirectory() as tmp:
            cnf, proof = [Path(tmp) / f for f in ("guards.cnf","guards.lrat")]
            cnf.write_text(f"p cnf {len(self.propositions)} {len(clauses)}\n" +
                "".join(" ".join(map(str,c)) + " 0\n" for c in clauses.values()))
            run = subprocess.run([cadical,"-q","--plain","--lrat","--no-binary",cnf,proof],
                                 capture_output=True, text=True, timeout=15)
            if run.returncode == 10:
                return None
            if run.returncode != 20:
                raise RuntimeError("SAT proof generation failed: " + run.stderr)
            empty, derived = resolution(clauses, proof.read_text())
        used = set()
        def visit(i):
            if i not in used:
                used.add(i)
                if i in derived:
                    for child in derived[i][1]:
                        visit(child)
        visit(empty)
        given = sorted(used - derived.keys())
        atoms = sorted({abs(lit) for i in used for lit in clauses[i]})
        helper = f"{name}_resolution"
        lines = [f"private theorem {helper} ("+" ".join(f"p{k}" for k in atoms)+" : Prop)"]
        lines.extend(f"    (c{k} : {clause_type(clauses[k])})" for k in given)
        lines.append("    : False := by")
        for k in sorted(used & derived.keys()):
            lines.append(f"  have c{k} : {clause_type(clauses[k])} := by")
            if clauses[k]:
                lines.append("    intro " + " ".join(f"a{i}" for i in range(len(clauses[k]))))
            lines.extend("    " + line for line in derived[k][0])
        lines.append(f"  exact c{empty}")
        tactic = ["classical", *self.words, *self.introduction()]
        tactic.extend(f"let p{k} : Prop := {p}" for k,p in enumerate(self.propositions,1))
        tactic.extend(self.facts)
        tactic.extend([f"change p{left} ↔ p{right}", "apply Classical.byContradiction", "intro mismatch"])
        tactic.append(f"exact {helper} " + " ".join(f"p{k}" for k in atoms))
        tactic.extend("  (" + self.initial[k-1][1] + ")" for k in given)
        return "\n".join(lines), "\n".join("  "+t for t in tactic)


class BitGuardProblem(GuardProblem):
    """Check one output bit. Word arithmetic can remain an unconstrained atom."""

    def __init__(self, rb, pair, bit):
        super().__init__(rb, pair)
        self.index = bit

    def truth(self, term):
        q = super().truth(term)
        if term[1] == "slice":
            child = term[2][0]
            start = term[3]
            bit = self.bit(child, start)
            proof = (f"((Readback.Guard.truthBit {self.word(term)}).symm.trans "
                     f"(Readback.Guard.bitSlice {self.word(child)} {start} 1 0 (by decide)))")
            self.equivalent(q, bit, proof)
        return q

    def equivalent(self, q, p, lemma):
        self.add([-q, p], f"fun h hn => hn (({lemma}).mp h)")
        self.add([q, -p], f"fun hn h => hn (({lemma}).mpr h)")

    def bit(self, term, index):
        width, op, args, value = term
        if not 0 <= index < width:
            raise ValueError("Bit outside its declared word")
        name = self.word(term)
        key = (name, index)
        if key in self.ids:
            return self.ids[key]
        q = self.prop(key, f"{name}.getLsbD {index} = true")
        words = [self.word(child) for child in args]
        if width == 1:
            self.equivalent(q, self.truth(term), f"Readback.Guard.truthBit {name}")
        elif op == "lit":
            if (value >> index) & 1:
                self.add([q], "fun hn => hn (by decide +kernel)")
            else:
                self.add([-q], "by decide +kernel")
        elif op == "slice":
            proof = f"Readback.Guard.bitSlice {words[0]} {value} {width} {index} (by decide)"
            self.equivalent(q, self.bit(args[0], value + index), proof)
        elif op == "concat":
            low = args[1][0]
            if index < low:
                child, position, lemma = args[1], index, "bitLow"
            else:
                child, position, lemma = args[0], index-low, "bitHigh"
            proof = f"Readback.Guard.{lemma} {words[0]} {words[1]} {index} (by decide)"
            self.equivalent(q, self.bit(child, position), proof)
        elif op == "mux":
            self.gate(q, self.truth(args[0]), self.bit(args[1], index), self.bit(args[2], index),
                      f"Readback.Guard.bitMux {' '.join(words)} {index}")
        elif op in ("and", "or", "not"):
            a = self.bit(args[0], index)
            if op == "not":
                yes, no = self.constants[False], self.constants[True]
                proof = f"Readback.Guard.bitNot {words[0]} {index} (by decide)"
            elif op == "and":
                yes, no = self.bit(args[1], index), self.constants[False]
                proof = f"Readback.Guard.bitAnd {' '.join(words)} {index}"
            else:
                yes, no = self.constants[True], self.bit(args[1], index)
                proof = f"Readback.Guard.bitOr {' '.join(words)} {index}"
            self.gate(q, a, yes, no, proof)
        return q

    def goal(self):
        return self.bit(self.pair["left"], self.index), self.bit(self.pair["right"], self.index)

    def introduction(self):
        return []


def emit_proof(write, header, rb, pair, index, solver, render):
    """Emit a word proof or exhaust its declared bits with separate checked lemmas."""
    name = f"guard_{index}"
    module = f"GuardProof{index}"
    variables = " ".join(f"(x{j} : BitVec {w})" for j, (w, _, _) in enumerate(pair["variables"]))
    args = " ".join(f"x{j}" for j in range(len(pair["variables"])))
    left, right = render(pair["left"]), render(pair["right"])
    base = "import Pinwheel.Hardware.Readback.Bits\n" + header
    end = "\nend Pinwheel.TypedArtifact\n"
    theorem = f"theorem {name} {variables} :\n    {left} = {right} := by\n"
    word = GuardProblem(rb, pair).prove(solver, name)
    if word is not None:
        resolution, proof = word
        write(module, base + resolution + "\n" + theorem + proof + end)
        return [module]

    width = pair["left"][0]
    modules = []
    cases = []
    for k in range(width):
        lemma = f"{name}_bit{k}"
        result = BitGuardProblem(rb, pair, k).prove(solver, lemma)
        if result is None:
            raise ValueError(f"Unresolved bit {k} of {pair['source']}")
        resolution, proof = result
        bit_module = f"{module}Bit{k}"
        write(bit_module, base + resolution + f"\ntheorem {lemma} {variables} :\n"
              f"    {left}.getLsbD {k} = true ↔ {right}.getLsbD {k} = true := by\n" + proof + end)
        modules.append(bit_module)
        cases.append(f"  | {k} => exact {lemma} {args}")
    imports = "".join(f"import {unit}\n" for unit in modules)
    write(module, imports + base + theorem + "  apply Readback.Guard.bitExt\n  intro k bound\n  match k with\n" +
          "\n".join(cases) + f"\n  | k+{width} => omega\n" + end)
    return [*modules, module]
