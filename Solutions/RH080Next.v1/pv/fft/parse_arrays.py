#!/usr/bin/env python3
"""Untrusted candidate frontend: Lean's independent grammar checks its result.

Only the actual unsigned scalar C fragment in dual_grid.c is supported. Parentheses
are retained, not erased. No source text or expected numerical output is an AST node.
"""
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def quoted(s):
    return json.dumps(s)


class Parser:
    def __init__(self, source):
        source = re.sub(r"/\*.*?\*/", "", source, flags=re.S)
        source = re.sub(r"#[^\n]*", "", source)
        self.tokens = re.findall(r'"(?:[^"\\]|\\.)*"|[0-9]+(?:ULL)?|[A-Za-z_][A-Za-z_0-9]*|==|!=|<=|>=|&&|\|\||[^\s]', source)
        self.i = 0

    def peek(self):
        return self.tokens[self.i] if self.i < len(self.tokens) else "EOF"

    def take(self, value=None):
        got = self.peek()
        if value is not None and got != value:
            raise ValueError(f"Expected {value}, found {got} at token {self.i}")
        self.i += 1
        return got

    def ctype(self):
        t = self.take()
        if t == "unsigned":
            self.take("long"); self.take("long"); result = ".ull"
        else: result = {"uint64_t": ".u64", "int": ".int", "void": ".void"}[t]
        while self.peek() == "*":
            self.take("*"); result = "(.pointer " + result + ")"
        return result

    precedence = {"||": 1, "&&": 2, "==": 3, "!=": 3, "<": 4, "<=": 4,
                  ">": 4, ">=": 4, "+": 5, "-": 5, "*": 6, "/": 6, "%": 6}
    operator = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "mod",
                "==": "eq", "!=": "ne", "<": "lt", "<=": "le", ">": "gt", ">=": "ge",
                "&&": "logicalAnd", "||": "logicalOr"}

    def atom_base(self):
        t = self.take()
        if t == "(":
            if self.peek() in ["uint64_t", "int", "unsigned"]:
                ctype = self.ctype(); self.take(")"); return f"(.cast {ctype} {self.atom()})"
            e = self.expr(); self.take(")"); return f"(.paren {e})"
        if t == "NULL":
            return "(.literal .nullPointer)"
        if t.startswith('"'):
            # The mathematical model supports the one exact printf format below.
            return f"(.literal (.string {t}))"
        if re.fullmatch(r"[0-9]+(?:ULL)?", t):
            suffix = "ULL" if t.endswith("ULL") else ""
            n = int(t[:-3] if suffix else t)
            return f"(.literal (.integer {n} {quoted(suffix)}))"
        if self.peek() == "(":
            self.take("("); args = []
            if self.peek() != ")":
                while True:
                    args.append(self.expr())
                    if self.peek() != ",": break
                    self.take(",")
            self.take(")")
            return f"(.call {quoted(t)} [{', '.join(args)}])"
        return f"(.variable {quoted(t)})"

    def atom(self):
        e = self.atom_base()
        while self.peek() == "[":
            self.take("["); index = self.expr(); self.take("]")
            e = f"(.index {e} {index})"
        return e

    def expr(self, minimum=0):
        e = self.atom()
        while self.precedence.get(self.peek(), -1) >= minimum:
            op = self.take(); right = self.expr(self.precedence[op] + 1)
            e = f"(.binary .{self.operator[op]} {e} {right})"
        return e

    def stmt(self):
        if self.peek() == "{":
            self.take("{"); items = []
            while self.peek() != "}": items.append(self.stmt())
            self.take("}")
            return f"(.block [{', '.join(items)}])"
        if self.peek() == "if":
            self.take(); self.take("("); e = self.expr(); self.take(")"); yes = self.stmt()
            no = "none"
            if self.peek() == "else":
                self.take(); no = f"(some {self.stmt()})"
            return f"(.ite {e} {yes} {no})"
        if self.peek() == "while":
            self.take(); self.take("("); e = self.expr(); self.take(")"); body = self.stmt()
            return f"(.whileLoop {e} {body})"
        if self.peek() == "return":
            self.take(); e = self.expr(); self.take(";"); return f"(.returnValue (some {e}))"
        if self.peek() in ["uint64_t", "int"]:
            typ = self.ctype(); name = self.take(); self.take("="); e = self.expr(); self.take(";")
            return f"(.declare {typ} {quoted(name)} (some {e}))"
        e = self.expr()
        if self.peek() == "=":
            self.take(); value = self.expr(); self.take(";"); return f"(.assign {e} {value})"
        self.take(";"); return f"(.expression {e})"

    def functions(self):
        out = []
        while self.peek() != "EOF":
            typ = self.ctype(); name = self.take(); self.take("("); params = []; void = False
            if self.peek() == "void":
                self.take(); void = True
            elif self.peek() != ")":
                while True:
                    t = self.ctype(); n = self.take(); params.append(f"({t}, {quoted(n)})")
                    if self.peek() != ",": break
                    self.take(",")
            self.take(")"); body = self.stmt()
            out.append((name, f"{{result := {typ}, name := {quoted(name)}, parameters := [{', '.join(params)}], emptyVoid := {str(void).lower()}, body := {body}}}"))
        return out

