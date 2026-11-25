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
            self.take("long"); self.take("long"); return "ull"
        return {"uint64_t": "u64", "int": "int", "void": "void"}[t]

    precedence = {"||": 1, "&&": 2, "==": 3, "!=": 3, "<": 4, "<=": 4,
                  ">": 4, ">=": 4, "+": 5, "-": 5, "*": 6, "/": 6, "%": 6}
    operator = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "mod",
                "==": "eq", "!=": "ne", "<": "lt", "<=": "le", ">": "gt", ">=": "ge",
                "&&": "logicalAnd", "||": "logicalOr"}

    def atom(self):
        t = self.take()
        if t == "(":
            if self.peek() in ["uint64_t", "int", "unsigned"]:
                ctype = self.ctype(); self.take(")"); return f"(.cast .{ctype} {self.atom()})"
            e = self.expr(); self.take(")"); return f"(.paren {e})"
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
            return f"(.declare .{typ} {quoted(name)} (some {e}))"
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
                    t = self.ctype(); n = self.take(); params.append(f"(.{t}, {quoted(n)})")
                    if self.peek() != ",": break
                    self.take(",")
            self.take(")"); body = self.stmt()
            out.append((name, f"{{result := .{typ}, name := {quoted(name)}, parameters := [{', '.join(params)}], emptyVoid := {str(void).lower()}, body := {body}}}"))
        return out


def main():
    # Preserve physical source bytes, including line endings. This application
    # is ASCII; its authoritative formal String is reconstructed from those
    # exact character codes, with no newline or source-code normalization.
    source_bytes = (HERE / "dual_grid.c").read_bytes()
    source = source_bytes.decode("ascii")
    if bytes(ord(c) for c in source) != source_bytes:
        raise ValueError("Source character/physical-byte association differs")
    functions = Parser(source).functions()
    header = '''/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GoldbachDirect.Correspondence.Specification

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH080PV
open GoldbachDirect

'''
    declarations = []
    for name, value in functions:
        declarations.append(f"def {name}_ast : Function :=\n  {value}\n")
    items = [".include .stdint", ".include .stdio"] + [f".function {n}_ast" for n, _ in functions]
    declarations.append("def program : Program := [" + ", ".join(items) + "]\n")
    ast_output = HERE / "lean/DualAST.lean"
    ast_output.write_text(header + "\n".join(declarations) + "\nend RH080PV\n")
    source_header = header.replace("import GoldbachDirect.Correspondence.Specification", "import DualAST")
    chars = ", ".join("Char.ofNat " + str(b) for b in source_bytes)
    token_text = re.sub(r"/\*.*?\*/", "", source, flags=re.S)
    token_certificate = re.findall(r'"(?:[^"\\]|\\.)*"|[A-Za-z0-9_]+|==|!=|<=|>=|&&|\|\||[^\s]', token_text)
    checks = ["def sourceChars : List Char := [" + chars + "]\n",
              "def source : String := String.ofList sourceChars\n",
              "def expectedTokens : List String := " + quoted(token_certificate) + "\n"]
    checks.append('''def checkedSyntax (s : String) (p : Program) : Bool :=
  checkedSource s p && Correspondence.supportedProgramSyntax p &&
    Correspondence.preprocessingAccepted s

theorem checkedSyntax_sound {s : String} {p : Program}
    (checked : checkedSyntax s p = true) : Correspondence.SourceSyntaxCorresponds s p := by
  simp only [checkedSyntax, Bool.and_eq_true] at checked
  exact .derived (checkedSource_lexes checked.1.1)
    (Correspondence.supportedProgramSyntax_sound checked.1.2)
    (Correspondence.preprocessingAccepted_sound checked.2)

theorem actual_lexed : tokenize source = some expectedTokens := by
  unfold tokenize
  simp only [source,String.toList_ofList,String.length_ofList]
  decide +kernel

theorem actual_ast_tokens : program.tokens = expectedTokens := by
  simp only [program, Program.tokens, Top.tokens, Function.tokens,
    jump_positive_ast, jump_negative_ast, sine_fixed_ast, sample_bound_ast,
    rh_dual_bound_ast, main_ast, Stmt.tokens, Expr.tokens, Literal.tokens,
    CType.tokens, Binary.token, comma, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.nil_append, List.append_nil]
  decide +kernel

theorem actual_ast_guard : Correspondence.supportedProgramSyntax program = true := by
  decide +kernel

theorem actual_preprocessing : Correspondence.preprocessingAccepted source = true := by
  unfold Correspondence.preprocessingAccepted
  simp only [source,String.toList_ofList]
  decide +kernel

theorem actual_source_checked : checkedSyntax source program = true := by
  simp [checkedSyntax,checkedSource,actual_lexed,actual_ast_tokens,
    actual_ast_guard,actual_preprocessing]

theorem actual_source_syntax : Correspondence.SourceSyntaxCorresponds source program :=
  checkedSyntax_sound actual_source_checked

#print axioms checkedSyntax_sound
#print axioms actual_source_syntax
end RH080PV
''')
    output = HERE / "lean/DualSource.lean"
    output.write_text(source_header + "\n".join(checks))
    print(json.dumps({"output": str(output), "functions": [n for n, _ in functions]}))


if __name__ == "__main__":
    main()
