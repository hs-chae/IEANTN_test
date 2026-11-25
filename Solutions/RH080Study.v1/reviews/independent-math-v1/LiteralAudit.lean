import GoldbachDirect.SourceCheck
import GoldbachDirect.Correspondence.Expressions
import DualAST
import Mathlib.Tactic

open GoldbachDirect

-- Decoded AST newline and the physical C source spelling are distinct strings.
example : Literal.tokens (.string "%llu\n") = ["\"%llu\\n\""] := by decide
example : Literal.tokens (.string "%llu\\n") = ["\"%llu\\\\n\""] := by decide
example : Literal.tokens (.string "%llu\n") ≠ Literal.tokens (.string "%llu\\n") := by decide
example : tokenize "\"%llu\\n\"" = some ["\"%llu\\n\""] := by decide
example : Correspondence.LiteralSyntax ["\"%llu\\n\""] (.string "%llu\n") := by
  exact Correspondence.literal_tokens_syntax (.string "%llu\n") (by decide)

-- The actual host AST passes a correctly typed explicit unsigned-long-long cast.
example : RH080PV.main_ast.body = .block [
  .expression (.call "printf" [.literal (.string "%llu\n"),
    .cast .ull (.call "rh_dual_bound" [])]),
  .returnValue (some (.literal (.integer 0 "")))] := rfl

#print axioms GoldbachDirect.Correspondence.literal_tokens_syntax
