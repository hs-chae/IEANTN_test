/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteCellDecompose

/-! Structural inversion of every statement in the actual finite-cell source.
The trace retains the exact ten rejecting-condition evaluations, both source
callee declarations, and the final comparison evaluation. No numerical guard
or strict inequality is a premise. -/
namespace RamanujanPV.FiniteCellTrace
open FiniteScalarMachine LCMSourcePV.Witness.C
open FiniteCellDecompose
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

def g0 : Expr := .binary "<" (.var "n") (.nat 38358837683)
def g1 : Expr := .binary "<=" (.var "next") (.var "n")
def g2 : Expr := .binary ">" (.var "next") (.nat 2000000000001)
def g3 : Expr := .binary ">" (.var "j") (.var "n")
def g4 : Expr := .binary ">" (.var "Q") (.var "j")
def g5 : Expr := .binary ">" (.var "P") (.binary "-" (.var "next") (.nat 1))
def g6 : Expr := .binary "==" (.var "Lu") (.nat 0)
def g7 : Expr := .binary "!=" (.var "Lu") (.call (.var "rpc_log_upper") [.var "n"])
def lowDecl : List Decl := [⟨"uint64_t","lo",some (.call (.var "rpc_e_low") [])⟩]
def highDecl : List Decl := [⟨"uint64_t","hi",some (.call (.var "rpc_e_high") [])⟩]
def g8 : Expr := .binary ">"
  (.binary "*" (.cast "__uint128_t" (.var "j")) (.var "hi"))
  (.binary "*" (.cast "__uint128_t" (.var "n")) (.nat 1152921504606846976))
def g9 : Expr := .binary "!=" (.cast "__uint128_t" (.var "A"))
  (.binary "/" (.binary "*" (.cast "__uint128_t" (.var "n")) (.var "lo")) (.var "Lu"))
def finalComparison : Expr := .binary "<"
  (.binary "*" (.binary "*" (.cast "__uint128_t" (.nat 1048576)) (.var "P")) (.var "P"))
  (.binary "*" (.cast "__uint128_t" (.var "A")) (.var "Q"))
def reject (e : Expr) : Stmt := .branch e (.returnStmt (.nat 0)) .skip
def statements : List Stmt := [reject g0,reject g1,reject g2,reject g3,reject g4,
  reject g5,reject g6,reject g7,.declare lowDecl,.declare highDecl,reject g8,reject g9,
  .returnStmt finalComparison]

theorem actual_statements : FiniteCellSource.cellFunction.body=.sequence statements := rfl

def FalseCondition (p : Prototypes) (c : Service) (e : Expr) (s t : State) : Prop :=
  ∃value,Eval p c e s t value ∧WideScalar.truth value=false

/-- A data-bearing operational witness, never an axiom or a numerical input. -/
structure Trace (p : Prototypes) (c : Service) (start : State) where
  s1 : State
  s2 : State
  s3 : State
  s4 : State
  s5 : State
  s6 : State
  s7 : State
  s8 : State
  s9 : State
  s10 : State
  s11 : State
  s12 : State
  finish : State
  guard0 : FalseCondition p c g0 start s1
  guard1 : FalseCondition p c g1 s1 s2
  guard2 : FalseCondition p c g2 s2 s3
  guard3 : FalseCondition p c g3 s3 s4
  guard4 : FalseCondition p c g4 s4 s5
  guard5 : FalseCondition p c g5 s5 s6
  guard6 : FalseCondition p c g6 s6 s7
  guard7 : FalseCondition p c g7 s7 s8
  low : Declare p c lowDecl s8 s9
  high : Declare p c highDecl s9 s10
  guard8 : FalseCondition p c g8 s10 s11
  guard9 : FalseCondition p c g9 s11 s12
  returned : Eval p c finalComparison s12 finish (i32 1)

/-- Positive return from the ACTUAL thirteen-statement C body discharges
all ten reject branches in source order and executes both real declarations. -/
theorem positive_trace {p : Prototypes} {c : Service} {start final : State}
    (actual : Run p c FiniteCellSource.cellFunction.body start (.returned final (i32 1))) :
    Nonempty (Trace p c start) := by
  rw [actual_statements] at actual
  obtain ⟨finish,steps⟩ := sequence_returned actual
  change SeqRun p c statements start (.returned finish (i32 1)) at steps
  obtain ⟨s1,v0,e0,f0,tail1⟩ := guard_fallthrough steps
  obtain ⟨s2,v1,e1,f1,tail2⟩ := guard_fallthrough tail1
  obtain ⟨s3,v2,e2,f2,tail3⟩ := guard_fallthrough tail2
  obtain ⟨s4,v3,e3,f3,tail4⟩ := guard_fallthrough tail3
  obtain ⟨s5,v4,e4,f4,tail5⟩ := guard_fallthrough tail4
  obtain ⟨s6,v5,e5,f5,tail6⟩ := guard_fallthrough tail5
  obtain ⟨s7,v6,e6,f6,tail7⟩ := guard_fallthrough tail6
  obtain ⟨s8,v7,e7,f7,tail8⟩ := guard_fallthrough tail7
  obtain ⟨s9,declaredLow,tail9⟩ := declaration_fallthrough tail8
  obtain ⟨s10,declaredHigh,tail10⟩ := declaration_fallthrough tail9
  obtain ⟨s11,v8,e8,f8,tail11⟩ := guard_fallthrough tail10
  obtain ⟨s12,v9,e9,f9,tail12⟩ := guard_fallthrough tail11
  have returned := final_return_value tail12
  exact ⟨⟨s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,finish,
    ⟨v0,e0,f0⟩,⟨v1,e1,f1⟩,⟨v2,e2,f2⟩,⟨v3,e3,f3⟩,⟨v4,e4,f4⟩,
    ⟨v5,e5,f5⟩,⟨v6,e6,f6⟩,⟨v7,e7,f7⟩,declaredLow,declaredHigh,
    ⟨v8,e8,f8⟩,⟨v9,e9,f9⟩,returned⟩⟩

#print axioms actual_statements
#print axioms positive_trace
end RamanujanPV.FiniteCellTrace
