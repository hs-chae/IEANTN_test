/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveReturn
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceBindings

/-- An actual complete fixed-result body gives the full source function Call
and uniqueness across internal, void, terminated and foreign alternatives. -/
theorem recursive_call_from_segment {F : Type} (context : Context F)
    (selected : findFunction context.program "fft_recursive"=some FFTRecursivePV.fft_recursive_ast)
    {caller entered middle : State F} {outObj inObj twiddleObj workObj start index step n total : Nat}
    (bound : bindParameters {caller.enterScope with environment:=[]} FFTRecursivePV.fft_recursive_ast.parameters
      (arguments outObj inObj twiddleObj workObj start index step n total)=some entered)
    (segment : ResultSegment context entered functionStatements (.returned (.integer (integer64 0))) middle) :
    let after := {middle.leaveScope entered.scope caller.environment with scope:=caller.scope}
    Call context "fft_recursive" (arguments outObj inObj twiddleObj workObj start index step n total)
      caller (.value (.integer (integer64 0))) after ∧
    ∀other result,Call context "fft_recursive"
      (arguments outObj inObj twiddleObj workObj start index step n total) caller result other →
      result=.value (.integer (integer64 0)) ∧ other=after := by
  have noLabel : ∀label,labelTail label functionStatements=none := by intro label;rfl
  have everyBody : ∀other flow,Body context functionStatements entered functionStatements flow other →
      flow=.returned (.integer (integer64 0)) ∧ other=middle := by
    intro other flow run
    cases run with
    | finish actual noJump => exact segment.every _ _ actual
    | jump actual target rest => rw [noLabel] at target;cases target
  have body : Body context functionStatements entered functionStatements
      (.returned (.integer (integer64 0))) middle :=
    .finish segment.execution (by intro label bad;cases bad)
  refine ⟨.internal selected actual_body bound body (convert64 0 (by norm_num)) rfl,?_⟩
  intro other result called
  cases called with
  | external absent named run => rw [selected] at absent;cases absent
  | internal picked shape parameters run converted finished =>
    have sameFunction:=Option.some.inj (selected.symm.trans picked)
    subst_vars
    have sameStatements:=Stmt.block.inj (actual_body.symm.trans shape)
    subst_vars
    have sameEntered:=Option.some.inj (bound.symm.trans parameters)
    subst_vars
    obtain ⟨same,rfl⟩:=everyBody _ _ run
    cases same
    have convertedSame:=Option.some.inj (converted.symm.trans (convert64 0 (by norm_num)))
    subst_vars
    exact ⟨rfl,rfl⟩
  | internalVoid picked shape impossible parameters run finished =>
    have sameFunction:=Option.some.inj (selected.symm.trans picked)
    subst_vars
    cases impossible
  | internalTerminated picked shape parameters run =>
    have sameFunction:=Option.some.inj (selected.symm.trans picked)
    subst_vars
    have sameStatements:=Stmt.block.inj (actual_body.symm.trans shape)
    subst_vars
    have sameEntered:=Option.some.inj (bound.symm.trans parameters)
    subst_vars
    cases (everyBody _ _ run).1

#print axioms recursive_call_from_segment
end RH080Next.FFTPV.RecursiveSource
