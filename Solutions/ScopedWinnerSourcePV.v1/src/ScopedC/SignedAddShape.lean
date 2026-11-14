/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SignedMultiplyBody

namespace ScopedC.SignedAddCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.NatWrapperCalls
open ScopedC.DyadicRepresentation
open ScopedC.SignedPairFrames (frame)
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def same (a b : Endpoint) : Bool := a.negative==b.negative
def left (a b : Endpoint) : Bool := decide (b.magnitude≤a.magnitude)
def magnitude (a b : Endpoint) : Nat :=
  if same a b then a.magnitude+b.magnitude else if left a b then a.magnitude-b.magnitude else b.magnitude-a.magnitude

def negative (a b : Endpoint) : Bool := if same a b then a.negative else if left a b then a.negative else b.negative

def opName (a b : Endpoint) : String := if same a b then "na" else "ns"
def firstSlot (a b : Endpoint) : Nat := if same a b then a.slot else if left a b then a.slot else b.slot
def secondSlot (a b : Endpoint) : Nat := if same a b then b.slot else if left a b then b.slot else a.slot

def sameTest : Expr := .binary "==" (.field "." (.var "a") "neg") (.field "." (.var "b") "neg")
def lessTest : Expr := .call (.var "nle") [.field "." (.var "b") "mag",.field "." (.var "a") "mag"]
def plusReturn : Expr := .call (.var "smake") [
  .call (.var "na") [.field "." (.var "a") "mag",.field "." (.var "b") "mag"],.field "." (.var "a") "neg"]
def leftReturn : Expr := .call (.var "smake") [
  .call (.var "ns") [.field "." (.var "a") "mag",.field "." (.var "b") "mag"],.field "." (.var "a") "neg"]
def rightReturn : Expr := .call (.var "smake") [
  .call (.var "ns") [.field "." (.var "b") "mag",.field "." (.var "a") "mag"],.field "." (.var "b") "neg"]
def selectedReturn (a b : Endpoint) : Expr := if same a b then plusReturn else if left a b then leftReturn else rightReturn

theorem mathematical (a b : Endpoint) :
    Signed.make (magnitude a b) (negative a b)=Signed.add a.mathematical b.mathematical := by
  by_cases hs : a.negative=b.negative <;> by_cases hl : b.magnitude≤a.magnitude <;>
    simp [magnitude,negative,same,left,Signed.add,Endpoint.mathematical,hs,hl]

theorem same_value (s : State) (a b : Bool) :
    binaryValue Header.layout s "==" (unsigned32 (SignedNegCalls.bit a)) (unsigned32 (SignedNegCalls.bit b))=
      some (Machine.boolean Header.layout (a==b)) := by
  cases a <;> cases b <;> rfl

theorem same_eval (call : Call) (s : State) (a b : Endpoint) :
    Eval Header.layout call sameTest (frame s a b) (frame s a b) (Machine.boolean Header.layout (same a b)) := by
  refine ⟨4,?_⟩
  exact ExpressionTemplates.binary Header.layout call (by decide) (by decide) (by decide) (by decide)
    (SignedPairFrames.eval_a_neg call 1 s a b) (SignedPairFrames.eval_b_neg call 1 s a b)
    (same_value (frame s a b) _ _)

theorem truth_boolean (b : Bool) : truth (Machine.boolean Header.layout b)=b := by cases b <;> rfl
theorem truth_bit (b : Bool) : truth (unsigned32 (SignedNegCalls.bit b))=b := by cases b <;> rfl

/-- Structural execution of both actual source branch tests and whichever
actual return expression the source selects. No name/body-label execution rule. -/
theorem body (call : Call) (s after : State) (a b : Endpoint) (out : Value)
    (length : after.heap.length=(frame s a b).heap.length) (env : after.env=(frame s a b).env)
    (less : Eval Header.layout call lessTest (frame s a b) (frame s a b)
      (unsigned32 (SignedNegCalls.bit (left a b))))
    (ret : Eval Header.layout call (selectedReturn a b) (frame s a b) after out) :
    Run Header.layout call Generated.f_sa.body (frame s a b) (.returned after out) := by
  change Run Header.layout call (.sequence [
    .branch sameTest (.returnStmt plusReturn) .skip,
    .branch lessTest (.returnStmt leftReturn) .skip,.returnStmt rightReturn])
    (frame s a b) (.returned after out)
  have equal := same_eval call s a b
  cases hs : same a b with
  | true =>
    have selected : Eval Header.layout call plusReturn (frame s a b) after out := by
      simpa only [selectedReturn,hs,↓reduceIte] using ret
    have hit : Run Header.layout call (.branch sameTest (.returnStmt plusReturn) .skip)
        (frame s a b) (.returned after out) := by
      apply Loops.StmtRun.branch equal
      simpa only [truth_boolean,hs,↓reduceIte] using
        (Loops.StmtRun.returnValue selected : Run Header.layout call (.returnStmt plusReturn)
          (frame s a b) (.returned after out))
    exact Loops.StmtRun.sequence (Loops.SeqRun.returned hit)
      ⟨rfl,(PoolCalls.pop_same length env).symm⟩
  | false =>
    have skip1 : Run Header.layout call (.branch sameTest (.returnStmt plusReturn) .skip)
        (frame s a b) (.continuing (frame s a b)) := by
      apply Loops.StmtRun.branch equal
      simpa only [truth_boolean,hs,Bool.false_eq_true,↓reduceIte] using
        (Loops.StmtRun.skip (frame s a b) : Run Header.layout call .skip (frame s a b)
          (.continuing (frame s a b)))
    cases hl : left a b with
    | true =>
      have selected : Eval Header.layout call leftReturn (frame s a b) after out := by
        simpa only [selectedReturn,hs,hl,Bool.false_eq_true,↓reduceIte] using ret
      have hit : Run Header.layout call (.branch lessTest (.returnStmt leftReturn) .skip)
          (frame s a b) (.returned after out) := by
        apply Loops.StmtRun.branch less
        simpa only [truth_bit,hl,↓reduceIte] using
          (Loops.StmtRun.returnValue selected : Run Header.layout call (.returnStmt leftReturn)
            (frame s a b) (.returned after out))
      exact Loops.StmtRun.sequence (Loops.SeqRun.next skip1 (Loops.SeqRun.returned hit))
        ⟨rfl,(PoolCalls.pop_same length env).symm⟩
    | false =>
      have skip2 : Run Header.layout call (.branch lessTest (.returnStmt leftReturn) .skip)
          (frame s a b) (.continuing (frame s a b)) := by
        apply Loops.StmtRun.branch less
        simpa only [truth_bit,hl,Bool.false_eq_true,↓reduceIte] using
          (Loops.StmtRun.skip (frame s a b) : Run Header.layout call .skip (frame s a b)
            (.continuing (frame s a b)))
      have selected : Eval Header.layout call rightReturn (frame s a b) after out := by
        simpa only [selectedReturn,hs,hl,Bool.false_eq_true,↓reduceIte] using ret
      exact Loops.StmtRun.sequence (Loops.SeqRun.next skip1
        (Loops.SeqRun.next skip2 (Loops.SeqRun.returned (Loops.StmtRun.returnValue selected))))
        ⟨rfl,(PoolCalls.pop_same length env).symm⟩

end ScopedC.SignedAddCalls
