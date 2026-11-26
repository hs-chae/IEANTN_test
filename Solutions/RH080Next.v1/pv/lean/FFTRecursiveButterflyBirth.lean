/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyPointers
import FFTRecursiveLoopBirth
import FFTFixedMultiplyParameters
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

inductive PointerVar where | a | b | w deriving DecidableEq

def pointerName : PointerVar → String | .a => "a" | .b => "b" | .w => "w"
def pointerType (_ : PointerVar) : CType := .pointer .u64
def pointerIds (base : Nat) : PointerVar → Nat | .a => base | .b => base+1 | .w => base+2

def pointerValue {total : Nat} (buffers : Buffers total) (start n half j : Nat) : PointerVar → Value
  | .a => .pointer (wordPointer (buffers.object .output) ((start+j)*12))
  | .b => .pointer (wordPointer (buffers.object .output) ((start+j+half)*12))
  | .w => .pointer (wordPointer (buffers.object .twiddle) ((j*(total/n))*12))

private theorem name_not_a : ∀v, loopName v ≠ "a" := by
  intro v;cases v with
  | inl v => cases v <;> decide
  | inr v => cases v <;> decide
private theorem name_not_b : ∀v, loopName v ≠ "b" := by
  intro v;cases v with
  | inl v => cases v <;> decide
  | inr v => cases v <;> decide
private theorem name_not_w : ∀v, loopName v ≠ "w" := by
  intro v;cases v with
  | inl v => cases v <;> decide
  | inr v => cases v <;> decide

/-- The source's a/b/w pointer locals are genuinely initialized by their three
actual declarations. Their lifetime owner is the real current block scope,
while all persistent function locals and buffers survive unchanged. -/
theorem butterfly_pointer_births {F : Type} (context : Context F) {before : State F}
    {total : Nat} {buffers : Buffers total} {start index step n half j owner : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : LoopView before buffers start index step n ids owner j input table output work)
    (shape : IndexShape start index step n total) (split : n=2*half) (active : j<half) :
    ∃after, ExecList context before (butterflyStatements.take 3) .normal after ∧
      LoopView after buffers start index step n ids owner j input table output work ∧
      Locals after pointerName pointerType (pointerIds before.nextObject) before.scope
        (pointerValue buffers start n half j) ∧
      Frame before.nextObject before after [] := by
  have evA := (butterfly_pointer_expressions context h shape split active).1
  have sa := MultiplyParameters.pointer_storable (buffers.object .output) ((start+j)*12)
  obtain ⟨aState,declaredA⟩ := ZeroFrame.declare_exists h.well (.pointer .u64) "a" _ sa
  have da := declare_storable sa sa.converted declaredA
  have ha := h.declare name_not_a da declaredA
  have evB := (butterfly_pointer_expressions context ha shape split active).2.1
  have sb := MultiplyParameters.pointer_storable (buffers.object .output) ((start+j+half)*12)
  obtain ⟨bState,declaredB⟩ := ZeroFrame.declare_exists ha.well (.pointer .u64) "b" _ sb
  have db := declare_storable sb sb.converted declaredB
  have hb := ha.declare name_not_b db declaredB
  have evW := (butterfly_pointer_expressions context hb shape split active).2.2
  have sw := MultiplyParameters.pointer_storable (buffers.object .twiddle) ((j*(total/n))*12)
  obtain ⟨after,declaredW⟩ := ZeroFrame.declare_exists hb.well (.pointer .u64) "w" _ sw
  have dw := declare_storable sw sw.converted declaredW
  have hw := hb.declare name_not_w dw declaredW
  have aB := slot_declare_old ha.well da.slot db
  have aW := slot_declare_old hb.well aB dw
  have bW := slot_declare_old hb.well db.slot dw
  have pointers : Locals after pointerName pointerType (pointerIds before.nextObject) before.scope
      (pointerValue buffers start n half j) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro v;cases v <;> rw [dw.environment,db.environment,da.environment] <;>
        simp [pointerName,pointerType,pointerIds,db.nextObject,da.nextObject,List.lookup,Nat.add_assoc]
    · intro v;cases v
      · exact aW
      · simpa only [pointerIds,pointerType,pointerValue,da.nextObject,da.scope] using bW
      · simpa only [pointerIds,pointerType,pointerValue,db.nextObject,da.nextObject,db.scope,da.scope,Nat.add_assoc] using dw.slot
    · intro v u same;cases v <;> cases u <;> simp_all [pointerIds] <;> omega
    · rw [dw.nextScope,db.nextScope,da.nextScope]
      exact h.well.current
  have fA := ApplicationBirthFrame.declare_frame before.nextObject [] h.well (le_refl _) declaredA
  have fB := ApplicationBirthFrame.declare_frame before.nextObject [] ha.well fA.fresh declaredB
  have fW := ApplicationBirthFrame.declare_frame before.nextObject [] hb.well fB.fresh declaredW
  refine ⟨after,?_,hw,pointers,(fA.trans fB).trans fW⟩
  change ExecList context before
    [.declare (.pointer .u64) "a" (some butterflyA),.declare (.pointer .u64) "b" (some butterflyB),
      .declare (.pointer .u64) "w" (some butterflyW)] .normal after
  exact .cons (.declareSome evA declaredA) (.cons (.declareSome evB declaredB)
    (.cons (.declareSome evW declaredW) (.nil)))

#print axioms butterfly_pointer_births
end RH080Next.FFTPV.RecursiveSource
