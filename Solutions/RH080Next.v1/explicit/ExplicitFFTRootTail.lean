/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootSimpleFrame
import FFTCanonicalFullFrame
import FFTCanonicalDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs

private theorem negative_of_nonnegative (sign : Bool) (m : Nat) (nonnegative : 0≤ signed sign m) :
    signed true m=-(signed sign m) := by
  cases sign <;> simp [signed] at * <;> omega

theorem force_negative_fixed {data : Nat → Nat} {start : Nat} {value : Int}
    (h : FixedValue data start value) (nonnegative : 0≤ value) :
    FixedValue (Function.update data (start+5) 1) start (-value) := by
  have magnitudeSame : magnitude 1000000000 5 (fun k=>(Function.update data (start+5) 1) (start+k))=
      magnitude 1000000000 5 (fun k=>data (start+k)):=by
    apply Finset.sum_congr rfl
    intro k hk
    change (Function.update data (start+5) 1) (start+k)*_=data (start+k)*_
    rw [Function.update_of_ne (show start+k≠start+5 by have hk:=Finset.mem_range.mp hk;omega)]
  have signSame : decide ((Function.update data (start+5) 1) (start+5)≠0)=true:=by simp
  have represented : CanonicalSource.represented (Function.update data (start+5) 1) start=
      signed true (magnitude 1000000000 5 (fun k=>data (start+k))):=
    congrArg₂ signed signSame magnitudeSame
  have rawNonnegative : 0≤ CanonicalSource.represented data start:=by rw [h.represented];exact nonnegative
  refine ⟨?_,by simp,represented.trans ((negative_of_nonnegative _ _ rawNonnegative).trans (congrArg Neg.neg h.represented))⟩
  intro k hk
  rw [Function.update_of_ne (show start+k≠start+5 by omega)]
  exact h.digits k hk

theorem FixedValue.canonical {data : Nat → Nat} {start : Nat} {value : Int} (h : FixedValue data start value) :
    FixedValue (CanonicalSource.canonicalData data start) start value := by
  refine ⟨?_,?_,(CanonicalSource.canonicalData_preserves data start).trans h.represented⟩
  · intro k hk;rw [CanonicalSource.canonicalData_digit _ _ k hk];exact h.digits k hk
  · rw [CanonicalSource.canonicalData_sign];split_ifs
    · omega
    · exact h.sign

def tailStatements : List Stmt:=[finalSignStatement,finalCanonicalStatement,returnStatusStatement]

/-- The actual final negative-imaginary sign store, source canonicalization and
returned status0. The true twelve memory words decode to the existing root
integer model; the source does not receive a precomputed root as an input. -/
theorem tail_execution {F : Type} (context : Context F) (functions : Functions context)
    {before : State F} {input : Input} {owner statusId indexId : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data 11)
    (tracked : Tracked input data (regionValue input.n 10)) (grid : OriginalGrid input.n) :
    ∃after finalData,ExecList context before tailStatements (.returned (.integer (integer64 0))) after ∧
      EveryList context before tailStatements (.returned (.integer (integer64 0))) after ∧
      ScaleView after input owner statusId ids finalData ∧
      FixedValue finalData input.layout.rootStart (taylorState input.n 10).cr ∧
      FixedValue finalData (input.layout.rootStart+6) (-(taylorState input.n 10).sr) ∧
      (CanonicalSource.represented finalData input.layout.rootStart,CanonicalSource.represented finalData (input.layout.rootStart+6))=
        FFT.IntegerModel.root input.n ∧
      IncrementSource.FullCallerFrame before after input.layout.object ∧
      ∀k,(k< input.layout.rootStart ∨ input.layout.rootStart+12≤ k) → finalData k=data k := by
  have rootBound:=input.layout.rootBound
  obtain ⟨s1,run1,every1,view1,frame1⟩:=literal_store_framed context h.view .root (Or.inl rfl) 11 1
    (by simp only [pointerStart];omega) (by norm_num) (by norm_num)
  let data1:=Function.update data (input.layout.rootStart+11) 1
  obtain ⟨ct0,ct1,st0,st1,cr0,cr1,sr0,sr1⟩:=original_recurrence_bounds input.n 10 grid (by omega)
  have srNegative : FixedValue data1 (input.layout.rootStart+6) (-(taylorState input.n 10).sr):=by
    simpa only [data1,regionStart,regionValue,Nat.add_assoc] using force_negative_fixed (tracked .sr) sr0
  have cr : FixedValue data1 input.layout.rootStart (taylorState input.n 10).cr:=by
    apply (tracked .cr).congr
    intro k hk
    exact Function.update_of_ne (show input.layout.rootStart+k≠input.layout.rootStart+11 by omega) _ _
  obtain ⟨after,called,post,frame2⟩:=CanonicalSource.canonical_sign_call_framed context functions.canonical s1
    input.layout.object input.layout.size (input.layout.rootStart+6) data1 view1.params.well view1.params.array (by omega) srNegative.digits
  have args : Args context s1 [pointerExpr .root 6] [.pointer (wordPointer input.layout.object (input.layout.rootStart+6))] s1:=by
    apply Args.ordered (order:=[(0,pointerExpr .root 6)])
      (evaluated:=[(0,.pointer (wordPointer input.layout.object (input.layout.rootStart+6)))])
    · exact List.Perm.refl _
    · exact .cons (pointer_eval context view1.params .root (Or.inl rfl) 6 (by simp only [pointerStart];omega) (by norm_num)) .nil
    · change List.Forall₂ _ [0] _;exact .cons rfl .nil
  have view:=view1.reframe post frame2.environment (by rw [frame1.scope];exact h.active) frame2.scope frame2.well frame2.objects
  let finalData:=CanonicalSource.canonicalData data1 (input.layout.rootStart+6)
  have finalSr : FixedValue finalData (input.layout.rootStart+6) (-(taylorState input.n 10).sr):=srNegative.canonical
  have finalCr : FixedValue finalData input.layout.rootStart (taylorState input.n 10).cr:=by
    apply cr.congr
    intro k hk
    unfold finalData CanonicalSource.canonicalData
    split_ifs <;> simp [Function.update_of_ne (show input.layout.rootStart+k≠input.layout.rootStart+6+5 by omega)]
  have sourceRun : ExecList context before tailStatements (.returned (.integer (integer64 0))) after:=
    .cons run1 (.cons (.expression (.call args called)) (.abrupt (.returnSome (.variable view.statusLookup view.status.read)) (by simp)))
  have every2 : Every context s1 finalCanonicalStatement .normal after:=by
    apply every_expression_call (expressions:=[pointerExpr .root 6])
      (by intro e he;simp only [List.mem_singleton] at he;subst e;exact pointer_expr_pure .root 6) args
    intro state result execution
    exact CanonicalSource.call_unique functions.canonical called execution
  have every3 : Every context after returnStatusStatement (.returned (.integer (integer64 0))) after:=
    every_pure (by constructor)
      (.returnSome (.variable view.statusLookup view.status.read))
  have everyTail : EveryList context before tailStatements (.returned (.integer (integer64 0))) after:=
    every_cons every1 (every_cons every2 (every_abrupt every3 (by simp)))
  have secondFrame : IncrementSource.FullCallerFrame s1 after input.layout.object:=
    ⟨⟨frame2.environment,frame2.scope,frame2.foreign,frame2.well,frame2.objects⟩,frame2.nextObject,frame2.nextScope,frame2.mode⟩
  refine ⟨after,finalData,sourceRun,everyTail,view,finalCr,finalSr,?_,full_caller_trans frame1 secondFrame,?_⟩
  · rw [finalCr.represented,finalSr.represented];exact taylorState_root input.n
  · intro k outside
    have different : k≠input.layout.rootStart+11:=by omega
    unfold finalData CanonicalSource.canonicalData
    split_ifs <;> simp [data1,Function.update_of_ne different,Nat.add_assoc]

#print axioms force_negative_fixed
#print axioms tail_execution
end RH080Next.FFTPV.RootSource
