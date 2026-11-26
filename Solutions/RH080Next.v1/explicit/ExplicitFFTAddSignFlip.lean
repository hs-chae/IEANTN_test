/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddInitialize
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

theorem preValues_bs_update (input : Input) (a b : Nat) :
    Function.update (preValues input a) .bsign (.integer (integer64 b))=preValues input b := by
  funext v; cases v <;> rfl

theorem flip_test_eval {F : Type} (context : Context F) {state : State F} {input : Input}
    {owner bs : Nat} {pi : PreVar → Nat} (h : PreView state input owner pi bs) :
    Eval context state flipTest (.integer (.boolean (decide (0 < input.subtract)))) state :=
  .binaryLR (.variable (h.locals.lookup PreVar.subtract) (h.locals.read PreVar.subtract))
    (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
    (by simp only [preValues,binary,CompareSource.binary64_gt input.subtract 0 (by have hs:=input.subtract_bound; omega)
      (by norm_num),Option.map_some])

/-- Actual optional subtraction-sign adjustment. Its temporary branch scope
does not own bs: the source writes the already initialized function local. -/
theorem flip_sign_execution {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner : Nat} {pi : PreVar → Nat}
    (h : PreView before input owner pi (input.old (input.layout.object .b) (input.layout.start .b+5))) :
    ∃after,Exec context before flipBranch .normal after ∧ PreView after input owner pi input.bsign ∧
      ApplicationBirthFrame.Frame before.nextObject before after [pi .bsign] := by
  let bs:=input.old (input.layout.object .b) (input.layout.start .b+5)
  by_cases hc : 0 < input.subtract
  · have bBound : bs ≤ 1:=input.signB
    have target64 : 1-bs < 2^64:=by omega
    have storable:=ZeroFrame.u64_storable (1-bs) target64
    obtain ⟨middle,stored⟩:=IncrementSource.slot_store_exists (h.enter.locals.slots PreVar.bsign) (.integer (integer64 (1-bs))) storable
    have readB : Eval context before.enterScope (.variable "bs") (.integer (integer64 bs)) before.enterScope:=
      .variable (h.enter.locals.lookup PreVar.bsign) (h.enter.locals.read PreVar.bsign)
    have run : Exec context before.enterScope flipSign .normal middle:=
      .assign (Eval.paren (.binaryLR (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl)) readB
        (congrArg (Option.map Value.integer) (binary64_one_sub bs bBound))))
        (Place.variable (h.enter.locals.lookup PreVar.bsign)) stored
    have lm : Locals middle preName preType pi owner (preValues input (1-bs)):=by
      simpa only [preValues_bs_update] using h.enter.locals.store PreVar.bsign _ storable stored
    have am : ∀r,WordArrayRep middle (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r)):=
      fun r=>IncrementSource.array_store_other (h.enter.arrays r) (h.separate r PreVar.bsign) stored
    have fr:=ApplicationBirthFrame.store_frame before.nextObject [pi .bsign] h.enter.well (le_refl _)
      (Or.inl (by simp [scalarPointer])) stored
    have frame:=ApplicationBirthFrame.close_frame h.well (le_refl _) fr
    let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
    have different : before.nextScope≠owner:=by have ho:=h.locals.bound; omega
    have locals:=lm.leave different before.environment h.locals.lookup before.scope
    have post : PreView after input owner pi (1-bs):=
      ⟨fun r=>IncrementSource.wordArray_leave (am r),locals,h.separate,frame.well⟩
    refine ⟨after,.ifTrue (flip_test_eval context h) ?_ (.block (by rfl) (.cons run .nil) (by rfl)),?_,frame⟩
    · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hc]
    · simpa only [Input.bsign,if_pos hc,bs] using post
  · refine ⟨before,.ifFalse (flip_test_eval context h) ?_,?_,ApplicationBirthFrame.Frame.refl _ _ h.well (le_refl _)⟩
    · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hc]
    · simpa only [Input.bsign,if_neg hc] using h

#print axioms flip_sign_execution
end RH080Next.FFTPV.AddSource
