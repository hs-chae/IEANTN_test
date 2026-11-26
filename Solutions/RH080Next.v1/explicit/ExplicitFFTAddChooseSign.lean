/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddSignStore
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

theorem Input.bsign_bound (i : Input) : i.bsign ≤ 1 := by
  unfold Input.bsign
  split_ifs
  · exact Nat.sub_le 1 _
  · exact i.signB

def signName (_ : Unit) : String:="sign"
def signType (_ : Unit) : CType:=.u64
def signValues (s : Nat) (_ : Unit) : Value:=.integer (integer64 s)

def SignLocal {F : Type} (state : State F) (id owner sign : Nat) : Prop:=
  Locals state signName signType (fun _ : Unit=>id) owner (signValues sign)

theorem signValues_update (a b : Nat) : Function.update (signValues a) () (.integer (integer64 b))=signValues b := by
  funext u
  cases u
  rfl

/-- Actual subtraction-branch sign choice, with the branch-local sign slot
kept distinct from the existing function locals and all numeric arrays. -/
theorem choose_sign_execution {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner j signId signOwner cutoff : Nat} {li : Var → Nat}
    (h : View before input true (decide (input.cmp=0)) owner li j)
    (sign : SignLocal before signId signOwner input.asign) (different : ∀v,li v≠signId)
    (born : cutoff ≤ signId) (fresh : cutoff ≤ before.nextObject) :
    ∃after,Exec context before chooseSign .normal after ∧
      View after input true (decide (input.cmp=0)) owner li j ∧
      SignLocal after signId signOwner (if input.cmp=0 then input.bsign else input.asign) ∧
      ApplicationBirthFrame.Frame cutoff before after (writes input li) := by
  by_cases he : input.cmp=0
  · have storable:=ZeroFrame.u64_storable input.bsign (lt_of_le_of_lt input.bsign_bound (by norm_num))
    obtain ⟨middle,stored⟩:=IncrementSource.slot_store_exists (sign.enter.slots ()) (.integer (integer64 input.bsign)) storable
    have run : Exec context before.enterScope (.assign (.variable "sign") (.variable "bs")) .normal middle:=
      .assign (.variable (h.enter.locals.lookup Var.bsign) (h.enter.locals.read Var.bsign))
        (Place.variable (sign.enter.lookup ())) stored
    have lm:=ApplicationBirthFrame.locals_store_other h.enter.locals different stored
    have am:=h.enter.arrays.store_other (fun r=>(scalar_array_ne (sign.enter.slots ()) (h.enter.arrays r)).symm) stored
    have sm : SignLocal middle signId signOwner input.bsign:=by
      simpa only [SignLocal,signValues_update] using sign.enter.store () _ storable stored
    have bodyFrame:=ApplicationBirthFrame.store_frame cutoff (writes input li) h.enter.well fresh (Or.inr born) stored
    have frame:=ApplicationBirthFrame.close_frame h.well fresh bodyFrame
    let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
    have mainDifferent : before.nextScope≠owner:=by have ho:=h.locals.bound; omega
    have signDifferent : before.nextScope≠signOwner:=by have ho:=sign.bound; omega
    have post : View after input true (decide (input.cmp=0)) owner li j:=
      ⟨am.leave,lm.leave mainDifferent before.environment h.locals.lookup before.scope,h.separate,h.active,frame.well⟩
    have signPost : SignLocal after signId signOwner input.bsign:=
      sm.leave signDifferent before.environment sign.lookup before.scope
    refine ⟨after,.ifTrue (cmp_eval context h) ?_ (.block (by rfl) (.cons run .nil) (by rfl)),post,?_,frame⟩
    · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,he]
    · simpa only [if_pos he] using signPost
  · refine ⟨before,.ifFalse (cmp_eval context h) ?_,h,?_,ApplicationBirthFrame.Frame.refl _ _ h.well fresh⟩
    · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,he]
    · simpa only [if_neg he] using sign

#print axioms choose_sign_execution
end RH080Next.FFTPV.AddSource
