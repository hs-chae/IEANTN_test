/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexBase
import FFTComplexCapacity
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

theorem aOffset_cases (i : Fin 4) : aOffset i=0 ∨ aOffset i=6:=by unfold aOffset;split <;> omega
theorem bOffset_cases (i : Fin 4) : bOffset i=0 ∨ bOffset i=6:=by unfold bOffset;split <;> omega

theorem component_properties {F : Type} {state : State F} {input : Input}
    {ids : PVar→Nat} {owner statusId stage : Nat} {workData : Nat→Nat}
    (h : View state input ids owner statusId stage workData)
    (r : PVar) (role : r=MultiplyParameters.Var.a ∨ r=MultiplyParameters.Var.b)
    (offset : Nat) (offsetCases : offset=0 ∨ offset=6) :
    (∀k,k<5 → dataAt input workData (input.layout.object r) (input.layout.start r+offset+k)<1000000000) ∧
      dataAt input workData (input.layout.object r) (input.layout.start r+offset+5)≤1 ∧
      FFT.Limbs.magnitude 1000000000 5
        (fun k=>dataAt input workData (input.layout.object r) (input.layout.start r+offset+k))≤1000*unit ∧
      CanonicalSource.represented (dataAt input workData (input.layout.object r)) (input.layout.start r+offset)=
        CanonicalSource.represented (input.old (input.layout.object r)) (input.layout.start r+offset):=by
  have off : offset≤6:=by omega
  have values : ∀k,k<6 →
      dataAt input workData (input.layout.object r) (input.layout.start r+offset+k)=
        input.old (input.layout.object r) (input.layout.start r+offset+k):=by
    intro k hk
    simpa only [Nat.add_assoc] using h.inputValues r role (offset+k) (by omega)
  have digits : ∀k,k<5 → input.old (input.layout.object r) (input.layout.start r+offset+k)<1000000000:=by
    rcases offsetCases with rfl|rfl
    · simpa using input.digits r role (0:Fin 2)
    · simpa using input.digits r role (1:Fin 2)
  have bit : input.old (input.layout.object r) (input.layout.start r+offset+5)≤1:=by
    rcases offsetCases with rfl|rfl
    · simpa using input.signs r role (0:Fin 2)
    · simpa using input.signs r role (1:Fin 2)
  have mass : FFT.Limbs.magnitude 1000000000 5
      (fun k=>input.old (input.layout.object r) (input.layout.start r+offset+k))≤1000*unit:=by
    rcases offsetCases with rfl|rfl
    · simpa using input.magnitude r role (0:Fin 2)
    · simpa using input.magnitude r role (1:Fin 2)
  refine ⟨?_,?_,?_,represented_congr _ _ _ _ values⟩
  · intro k hk
    rw [values k (by omega)]
    exact digits k hk
  · rw [values 5 (by omega)]
    exact bit
  · have same : FFT.Limbs.magnitude 1000000000 5
        (fun k=>dataAt input workData (input.layout.object r) (input.layout.start r+offset+k))=
      FFT.Limbs.magnitude 1000000000 5 (fun k=>input.old (input.layout.object r) (input.layout.start r+offset+k)):=by
      simpa only [Nat.add_assoc] using magnitude_congr (dataAt input workData (input.layout.object r))
        (input.old (input.layout.object r)) (input.layout.start r+offset) (input.layout.start r+offset) 5 (fun k hk=>values k (by omega))
    exact same.trans_le mass

#print axioms component_properties
end RH080Next.FFTPV.ComplexSource
