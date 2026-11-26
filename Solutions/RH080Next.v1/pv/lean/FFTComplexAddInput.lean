/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexAddLayout
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

private theorem work_component_bound (input : Input) (i : Fin 4) (k : Nat) (hk : k<6) :
    input.layout.start .work+6*i.val+k< input.layout.length (input.layout.object .work):=by
  have bound:=input.layout.bound MultiplyParameters.Var.work
  simp at bound
  have ib:=i.isLt
  omega

def sumInput {F : Type} {state : State F} {input : Input} {ids : PVar→Nat}
    {owner statusId stage : Nat} {workData outData : Nat→Nat}
    (h : SumView state input ids owner statusId stage workData outData) (part : Fin 2) : AddSource.Input where
  layout:=sumLayout input part
  old:=sumData input workData outData
  subtract:=if part.val=0 then 1 else 0
  subtract_bound:=by split <;> omega
  digitsA:=by
    intro k hk
    change sumData input workData outData (input.layout.object .work) (input.layout.start .work+6*(leftProduct part).val+k)<1000000000
    rw [sum_data_work_value h (work_component_bound input _ _ (by omega))]
    exact (h.products (leftProduct part)).2.1 k hk
  digitsB:=by
    intro k hk
    change sumData input workData outData (input.layout.object .work) (input.layout.start .work+6*(rightProduct part).val+k)<1000000000
    rw [sum_data_work_value h (work_component_bound input _ _ (by omega))]
    exact (h.products (rightProduct part)).2.1 k hk
  signA:=by
    change sumData input workData outData (input.layout.object .work) (input.layout.start .work+6*(leftProduct part).val+5)≤1
    rw [sum_data_work_value h (work_component_bound input _ _ (by omega))]
    exact (h.products (leftProduct part)).2.2
  signB:=by
    change sumData input workData outData (input.layout.object .work) (input.layout.start .work+6*(rightProduct part).val+5)≤1
    rw [sum_data_work_value h (work_component_bound input _ _ (by omega))]
    exact (h.products (rightProduct part)).2.2

theorem sum_input_reps {F : Type} {state : State F} {input : Input} {ids : PVar→Nat}
    {owner statusId stage : Nat} {workData outData : Nat→Nat}
    (h : SumView state input ids owner statusId stage workData outData) (part : Fin 2) :
    ∀r,WordArrayRep state ((sumInput h part).layout.object r)
      ((sumInput h part).layout.length ((sumInput h part).layout.object r))
      ((sumInput h part).old ((sumInput h part).layout.object r)):=by
  intro r
  cases r with
  | out=>simpa [sumInput,sumLayout,sumObject,sumData] using h.output
  | a=>exact sum_data_work_rep h
  | b=>exact sum_data_work_rep h

theorem product_magnitude_bound {F : Type} {state : State F} {input : Input} {ids : PVar→Nat}
    {owner statusId stage : Nat} {workData outData : Nat→Nat}
    (h : SumView state input ids owner statusId stage workData outData) (i : Fin 4) :
    FFT.Limbs.magnitude 1000000000 5 (fun k=>workData (input.layout.start .work+6*i.val+k))≤1000000*unit+1:=by
  have am : FFT.Limbs.magnitude 1000000000 5 (fun k=>input.old (input.layout.object .a) (input.layout.start .a+aOffset i+k))≤1000*unit:=by
    rcases aOffset_cases i with eq|eq <;> rw [eq]
    · simpa using input.magnitude .a (Or.inl rfl) (0:Fin 2)
    · simpa using input.magnitude .a (Or.inl rfl) (1:Fin 2)
  have bm : FFT.Limbs.magnitude 1000000000 5 (fun k=>input.old (input.layout.object .b) (input.layout.start .b+bOffset i+k))≤1000*unit:=by
    rcases bOffset_cases i with eq|eq <;> rw [eq]
    · simpa using input.magnitude .b (Or.inr rfl) (0:Fin 2)
    · simpa using input.magnitude .b (Or.inr rfl) (1:Fin 2)
  have scale : (1000000000^4:Nat)=unit:=by norm_num [unit]
  exact rounded_product_magnitude_bound _ _ _ _ _ _ am bm (by simpa only [scale,productValue] using (h.products i).1)

theorem sum_input_status_zero {F : Type} {state : State F} {input : Input} {ids : PVar→Nat}
    {owner statusId stage : Nat} {workData outData : Nat→Nat}
    (h : SumView state input ids owner statusId stage workData outData) (part : Fin 2) :
    AddSource.rawStatus (sumInput h part)=0:=by
  have left : FFT.Limbs.magnitude 1000000000 5 (sumInput h part).a=
      FFT.Limbs.magnitude 1000000000 5 (fun k=>workData (input.layout.start .work+6*(leftProduct part).val+k)):=by
    apply Finset.sum_congr rfl
    intro k hk
    change sumData input workData outData (input.layout.object .work) (input.layout.start .work+6*(leftProduct part).val+k)*1000000000^k=_
    rw [sum_data_work_value h (work_component_bound input _ _ (by have hb:=Finset.mem_range.mp hk;omega))]
  have right : FFT.Limbs.magnitude 1000000000 5 (sumInput h part).b=
      FFT.Limbs.magnitude 1000000000 5 (fun k=>workData (input.layout.start .work+6*(rightProduct part).val+k)):=by
    apply Finset.sum_congr rfl
    intro k hk
    change sumData input workData outData (input.layout.object .work) (input.layout.start .work+6*(rightProduct part).val+k)*1000000000^k=_
    rw [sum_data_work_value h (work_component_bound input _ _ (by have hb:=Finset.mem_range.mp hk;omega))]
  apply AddSource.rawStatus_zero_of_sum_lt
  rw [show IncrementSource.base=1000000000 from rfl,left,right]
  exact sum_products_fits _ _ (product_magnitude_bound h (leftProduct part)) (product_magnitude_bound h (rightProduct part))

#print axioms sumInput
#print axioms sum_input_reps
#print axioms product_magnitude_bound
#print axioms sum_input_status_zero
end RH080Next.FFTPV.ComplexSource
