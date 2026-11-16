/- Faster proof evaluation by eleven already verified C function contracts.
The actual numerical C source, arithmetic, inputs and outputs are unchanged. -/
import SynergyHeightC.FastPointExecute
import SynergyC.ComputableFullService
namespace SynergyHeightC.FullContractPointExecute
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
abbrev code := Generated.functions
theorem installed_zero : SynergyC.Generated.f_zero ∈ code := by
  rw [←shared_zero]
  exact (SourceCallExecute.find_sound find_zero).1
theorem installed_unit : SynergyC.Generated.f_unit ∈ code := by
  rw [←shared_unit]
  exact (SourceCallExecute.find_sound find_unit).1
theorem installed_add : SynergyC.Generated.f_add ∈ code := by
  rw [←shared_add]
  exact (SourceCallExecute.find_sound find_add).1
theorem installed_mul : SynergyC.Generated.f_mul ∈ code := by
  rw [←shared_mul]
  exact (SourceCallExecute.find_sound find_mul).1
theorem installed_divI : SynergyC.Generated.f_divI ∈ code := by
  rw [←shared_divI]
  exact (SourceCallExecute.find_sound find_divI).1
theorem installed_divN : SynergyC.Generated.f_divN ∈ code := by
  rw [←shared_divN]
  exact (SourceCallExecute.find_sound find_divN).1
theorem installed_positiveSub : SynergyC.Generated.f_positiveSub ∈ code := by
  rw [←shared_positiveSub]
  exact (SourceCallExecute.find_sound find_positiveSub).1
theorem installed_rat : SynergyC.Generated.f_rat ∈ code := by
  rw [←shared_rat]
  exact (SourceCallExecute.find_sound find_rat).1
theorem installed_addU : SynergyC.Generated.f_addU ∈ code := by
  rw [←shared_addU]
  exact (SourceCallExecute.find_sound find_addU).1
theorem installed_mulU : SynergyC.Generated.f_mulU ∈ code := by
  rw [←shared_mulU]
  exact (SourceCallExecute.find_sound find_mulU).1
theorem installed_ceilDiv : SynergyC.Generated.f_ceilDiv ∈ code := by
  rw [←shared_ceilDiv]
  exact (SourceCallExecute.find_sound find_ceilDiv).1
theorem arithmetic_parameters : SynergyC.ArithmeticService.parameters code=true := by decide +kernel
theorem mixed_parameters : SynergyC.ComputableIntervalService.parameters code=true := by decide +kernel

def library : SynergyC.ComputableIntervalService.Library code := {
  zero := installed_zero
  unit := installed_unit
  add := installed_add
  mul := installed_mul
  divI := installed_divI
  divN := installed_divN
  positiveSub := installed_positiveSub
  rat := installed_rat
  addU := installed_addU
  mulU := installed_mulU
  ceilDiv := installed_ceilDiv
  arithmeticParameters := arithmetic_parameters
  mixedParameters := mixed_parameters}
theorem contract_closed {name : String} {args : List Value} {s t : State} {v : Value}
    (h : SynergyC.ComputableFullService.call name args s=some (v,t)) :
    ArraySourceCalls.SourceCall SynergyC.Header.layout code 3 name args s v t :=
  SynergyC.ComputableFullService.array_closed code library h

@[irreducible] def run (base : State) (input : ProofBox) : Option (Value × State) :=
  ContractExecute.execute SynergyC.Header.layout code 128 2048
    SynergyC.ComputableFullService.call 13 "pointHeight"
    (PointExecuteAPI.args base input) (PointExecuteAPI.buffers base)

def checked (base : State) (input c d : ProofBox) : Bool :=
  FastPointExecute.resultCheck base c d (run base input)
def checkedModel (base : State) (input : ProofBox) : Bool :=
  match PointExecuteAPI.modelOutputs input with
  | none => false
  | some (c,d) => checked base input c d

theorem source_outputs_of_checked {base : State} {input c d : ProofBox}
    (h : checked base input c d=true) : PointExecuteAPI.SourcePointOutputs base input c d := by
  obtain ⟨after,hr,hc,hd,_⟩ := FastPointExecute.resultCheck_sound h
  have run_eq : run base input = ContractExecute.execute SynergyC.Header.layout code 128 2048
      SynergyC.ComputableFullService.call 13 "pointHeight"
      (PointExecuteAPI.args base input) (PointExecuteAPI.buffers base) := by
    unfold run
    rfl
  have exec := Eq.mp (congrArg (fun r=>r=some (.unit,after)) run_eq) hr
  have actual : ArraySourceCalls.SourceCall SynergyC.Header.layout code 16 "pointHeight"
      (PointExecuteAPI.args base input) (PointExecuteAPI.buffers base) .unit after :=
    ContractExecute.execute_sound (fun _ _ _ _ _ hp=>contract_closed hp) exec
  have boundActual : ArraySourceCalls.SourceCall SynergyC.Header.layout Bundle.code 16 "pointHeight"
      (PointExecuteAPI.args base input) (PointExecuteAPI.buffers base) .unit after :=
    Eq.mpr (congrArg (fun functions=>ArraySourceCalls.SourceCall SynergyC.Header.layout functions
      16 "pointHeight" (PointExecuteAPI.args base input) (PointExecuteAPI.buffers base)
      .unit after) Bundle.code_exact) actual
  exact ⟨16,after,boundActual,hc,hd⟩

theorem source_outputs_of_checkedModel {base : State} {input : ProofBox}
    (h : checkedModel base input=true) :
    ∃ c d, PointExecuteAPI.modelOutputs input=some (c,d) ∧
      PointExecuteAPI.SourcePointOutputs base input c d := by
  cases hm : PointExecuteAPI.modelOutputs input with
  | none => simp [checkedModel,hm] at h
  | some pair =>
    rcases pair with ⟨c,d⟩
    have hc : checked base input c d=true := by simpa only [checkedModel,hm] using h
    exact ⟨c,d,rfl,source_outputs_of_checked hc⟩
#print axioms contract_closed
#print axioms source_outputs_of_checkedModel
end SynergyHeightC.FullContractPointExecute
