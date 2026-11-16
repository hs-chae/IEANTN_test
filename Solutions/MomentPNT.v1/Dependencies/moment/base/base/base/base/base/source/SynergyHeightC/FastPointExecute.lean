/- Verified reuse of actual C arithmetic function contracts. The numerical C
program, source AST, inputs, precision and mathematical model are unchanged. -/
import ScopedC.ContractExecute
import SynergyC.ComputableArithmeticService
import SynergyHeightC.SharedBackend
import SynergyHeightC.PointSemanticOutputs

namespace SynergyHeightC.FastPointExecute
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev code := Generated.functions

theorem add_installed : SynergyC.Generated.f_addU ∈ code := by
  rw [←shared_addU]
  exact (SourceCallExecute.find_sound find_addU).1

theorem mul_installed : SynergyC.Generated.f_mulU ∈ code := by
  rw [←shared_mulU]
  exact (SourceCallExecute.find_sound find_mulU).1

theorem ceil_installed : SynergyC.Generated.f_ceilDiv ∈ code := by
  rw [←shared_ceilDiv]
  exact (SourceCallExecute.find_sound find_ceilDiv).1

theorem parameters_checked : SynergyC.ArithmeticService.parameters code = true := by
  decide +kernel

theorem contract_closed {name : String} {args : List Value} {s t : State} {v : Value}
    (h : SynergyC.ComputableArithmeticService.call name args s = some (v,t)) :
    ArraySourceCalls.SourceCall SynergyC.Header.layout code 2 name args s v t :=
  SynergyC.ComputableArithmeticService.array_closed code add_installed mul_installed
    ceil_installed parameters_checked h

@[irreducible] def run (base : State) (input : ProofBox) : Option (Value × State) :=
  ContractExecute.execute SynergyC.Header.layout code 128 2048
    SynergyC.ComputableArithmeticService.call 14 "pointHeight"
    (PointExecuteAPI.args base input) (PointExecuteAPI.buffers base)

def resultCheck (base : State) (c d : ProofBox) (result : Option (Value × State)) : Bool :=
  match result with
  | none => false
  | some (value,after) =>
    StateWordEquality.valueEq 4 value .unit &&
      (PointExecuteAPI.readHasBox after (PointExecuteAPI.cAddress base) c &&
        (PointExecuteAPI.readHasBox after (PointExecuteAPI.dAddress base) d &&
          StateWordEquality.stateEq 16 after (PointExecuteAPI.filled base c d)))

def checked (base : State) (input c d : ProofBox) : Bool :=
  resultCheck base c d (run base input)

def checkedModel (base : State) (input : ProofBox) : Bool :=
  match PointExecuteAPI.modelOutputs input with
  | none => false
  | some (c,d) => checked base input c d

theorem resultCheck_sound {base : State} {c d : ProofBox} {result : Option (Value × State)}
    (h : resultCheck base c d result = true) :
    ∃ after, result = some (.unit,after) ∧
      Machine.read SynergyC.Header.layout after (PointExecuteAPI.cAddress base) =
        some (SynergyC.SourceIntervalMath.represented c) ∧
      Machine.read SynergyC.Header.layout after (PointExecuteAPI.dAddress base) =
        some (SynergyC.SourceIntervalMath.represented d) ∧
      after = PointExecuteAPI.filled {base with nats:=after.nats} c d := by
  cases result with
  | none => simp [resultCheck] at h
  | some pair =>
    rcases pair with ⟨v,after⟩
    obtain ⟨hv,rest⟩ := StateWordEquality.split_and h
    obtain ⟨hc,rest⟩ := StateWordEquality.split_and rest
    obtain ⟨hd,hs⟩ := StateWordEquality.split_and rest
    have ev : v = .unit := StateWordEquality.valueEq_sound 4 hv
    subst v
    exact ⟨after,rfl,PointExecuteAPI.readHasBox_sound hc,
      PointExecuteAPI.readHasBox_sound hd,StateWordEquality.stateEq_sound hs⟩

theorem source_outputs_of_checked {base : State} {input c d : ProofBox}
    (h : checked base input c d = true) :
    PointExecuteAPI.SourcePointOutputs base input c d := by
  obtain ⟨after,hr,hc,hd,_⟩ := resultCheck_sound h
  have run_eq : run base input = ContractExecute.execute SynergyC.Header.layout code 128 2048
      SynergyC.ComputableArithmeticService.call 14 "pointHeight"
      (PointExecuteAPI.args base input) (PointExecuteAPI.buffers base) := by
    unfold run
    rfl
  have exec := Eq.mp (congrArg (fun r => r = some (.unit,after)) run_eq) hr
  have actual : ArraySourceCalls.SourceCall SynergyC.Header.layout code 16 "pointHeight"
      (PointExecuteAPI.args base input) (PointExecuteAPI.buffers base) .unit after :=
    ContractExecute.execute_sound (fun _ _ _ _ _ hp => contract_closed hp) exec
  have boundActual : ArraySourceCalls.SourceCall SynergyC.Header.layout Bundle.code 16 "pointHeight"
      (PointExecuteAPI.args base input) (PointExecuteAPI.buffers base) .unit after :=
    Eq.mpr (congrArg (fun functions => ArraySourceCalls.SourceCall SynergyC.Header.layout functions
      16 "pointHeight" (PointExecuteAPI.args base input) (PointExecuteAPI.buffers base)
      .unit after) Bundle.code_exact) actual
  exact ⟨16,after,boundActual,hc,hd⟩

#print axioms contract_closed
#print axioms resultCheck_sound
#print axioms source_outputs_of_checked
end SynergyHeightC.FastPointExecute
