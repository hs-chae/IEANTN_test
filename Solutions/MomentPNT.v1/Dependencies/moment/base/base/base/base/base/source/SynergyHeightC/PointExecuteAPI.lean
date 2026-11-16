import SynergyHeightC.PointExecuteDefinitions
namespace SynergyHeightC.PointExecuteAPI
open ScopedC ScopedC.Syntax ScopedC.Machine
open ScopedNumerical ScopedNumerical.ProofBox
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem readHasBox_sound {after : State} {address : Address} {box : ProofBox}
    (h : readHasBox after address box = true) :
    Machine.read SynergyC.Header.layout after address =
      some (SynergyC.SourceIntervalMath.represented box) := by
  cases hr : Machine.read SynergyC.Header.layout after address with
  | none => simp [readHasBox,hr] at h
  | some value =>
      have hv : value = SynergyC.SourceIntervalMath.represented box :=
        SynergyC.ExecutePilot.hasBox_sound (by simpa only [readHasBox,hr] using h)
      rw [hv]


def resultChecked (base : State) (c d : ProofBox) (result : Option (Value × State)) : Bool :=
  match result with
  | none => false
  | some (value,after) =>
      StateWordEquality.valueEq 4 value .unit &&
        (readHasBox after (cAddress base) c &&
          (readHasBox after (dAddress base) d &&
            StateWordEquality.stateEq 16 after (filled base c d)))

theorem result_sound {base : State} {c d : ProofBox} {result : Option (Value × State)}
    (h : resultChecked base c d result = true) :
    ∃ after, result = some (.unit,after) ∧
      Machine.read SynergyC.Header.layout after (cAddress base) =
        some (SynergyC.SourceIntervalMath.represented c) ∧
      Machine.read SynergyC.Header.layout after (dAddress base) =
        some (SynergyC.SourceIntervalMath.represented d) ∧
      after = filled {base with nats:=after.nats} c d := by
  cases result with
  | none => simp [resultChecked] at h
  | some pair =>
      rcases pair with ⟨value,after⟩
      obtain ⟨hu,rest⟩ := StateWordEquality.split_and h
      obtain ⟨hc,rest⟩ := StateWordEquality.split_and rest
      obtain ⟨hd,hs⟩ := StateWordEquality.split_and rest
      have hu' : value = .unit := StateWordEquality.valueEq_sound 4 hu
      subst value
      exact ⟨after,rfl,readHasBox_sound hc,readHasBox_sound hd,
        StateWordEquality.stateEq_sound (fuel:=16) (a:=after) (b:=filled base c d) hs⟩

theorem source_of_checked {base : State} {input c d : ProofBox}
    (h : checked base input c d = true) :
    ∃ after, ArraySourceCalls.SourceCall SynergyC.Header.layout Bundle.code 16
      "pointHeight" (args base input) (buffers base) .unit after ∧
      Machine.read SynergyC.Header.layout after (cAddress base) =
        some (SynergyC.SourceIntervalMath.represented c) ∧
      Machine.read SynergyC.Header.layout after (dAddress base) =
        some (SynergyC.SourceIntervalMath.represented d) ∧
      after = filled {base with nats:=after.nats} c d := by
  have form : checked base input c d = resultChecked base c d (run base input) := by rfl
  have truth := Eq.mp (congrArg (fun b => b=true) form) h
  obtain ⟨after,he,hc,hd,hs⟩ := result_sound truth
  have run_eq : run base input =
      ArraySourceCallExecute.execute SynergyC.Header.layout Bundle.code 128 2048 16
        "pointHeight" (args base input) (buffers base) := by unfold run; rfl
  have exec := Eq.mp (congrArg (fun out => out=some (.unit,after)) run_eq) he
  exact ⟨after,ArraySourceCallExecute.execute_sound exec,hc,hd,hs⟩

#print axioms actual_buffer_declaration
#print axioms buffers_from_actual_declaration
#print axioms result_sound
#print axioms source_of_checked
end SynergyHeightC.PointExecuteAPI
