/- Turn full actual-source execution equality into same-pointer output proofs.
   All states, values, caller locals and the actual C function remain explicit. -/
import SynergyHeightC.FullMainFrame
import SynergyHeightC.FullContractPointExecute
namespace SynergyHeightC.FramedPointReplayAPI
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem read_filled_c (base : State) (c d : ProofBox) :
    Machine.read SynergyC.Header.layout (PointExecuteAPI.filled base c d)
      (PointExecuteAPI.cAddress base) = some (SynergyC.SourceIntervalMath.represented c) := by
  simp [PointExecuteAPI.filled, PointExecuteAPI.cAddress, allocate, Machine.read,
    nested, initialized, SynergyC.SourceIntervalMath.represented,
    SynergyC.ZeroBody.interval, SynergyC.Word512.value, List.getElem?_append]

theorem read_filled_d (base : State) (c d : ProofBox) :
    Machine.read SynergyC.Header.layout (PointExecuteAPI.filled base c d)
      (PointExecuteAPI.dAddress base) = some (SynergyC.SourceIntervalMath.represented d) := by
  simp [PointExecuteAPI.filled, PointExecuteAPI.dAddress, allocate, Machine.read,
    nested, initialized, SynergyC.SourceIntervalMath.represented,
    SynergyC.ZeroBody.interval, SynergyC.Word512.value, List.getElem?_append]

theorem source_of_execution {base : State} {input c d : ProofBox}
    (execution : FullContractPointExecute.run base input =
      some (.unit,PointExecuteAPI.filled base c d)) :
    PointExecuteAPI.SourcePointOutputs base input c d := by
  have run_eq : FullContractPointExecute.run base input =
      ContractExecute.execute SynergyC.Header.layout FullContractPointExecute.code 128 2048
        SynergyC.ComputableFullService.call 13 "pointHeight"
        (PointExecuteAPI.args base input) (PointExecuteAPI.buffers base) := by
    unfold FullContractPointExecute.run
    rfl
  have exec := Eq.mp (congrArg (fun result => result = some
      (.unit,PointExecuteAPI.filled base c d)) run_eq) execution
  have actual : ArraySourceCalls.SourceCall SynergyC.Header.layout
      FullContractPointExecute.code 16 "pointHeight" (PointExecuteAPI.args base input)
      (PointExecuteAPI.buffers base) .unit (PointExecuteAPI.filled base c d) :=
    ContractExecute.execute_sound
      (fun _ _ _ _ _ h => FullContractPointExecute.contract_closed h) exec
  have boundActual : ArraySourceCalls.SourceCall SynergyC.Header.layout Bundle.code 16
      "pointHeight" (PointExecuteAPI.args base input) (PointExecuteAPI.buffers base)
      .unit (PointExecuteAPI.filled base c d) :=
    Eq.mpr (congrArg (fun code => ArraySourceCalls.SourceCall SynergyC.Header.layout code 16
      "pointHeight" (PointExecuteAPI.args base input) (PointExecuteAPI.buffers base)
      .unit (PointExecuteAPI.filled base c d)) Bundle.code_exact) actual
  exact ⟨16,PointExecuteAPI.filled base c d,boundActual,read_filled_c base c d,read_filled_d base c d⟩

#print axioms source_of_execution
end SynergyHeightC.FramedPointReplayAPI
