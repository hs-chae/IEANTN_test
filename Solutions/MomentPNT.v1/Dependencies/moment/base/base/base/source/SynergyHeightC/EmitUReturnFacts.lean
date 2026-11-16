/- Checked actual emitU summaries expose their input domain and exact effects. -/
import SynergyHeightC.EmitIFrames
namespace SynergyHeightC.EmitUReturnFacts
open ScopedC ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

theorem call_word_output (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (x : Int)
    (world after : ScopedIO.WorldIO.World) (v : Value)
    (accepted : EmitUService.call platform fault "emitU" [SynergyC.Word512.value x]
      world=some (v,after)) :
    SynergyC.Word512.Range x ∧ after.app=world.app ∧
      after.stream.accepted=world.stream.accepted++EmitUBuffer.bytes x := by
  have range : SynergyC.Word512.Range x := by
    unfold EmitUService.call at accepted
    simp only [SynergyC.Word512.value,SynergyC.Word512.word,↓reduceIte] at accepted
    split at accepted
    · rename_i valid
      exact valid.2
    · contradiction
  have invoke := accepted
  rw [EmitISource.call_word platform fault x range] at invoke
  exact ⟨range,EmitUService.output_correct platform fault invoke⟩

#print axioms call_word_output
end SynergyHeightC.EmitUReturnFacts
