/- Complete emitI source calls, using separately checked frame/ABI helpers. -/
import SynergyHeightC.EmitIFrames
namespace SynergyHeightC.EmitISource
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option diagnostics true
set_option maxRecDepth 100000
attribute [local irreducible] EmitUService.call EmitUService.invoke
  ScopedIO.WorldIO.stdio ScopedIO.WorldIO.external
theorem body_of_calls (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (caller : State) (box : ProofBox)
    (lo : SynergyC.Word512.Range box.lo) (hi : SynergyC.Word512.Range box.hi)
    (stream : ScopedIO.Stream) (middle after : ScopedIO.WorldIO.World)
    (first : EmitUService.call platform fault "emitU" [SynergyC.Word512.value box.lo]
      ⟨frame caller box,stream⟩=some (.unit,middle))
    (second : EmitUService.call platform fault "emitU" [SynergyC.Word512.value box.hi]
      middle=some (.unit,after)) :
    ScopedIO.WorldSource.Run SynergyC.Header.layout EmitUSource.noPure
      (EmitUService.call platform fault) platform Generated.f_emitI.body
      ⟨frame caller box,stream⟩ (.continuing ⟨frame caller box,after.stream⟩) ∧
    after.stream.accepted=stream.accepted++EmitUBuffer.bytes box.lo++EmitUBuffer.bytes box.hi := by
  have firstInvoke := first
  rw [call_word platform fault box.lo lo] at firstInvoke
  have firstOutput := EmitUService.output_correct platform fault firstInvoke
  have secondInvoke := second
  rw [call_word platform fault box.hi hi] at secondInvoke
  have secondOutput := EmitUService.output_correct platform fault secondInvoke
  have sameAfter : after.app=frame caller box := secondOutput.1.trans firstOutput.1
  have body : ScopedIO.WorldSource.Run SynergyC.Header.layout EmitUSource.noPure
      (EmitUService.call platform fault) platform Generated.f_emitI.body
      ⟨frame caller box,stream⟩ (.continuing ⟨frame caller box,after.stream⟩) := by
    apply Loops.StmtRun.sequence
    · have lowEval : ScopedIO.WorldSource.Eval SynergyC.Header.layout EmitUSource.noPure
          (EmitUService.call platform fault) platform (.field "." (.var "x") "lo")
          ⟨frame caller box,stream⟩ ⟨frame caller box,stream⟩ (SynergyC.Word512.value box.lo) :=
        .pure (read_lo EmitUSource.noPure caller box)
      have highEval : ScopedIO.WorldSource.Eval SynergyC.Header.layout EmitUSource.noPure
          (EmitUService.call platform fault) platform (.field "." (.var "x") "hi")
          middle middle (SynergyC.Word512.value box.hi) :=
        world_hi EmitUSource.noPure (EmitUService.call platform fault)
          platform middle caller box firstOutput.1
      exact Loops.SeqRun.next
        (Loops.StmtRun.evaluate (.call (.cons lowEval (.nil _)) first))
        (Loops.SeqRun.next (Loops.StmtRun.evaluate (.call (.cons highEval (.nil _)) second))
          (Loops.SeqRun.nil _))
    · change (⟨frame caller box,after.stream⟩ : ScopedIO.WorldIO.World)=
        ⟨Machine.popScope (frame caller box) after.app,after.stream⟩
      rw [sameAfter]
      simp [Machine.popScope]
  refine ⟨body,?_⟩
  rw [secondOutput.2,firstOutput.2]
#print axioms body_of_calls
end SynergyHeightC.EmitISource
