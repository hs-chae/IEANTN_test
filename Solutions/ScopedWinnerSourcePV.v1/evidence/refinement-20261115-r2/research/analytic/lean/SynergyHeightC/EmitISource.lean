/- Complete emitI source calls, using separately checked frame/ABI helpers. -/
import SynergyHeightC.EmitIBody
namespace SynergyHeightC.EmitISource
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option diagnostics true
set_option maxRecDepth 100000
attribute [local irreducible] EmitUService.call EmitUService.invoke
  ScopedIO.WorldIO.stdio ScopedIO.WorldIO.external
theorem source_of_calls (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (caller : State) (box : ProofBox)
    (lo : SynergyC.Word512.Range box.lo) (hi : SynergyC.Word512.Range box.hi)
    (stream : ScopedIO.Stream) (middle after : ScopedIO.WorldIO.World)
    (first : EmitUService.call platform fault "emitU" [SynergyC.Word512.value box.lo]
      ⟨frame caller box,stream⟩=some (.unit,middle))
    (second : EmitUService.call platform fault "emitU" [SynergyC.Word512.value box.hi]
      middle=some (.unit,after)) :
    ScopedIO.WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform fault 2
      "emitI" [SynergyC.SourceIntervalMath.represented box] ⟨caller,stream⟩
      .unit ⟨caller,after.stream⟩ ∧
    after.stream.accepted=stream.accepted++EmitUBuffer.bytes box.lo++EmitUBuffer.bytes box.hi := by
  have result := body_of_calls platform fault caller box lo hi stream middle after first second
  have source := ScopedIO.WorldSource.installed_body (f:=Generated.f_emitI)
    (cfg:=SynergyC.Header.layout) (code:=Bundle.code) (p:=platform) (fault:=fault)
    (args:=[SynergyC.SourceIntervalMath.represented box])
    (s:=⟨caller,stream⟩) (t:=⟨caller,after.stream⟩) (v:=.unit)
    (frame:=frame caller box)
    (outcome:=.continuing ⟨frame caller box,after.stream⟩)
    (rank:=1) installed (pure:=EmitUSource.noPure)
    (by intro name args s v t h; contradiction)
    (service:=EmitUService.call platform fault)
    (fun _ _ _ _ _ h=>EmitUService.closed platform fault h)
    (argument caller box lo hi) result.1
    (show ScopedIO.WorldSource.Finish SynergyC.Header.layout Generated.f_emitI
      ⟨caller,stream⟩ (.continuing ⟨frame caller box,after.stream⟩)
      .unit ⟨caller,after.stream⟩ from ⟨rfl,rfl,by
        change (⟨caller,after.stream⟩ : ScopedIO.WorldIO.World)=
          ⟨Machine.popScope caller (frame caller box),after.stream⟩
        rw [pop_frame]⟩)
  exact ⟨source,result.2⟩
#print axioms source_of_calls
end SynergyHeightC.EmitISource
