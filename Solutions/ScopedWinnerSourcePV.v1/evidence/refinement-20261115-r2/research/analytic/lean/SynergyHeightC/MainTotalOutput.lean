/- The actual final total memory read is the argument to the actual emitI source.
Accepted bytes are distinguished from a later successful flush/delivery. -/
import SynergyHeightC.MainWorldLoop
import SynergyHeightC.EmitIService
namespace SynergyHeightC.MainTotalOutput
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

theorem read_total (service : Machine.Call) (total : ProofBox) (i : Nat) :
    evalExpr SynergyC.Header.layout service 1 (FullMainEdges.loopState total i) (.var "total")=
      some (SynergyC.SourceIntervalMath.represented total,FullMainEdges.loopState total i) := by
  simp [evalExpr,Machine.getVar,FullMainEdges.loopState,Machine.allocate,Machine.read,
    Machine.nested,Machine.initialized,List.lookup,SynergyC.SourceIntervalMath.represented,
    SynergyC.ZeroBody.interval,SynergyC.Word512.value]

theorem represented_injective : Function.Injective SynergyC.SourceIntervalMath.represented := by
  intro a b same
  have lo := congrArg (fun v : Value=>match v with
    | .record _ [.integer l,.integer _]=>l.number
    | _=>0) same
  have hi := congrArg (fun v : Value=>match v with
    | .record _ [.integer _,.integer h]=>h.number
    | _=>0) same
  change a.lo=b.lo at lo
  change a.hi=b.hi at hi
  cases a
  cases b
  cases lo
  cases hi
  rfl

theorem call_represented (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (box : ProofBox)
    (lo : SynergyC.Word512.Range box.lo) (hi : SynergyC.Word512.Range box.hi)
    (world : ScopedIO.WorldIO.World) :
    EmitIService.call platform fault "emitI" [SynergyC.SourceIntervalMath.represented box] world=
      EmitIService.invoke platform fault box world := by
  have valid : 0≤box.lo ∧ box.lo<2^512 ∧ 0≤box.hi ∧ box.hi<2^512 :=
    ⟨lo.1,lo.2,hi.1,hi.2⟩
  simp [EmitIService.call,SynergyC.SourceIntervalMath.represented,
    SynergyC.ZeroBody.interval,SynergyC.ComputableIntervalInput.interval?,
    SynergyC.Word512.value,SynergyC.Word512.word,↓reduceIte,
    Bind.bind,Option.bind,valid]

theorem actual_emitI (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (total : ProofBox) (i : Nat)
    (lo : SynergyC.Word512.Range total.lo) (hi : SynergyC.Word512.Range total.hi)
    (stream : ScopedIO.Stream) {after : ScopedIO.WorldIO.World} {v : Value}
    (accepted : EmitIService.call platform fault "emitI"
      [SynergyC.SourceIntervalMath.represented total]
      ⟨FullMainEdges.loopState total i,stream⟩=some (v,after)) :
    ScopedIO.WorldSource.Eval SynergyC.Header.layout FullMainPrefix.service
      (EmitIService.call platform fault) platform (.call (.var "emitI") [.var "total"])
      ⟨FullMainEdges.loopState total i,stream⟩ after v ∧
    after.app=FullMainEdges.loopState total i ∧
    after.stream.accepted=stream.accepted++EmitUBuffer.bytes total.lo++EmitUBuffer.bytes total.hi := by
  have expression : ScopedIO.WorldSource.Eval SynergyC.Header.layout FullMainPrefix.service
      (EmitIService.call platform fault) platform (.call (.var "emitI") [.var "total"])
      ⟨FullMainEdges.loopState total i,stream⟩ after v := ScopedIO.WorldSource.Eval.call
    (ScopedIO.WorldSource.Arguments.cons
      (ScopedIO.WorldSource.Eval.pure (read_total FullMainPrefix.service total i))
      (ScopedIO.WorldSource.Arguments.nil _)) accepted
  rw [call_represented platform fault total lo hi] at accepted
  exact ⟨expression,EmitIService.invoke_output platform fault lo hi accepted⟩

#print axioms read_total
#print axioms represented_injective
#print axioms call_represented
#print axioms actual_emitI
end SynergyHeightC.MainTotalOutput
