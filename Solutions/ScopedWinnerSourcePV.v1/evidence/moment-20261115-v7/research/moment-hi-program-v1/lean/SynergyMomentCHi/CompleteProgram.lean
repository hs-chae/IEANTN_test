/- Complete actual moment entries in the explicit successful-stdio model.
All application initialization/768rows/suffix guards/output/flush/return are proved.
Actual host run and generic compiler/CRT/ABI applicability are separate receipts. -/
import SynergyMomentCHi.AllRows
import SynergyMomentCHi.WorldCall
import SynergyHeightC.MainComputedGlobals
namespace SynergyMomentCHi.CompleteProgram
open ScopedC ScopedC.Machine ScopedNumerical ScopedIO SynergyHeightC SynergyMomentC
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
noncomputable section

theorem final_range (kind : Kind) :
 SynergyC.SourceIntervalMath.representable (FamilyAPI.total kind 768) := by
 cases kind with
 | mass=>
  change SynergyC.SourceIntervalMath.representable (SourceMomentSumsV1.Data.total .mass 768)
  rw [SourceMomentSumsV1.Data.mass_final]
  unfold SynergyC.SourceIntervalMath.representable SynergyC.Word512.Range
  decide +kernel
 | firstMoment=>
  change SynergyC.SourceIntervalMath.representable (SourceMomentSumsV1.Data.total .firstMoment 768)
  rw [SourceMomentSumsV1.Data.first_moment_final]
  unfold SynergyC.SourceIntervalMath.representable SynergyC.Word512.Range
  decide +kernel

theorem complete (kind : Kind) (platform : WorldIO.Platform) (initial : Stream) :
 ∃ (trace : Nat→Stream) (final : WorldIO.World) (out : ProofBox),
  trace 0=initial ∧
  WorldSource.SourceCall SynergyC.Header.layout (code kind) platform CompleteIOModel.policy
   3 "__wrap_main" [] ⟨Initialization.initializeBoundGlobals.getD Machine.empty,initial⟩
   (WorldIO.signed32 0) ⟨FullMainPrefix.cache,final.stream⟩ ∧
  evalExpr SynergyC.Header.layout FullMainPrefix.service 1
   (FullMainEdges.loopState (FamilyAPI.total kind 768) 768) (.var "total")=
   some (SynergyC.SourceIntervalMath.represented out,
    FullMainEdges.loopState (FamilyAPI.total kind 768) 768) ∧
  final.stream.accepted=(trace 768).accepted++
   EmitUBuffer.bytes out.lo++EmitUBuffer.bytes out.hi ∧
  final.stream.delivered=final.stream.accepted.length := by
 let trace:=MainIOTrace.streams initial
 let total:=FamilyAPI.total kind 768
 let state:=FullMainEdges.loopState total 768
 let emitted : WorldIO.World:=⟨state,CompleteIOModel.appendWord
   (CompleteIOModel.appendWord (trace 768) total.lo) total.hi⟩
 let final : WorldIO.World:=⟨emitted.app,
   {emitted.stream with delivered:=emitted.stream.accepted.length}⟩
 have ranges:=final_range kind
 have emit : EmitIService.call platform CompleteIOModel.policy "emitI"
   [SynergyC.SourceIntervalMath.represented total] ⟨state,trace 768⟩=some (.unit,emitted) :=
  CompleteIOModel.emitI_success platform state total ranges (trace 768) rfl
 have flush : WorldIO.stdio platform CompleteIOModel.policy "fflush"
   [WorldIO.stdoutValue platform] emitted=some (WorldIO.signed32 0,final) :=
  CompleteIOModel.flush_success platform emitted
 have source:=WorldCall.source_main kind platform CompleteIOModel.policy (FamilyAPI.total kind)
  (FamilyAPI.zero kind) trace (AllRows.actual_row kind platform initial) ranges
  emitted final emit flush
 have whole:=WorldMain.actual_body kind platform CompleteIOModel.policy (FamilyAPI.total kind)
  (FamilyAPI.zero kind) trace (AllRows.actual_row kind platform initial) ranges
  emitted final emit flush
 have read:=MainTotalOutput.read_total FullMainPrefix.service total 768
 refine ⟨trace,final,total,rfl,?_,read,whole.2.1,whole.2.2⟩
 exact Eq.mpr (congrArg (fun entry=>WorldSource.SourceCall SynergyC.Header.layout
   (code kind) platform CompleteIOModel.policy 3 "__wrap_main" []
   ⟨entry,initial⟩ (WorldIO.signed32 0) ⟨FullMainPrefix.cache,final.stream⟩)
   MainComputedGlobals.initial_state_exact) source

theorem read_identity (kind : Kind) {out : ProofBox}
 (read : evalExpr SynergyC.Header.layout FullMainPrefix.service 1
   (FullMainEdges.loopState (FamilyAPI.total kind 768) 768) (.var "total")=
   some (SynergyC.SourceIntervalMath.represented out,
    FullMainEdges.loopState (FamilyAPI.total kind 768) 768)) :
 out=FamilyAPI.total kind 768 := by
 have same:=Option.some.inj (read.symm.trans
   (MainTotalOutput.read_total FullMainPrefix.service (FamilyAPI.total kind 768) 768))
 exact MainTotalOutput.represented_injective (congrArg Prod.fst same)
#print axioms final_range
#print axioms complete
#print axioms read_identity
end
end SynergyMomentCHi.CompleteProgram
