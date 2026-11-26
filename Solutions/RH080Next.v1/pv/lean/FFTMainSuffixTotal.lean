/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixTotalBindings
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

def totalStatements (fap : Bool) : List Stmt:=DropTwoSource.statements++NormalizeSource.totalStatements fap

theorem actual_w4_total : ((bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).drop 26).take 8=totalStatements false := by rfl
theorem actual_fap_total : ((bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).drop 26).take 7=totalStatements true := by rfl

theorem normalize_accumulated_output {F : Type} (context : Context F) (fap : Bool)
    (pinned : context.program=NormalizeSource.profileProgram fap)
    {before : State F} {n nId owner pointerBase status iId : Nat} {objects ids : Role → Nat}
    {outputData workData : Nat → Nat} {samples : Nat → FFT.IntegerModel.CInt}
    (full : FullMainLocals before n nId owner objects ids pointerBase status)
    (sum : OutputSumSource.View before (objects .output) (objects .work) n
      (sumIds nId ids pointerBase status iId) owner n outputData workData samples)
    (scope : before.scope=owner) :
    ∃after dataAfter,
      NormalSegment context before (totalStatements fap) after ∧
      FullMainLocals after n nId owner objects ids pointerBase status ∧
      WordArrayRep after (objects .work) 512 dataAfter ∧
      Frame before.nextObject before after [objects .work,iId] ∧
      FFT.Limbs.magnitude 1000000000 6 (fun k => dataAfter (192+k))=
        NormalizeSource.totalValue fap (FFT.Limbs.ceilQuotient (OutputSumSource.partialSum samples n) (1000000000^2)) n ∧
      (∀k,k<6 → dataAfter (192+k)<1000000000) ∧
      (∀k,(k<192∨198≤k) → dataAfter k=workData k) ∧
      (∀name,name≠"lost" → after.environment.lookup name=before.environment.lookup name) ∧ after.scope=owner := by
  have programCases : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program := by
    cases fap with
    | false => exact Or.inl pinned
    | true => exact Or.inr pinned
  have restricted : Locals before (fun v => DropTwoSource.name (DropTwoSource.lift v))
      (fun v => DropTwoSource.type (DropTwoSource.lift v)) (dropIds pointerBase status iId) before.scope
      (fun v => DropTwoSource.values (objects .work) workData n (DropTwoSource.lift v)) := by
    rw [scope]
    have inj : Function.Injective dropLift := by intro a b h;cases a <;> cases b <;> simp_all [dropLift]
    have did : dropIds pointerBase status iId=sumIds nId ids pointerBase status iId ∘ dropLift := by funext v;cases v <;> rfl
    refine ⟨?_,?_,by rw [did];exact sum.locals.distinct.comp inj,sum.locals.bound⟩
    · intro v;have h:=sum.locals.lookup (dropLift v);cases v <;> exact h
    · intro v;have h:=sum.locals.slots (dropLift v);cases v <;> exact h
  obtain ⟨_,_,_,_,dropState,lostId,dropRun,dropArray,_,dropFrame,dropValue,dropEvery⟩ :=
    DropTwoSource.source_drop_two_total context programCases before (objects .work) n
      (dropIds pointerBase status iId) workData sum.well restricted sum.work sum.totalDigits
  obtain ⟨dropLookup,dropScope⟩ := drop_lookup_scope dropRun
  have awayI := full_main_i_distinct full sum
  have dropFull : FullMainLocals dropState n nId owner objects ids pointerBase status := by
    apply MainTransport.locals_of_frame sum.well full dropFrame
    · intro v;exact dropLookup (fullName v) (full_name_ne_lost v)
    · intro v
      simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
      exact ⟨(MultiplyParameters.array_slot_different sum.work (full.slots v)).symm,awayI v⟩
  have params := normalize_parameters dropFull
  have separation : ∀v,objects .work≠normalizeIds nId pointerBase status v := by
    intro v;exact MultiplyParameters.array_slot_different dropArray (params.slots v)
  have small : n<1000000000 := by have h:=sum.nbound;omega
  have positive : 0<n := by have h:=sum.nbound;omega
  have droppedDigits : ∀k,k<6 → DropTwoSource.roundData workData 192 (192+k)<1000000000 :=
    DropTwoSource.roundData_normalized sum.totalDigits
  obtain ⟨_,_,_,after,dataAfter,normRun,array,normParams,normFrame,normValue,digits,outside,every⟩ :=
    NormalizeSource.source_total_execution context fap pinned params dropArray separation dropFrame.well positive small droppedDigits
  have finalFull : FullMainLocals after n nId owner objects ids pointerBase status := by
    apply MainTransport.locals_of_frame dropFrame.well dropFull normFrame.frame (fun v => by rw [normFrame.environment])
    intro v;simpa using (MultiplyParameters.array_slot_different dropArray (dropFull.slots v)).symm
  have postFrame : Frame before.nextObject dropState after [objects .work,iId] := by
    refine ⟨normFrame.frame.well,le_trans dropFrame.nextObject normFrame.frame.fresh,normFrame.frame.nextObject,
      normFrame.frame.nextScope,normFrame.frame.mode,normFrame.frame.foreign,?_⟩
    intro id old away
    apply normFrame.frame.outside id (lt_of_lt_of_le old dropFrame.nextObject)
    intro written
    exact away (by simpa using Or.inl (List.mem_singleton.mp written))
  have value : FFT.Limbs.magnitude 1000000000 6 (fun k => dataAfter (192+k))=
      NormalizeSource.totalValue fap (FFT.Limbs.ceilQuotient (OutputSumSource.partialSum samples n) (1000000000^2)) n := by
    have rawValue : FFT.Limbs.magnitude 1000000000 6 (fun k => workData (192+k))=OutputSumSource.partialSum samples n := by
      simpa using sum.totalValue
    exact normValue.trans (congrArg (fun v => NormalizeSource.totalValue fap v n)
      (dropValue.trans (congrArg (fun v => FFT.Limbs.ceilQuotient v (1000000000^2)) rawValue)))
  refine ⟨after,dataAfter,(⟨dropRun,dropEvery⟩ : NormalSegment context before DropTwoSource.statements dropState).append
    ⟨normRun,every⟩,finalFull,array,dropFrame.trans postFrame,value,digits,?_,?_,normFrame.scope.trans (dropScope.trans scope)⟩
  · intro k away
    exact (outside k away).trans (DropTwoSource.roundData_outside workData 192 k away)
  · intro name different
    rw [normFrame.environment]
    exact dropLookup name different

#print axioms actual_w4_total
#print axioms actual_fap_total
#print axioms normalize_accumulated_output
end RH080Next.FFTPV.MainSuffix
