/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixSumBindings
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

def sumStatements : List Stmt:=[MainCounters.declaration "i",MainCounters.reset "i",OutputSumSource.loop]

theorem actual_w4_sum : ((bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).drop 23).take 3=sumStatements := by rfl
theorem actual_fap_sum : ((bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).drop 23).take 3=sumStatements := by rfl

/-- Real source counter birth/reset and full unsigned magnitude accumulation.
The sample fields describe the actual already-produced FFT array and are
provided by the source recursive-call refinement, not assumed program output. -/
theorem accumulate_output {F : Type} (context : Context F)
    (pinned : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program)
    {before : State F} {n nId owner pointerBase status : Nat} {objects ids : Role → Nat}
    {outputData workData : Nat → Nat} {samples : Nat → FFT.IntegerModel.CInt}
    (full : FullMainLocals before n nId owner objects ids pointerBase status)
    (well : WellScoped before) (scope : before.scope=owner)
    (output : WordArrayRep before (objects .output) (n*12) outputData)
    (work : WordArrayRep before (objects .work) 512 workData)
    (different : objects .output≠objects .work) (nbound : 1≤n∧n≤16777216)
    (outputDigits : ∀k,k<n → ∀d,d<5 → outputData (k*12+d)<1000000000)
    (outputValues : ∀k,k<n → (ComplexSource.pair outputData (k*12)).1=(samples k).1)
    (outputSmall : ∀k,k<n → (samples k).1.natAbs≤400*10^36)
    (totalZero : ∀d,d<6 → workData (192+d)=0) :
    ∃after nextWork,
      NormalSegment context before sumStatements after ∧
      FullMainLocals after n nId owner objects ids pointerBase status ∧
      OutputSumSource.View after (objects .output) (objects .work) n
        (sumIds nId ids pointerBase status before.nextObject) owner n outputData nextWork samples ∧
      Frame before.nextObject before after [objects .work] ∧
      (∀k,(k<192∨198≤k) → nextWork k=workData k) ∧
      (∀name,name≠"i" → after.environment.lookup name=before.environment.lookup name) ∧ after.scope=owner := by
  obtain ⟨counterState,counterRun,counterEnv,iSlot,counterFrame⟩:=MainCounters.declaration_and_reset context before "i" well
  obtain ⟨counterFull,params⟩:=sum_parameters full well scope counterEnv iSlot counterFrame
  have outputNow : WordArrayRep counterState (objects .output) (n*12) outputData:=
    MainTransport.array_of_frame well output counterFrame (by simp)
  have workNow : WordArrayRep counterState (objects .work) 512 workData:=
    MainTransport.array_of_frame well work counterFrame (by simp)
  have initial : OutputSumSource.View counterState (objects .output) (objects .work) n
      (sumIds nId ids pointerBase status before.nextObject) owner 0 outputData workData samples:=by
    refine ⟨params,outputNow,workNow,different,?_,nbound,by omega,outputDigits,outputValues,outputSmall,?_,?_,counterFrame.well⟩
    · intro v;exact ⟨MultiplyParameters.array_slot_different outputNow (params.slots v),MultiplyParameters.array_slot_different workNow (params.slots v)⟩
    · intro d hd;rw [totalZero d hd];norm_num
    · simp only [FFT.Limbs.magnitude,OutputSumSource.partialSum,Finset.range_zero,Finset.sum_empty,Bool.false_eq_true,reduceIte,Nat.add_zero]
      apply Finset.sum_eq_zero
      intro d hd
      rw [totalZero d (Finset.mem_range.mp hd)]
      simp
  obtain ⟨_,_,_,_,after,nextWork,sumRun,post,sumFrame,outside,every⟩:=
    OutputSumSource.source_loop_execution context pinned n initial (by omega)
  have sumSegment : NormalSegment context counterState [OutputSumSource.loop] after:=.single sumRun every
  have oldBound : ∀v,fullIds nId ids pointerBase status v<before.nextObject:=fun v=>well.objectIds _ _ (full.slots v).object
  have fullAfter : FullMainLocals after n nId owner objects ids pointerBase status:=by
    apply MainTransport.locals_of_frame counterFrame.well counterFull sumFrame
    · intro v
      rw [BlockEnvironment.while_block_environment (by trivial) sumRun]
    · intro v
      simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
      refine ⟨(MultiplyParameters.array_slot_different workNow (counterFull.slots v)).symm,?_⟩
      change fullIds nId ids pointerBase status v≠before.nextObject
      have bound:=oldBound v;omega
  have preFrame : Frame before.nextObject before counterState [objects .work]:=by
    refine ⟨counterFrame.well,counterFrame.fresh,counterFrame.nextObject,counterFrame.nextScope,counterFrame.mode,counterFrame.foreign,?_⟩
    intro id old away;exact counterFrame.outside id old (by simp)
  have postFrame : Frame before.nextObject counterState after [objects .work]:=by
    refine ⟨sumFrame.well,le_trans counterFrame.nextObject sumFrame.fresh,sumFrame.nextObject,sumFrame.nextScope,sumFrame.mode,sumFrame.foreign,?_⟩
    intro id old away
    apply sumFrame.outside id (lt_of_lt_of_le old counterFrame.nextObject)
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at away ⊢
    exact ⟨away,by change id≠before.nextObject;omega⟩
  have finalScope : after.scope=owner:=
    (BlockEnvironment.while_block_scope (by trivial) sumRun).trans ((counter_scope counterRun.execution).trans scope)
  refine ⟨after,nextWork,counterRun.append sumSegment,fullAfter,post,preFrame.trans postFrame,outside,?_,finalScope⟩
  intro name differentName
  rw [BlockEnvironment.while_block_environment (by trivial) sumRun,counterEnv]
  simp only [List.lookup,beq_eq_false_iff_ne.mpr differentName]

#print axioms actual_w4_sum
#print axioms actual_fap_sum
#print axioms accumulate_output
end RH080Next.FFTPV.MainSuffix
