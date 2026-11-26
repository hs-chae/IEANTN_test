/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixQuadBindings
import FFTMainSuffixScopes
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

def quadStatements (p : InputLoader.Profile) : List Stmt:=[MainCounters.reset "j"]++QuadSource.stage p

theorem actual_w4_quad : ((bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).drop 34).take 2=quadStatements .w4 := by rfl
theorem actual_fap_quad : ((bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).drop 33).take 3=quadStatements .fap := by rfl

/-- Real existing j reset, actual coefficient quadrature loop, and Fap's actual
extra scaling call. The exact quad value is computed by those source loops. -/
theorem construct_quad {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) {before : State F}
    {nId owner pointerBase status jId : Nat} {objects ids : Role → Nat} {dataMemory workData : Nat → Nat}
    (full : FullMainLocals before p.grid nId owner objects ids pointerBase status)
    (loader : Locals before InputLoader.parameterName InputLoader.parameterType (loaderIds nId ids jId) owner
      (InputLoader.parameterValues ⟨p,objects .data⟩ p.count))
    (dataArray : WordArrayRep before (objects .data) (p.grid*12) dataMemory)
    (work : WordArrayRep before (objects .work) 512 workData)
    (different : objects .data≠objects .work) (well : WellScoped before) (scope : before.scope=owner)
    (quadZero : ∀k,k<6 → workData (208+k)=0) :
    ∃after memory,
      NormalSegment context before (quadStatements p) after ∧
      FullMainLocals after p.grid nId owner objects ids pointerBase status ∧
      Locals after InputLoader.parameterName InputLoader.parameterType (loaderIds nId ids jId) owner
        (InputLoader.parameterValues ⟨p,objects .data⟩ p.count) ∧
      WordArrayRep after (objects .data) (p.grid*12) dataMemory ∧
      WordArrayRep after (objects .work) 512 memory ∧
      Frame before.nextObject before after [objects .work,jId] ∧
      (∀k,k<6 → memory (208+k)<1000000000) ∧
      FFT.Limbs.magnitude 1000000000 6 (fun k => memory (208+k))=QuadSource.scaledModel p ∧
      (∀k,(k<160∨166≤k) → (k<208∨214≤k) → memory k=workData k) ∧ after.scope=owner := by
  have awayJ:=full_main_loader_j_distinct full loader
  obtain ⟨resetAfter,resetRun,jZero,resetFrame,resetEnv⟩:=MainCounters.reset_execution context before "j"
    jId owner _ well (loader.lookup .j) (loader.slots .j)
  have fullReset : FullMainLocals resetAfter p.grid nId owner objects ids pointerBase status := by
    apply MainTransport.locals_of_frame well full resetFrame (fun v => by rw [resetEnv])
    intro v;simpa using awayJ v
  have arrayReset : WordArrayRep resetAfter (objects .data) (12*p.grid) dataMemory := by
    apply MainTransport.array_of_frame well (by simpa only [Nat.mul_comm] using dataArray) resetFrame
    simpa [loaderIds] using MultiplyParameters.array_slot_different dataArray (loader.slots .j)
  have workReset : WordArrayRep resetAfter (objects .work) 512 workData := by
    apply MainTransport.array_of_frame well work resetFrame
    simpa [loaderIds] using MultiplyParameters.array_slot_different work (loader.slots .j)
  have jLookup : resetAfter.environment.lookup "j"=some (scalarPointer jId .u64) := by rw [resetEnv];exact loader.lookup .j
  have parameters:=loader_parameters fullReset jLookup jZero (awayJ (some (.inl none)))
  have aux:=quad_parameters fullReset
  have initial : QuadSource.LoopView resetAfter ⟨p,objects .data⟩ (objects .work) owner 0
      (loaderIds nId ids jId) (quadIds pointerBase status) dataMemory workData := by
    refine ⟨parameters,aux,arrayReset,workReset,different,?_,?_,?_,quad_cross fullReset awayJ,by omega,?_,?_,resetFrame.well⟩
    · intro v;exact MultiplyParameters.array_slot_different arrayReset (parameters.slots v)
    · intro v;exact MultiplyParameters.array_slot_different workReset (parameters.slots v)
    · intro v;exact MultiplyParameters.array_slot_different workReset (aux.slots v)
    · intro k hk;rw [quadZero k hk];norm_num [QuadSource.base]
    · simp only [FFT.Limbs.magnitude,QuadSource.partialQuad,Finset.range_zero,Finset.sum_empty]
      apply Finset.sum_eq_zero
      intro k hk;rw [quadZero k (Finset.mem_range.mp hk)];simp
  obtain ⟨_,_,after,memory,run,every,data,wordArray,parametersAfter,auxAfter,frame,digits,value,outside⟩:=
    QuadSource.source_quad_stage_total context initial pinned
  have fullAfter : FullMainLocals after p.grid nId owner objects ids pointerBase status := by
    apply MainTransport.locals_of_frame resetFrame.well fullReset frame.frame (fun v => by rw [frame.environment])
    intro v
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
    exact ⟨(MultiplyParameters.array_slot_different workReset (fullReset.slots v)).symm,awayJ v⟩
  have firstFrame : Frame before.nextObject before resetAfter [objects .work,jId] := by
    refine ⟨resetFrame.well,resetFrame.fresh,resetFrame.nextObject,resetFrame.nextScope,resetFrame.mode,resetFrame.foreign,?_⟩
    intro id old away
    apply resetFrame.outside id old
    intro written
    exact away (by simpa using Or.inr (List.mem_singleton.mp written))
  have secondFrame : Frame before.nextObject resetAfter after [objects .work,jId] := by
    refine ⟨frame.frame.well,le_trans resetFrame.nextObject frame.frame.fresh,frame.frame.nextObject,
      frame.frame.nextScope,frame.frame.mode,frame.frame.foreign,?_⟩
    intro id old away
    exact frame.frame.outside id (lt_of_lt_of_le old resetFrame.nextObject) away
  have resetScope : resetAfter.scope=before.scope := by
    cases resetRun.execution with
    | abrupt h no => exact False.elim (no rfl)
    | cons h rest => cases rest;exact pure_assignment_scope (by trivial) (by trivial) h
  exact ⟨after,memory,resetRun.append ⟨run,every⟩,fullAfter,parametersAfter,
    by simpa only [Nat.mul_comm] using data,wordArray,firstFrame.trans secondFrame,digits,value,outside,
    frame.scope.trans (resetScope.trans scope)⟩

#print axioms actual_w4_quad
#print axioms actual_fap_quad
#print axioms construct_quad
end RH080Next.FFTPV.MainSuffix
