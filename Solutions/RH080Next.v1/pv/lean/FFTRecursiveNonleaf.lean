/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveEntry
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

private theorem restrict_frame {F : Type} {cutoff bigger : Nat} {before after : State F} {writes : List Nat}
    (h : Frame bigger before after writes) (bound : cutoff≤bigger) : Frame cutoff before after writes :=
  ⟨h.well,bound.trans h.fresh,h.nextObject,h.nextScope,h.mode,h.foreign,
    fun id old absent=>h.outside id (old.trans_le bound) absent⟩

/-- The actual recursive source step: both true child Calls, the entire real
header, terminating butterfly while, return and function lifetime closure.
Independent child trace bounds establish each primitive's numerical domain. -/
theorem nonleaf_strong_contract {F : Type} (context : Context F) (helpers : Helpers context)
    {total : Nat} (buffers : Buffers total) (input table : Nat → Nat) (s start index step : Nat)
    (shape : IndexShape start index step (2^(s+1)) total)
    (left : StrongContract context buffers input table s start index (step*2))
    (right : StrongContract context buffers input table s (start+2^s) (index+step) (step*2))
    (traceNorm : ∀a i d out,IndexShape a i d (2^s) total →
      FFT.IntegerModel.ExecutionTrace (stages table total) (cell input) s i d out →
      ∀k,k<2^s → ‖FFT.IntegerModel.decode (out.getD k (0,0))‖≤400)
    (twiddleNormalized : ∀r,r<2^s → NormalizedCell table (r*(total/2^(s+1))))
    (twiddleNorm : ∀r,r<2^s → ‖FFT.IntegerModel.decode (cell table (r*(total/2^(s+1))))‖≤2) :
    StrongContract context buffers input table (s+1) start index step := by
  intro before output work well arrays
  have split : 2^(s+1)=2*2^s := by rw [Nat.pow_succ];omega
  have positive : 0<2^s := by positivity
  have childShapes:=shape.children split positive
  obtain ⟨entered,parameterIds,bound,entry,parameterFrame,enteredScope⟩:=recursive_entry shape well arrays
  obtain ⟨loopBefore,finalIds,leftBefore,leftAfter,rightBefore,rightAfter,leftIds,rightIds,
      leftOutput,leftWork,mergedOutput,mergedWork,header,hl,headerFrame,hLeft,leftCall,leftArrays,hRight,rightCall,rightArrays⟩:=
    entry.total_header context shape split positive left.child right.child
  have leftPost:=left.at_call childShapes.1 hLeft.well hLeft.arrays leftCall leftArrays
  have rightPost:=right.at_call childShapes.2 hRight.well hRight.arrays rightCall rightArrays
  have leftWords : ∀r,r<2^s → ∀k,k<12 →
      mergedOutput (12*(start+r)+k)=leftOutput (12*(start+r)+k) := by
    intro r hr k hk
    apply rightPost.outputOutside
    · have htotal:=shape.output;have extent:=buffers.outputBound;omega
    · left;omega
  have leftCells : cells mergedOutput start (2^s)=cells leftOutput start (2^s) :=
    cells_congr (fun r hr=>cell_congr (leftWords r hr))
  have leftTrace : FFT.IntegerModel.ExecutionTrace (stages table total) (cell input)
      s index (step*2) (cells mergedOutput start (2^s)) := by
    rw [leftCells];exact leftPost.trace
  have domain : MergeDomain mergedOutput table start (2^s) (total/2^(s+1)) := by
    refine ⟨?_,?_,twiddleNormalized,?_,?_,twiddleNorm⟩
    · intro r hr;exact normalized_congr (leftWords r hr) (leftPost.normalized r hr)
    · intro r hr
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rightPost.normalized r hr
    · intro r hr
      have h:=traceNorm start index (step*2) _ childShapes.1 leftTrace r hr
      simpa only [cells_getD _ _ _ _ hr] using h
    · intro r hr
      have h:=traceNorm (start+2^s) (index+step) (step*2) _ childShapes.2 rightPost.trace r hr
      simpa only [cells_getD _ _ _ _ hr,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  obtain ⟨middle,finalOutput,finalWork,loop,hm,progress,loopWork,loopFrame⟩:=
    butterfly_loop context helpers hl shape split domain
  have whole : ResultSegment context entered functionStatements (.returned (.integer (integer64 0))) middle := by
    have joined:=(header.append loop).then_result (hm.final_return context)
    exact joined
  let after : State F := {middle.leaveScope entered.scope before.environment with scope:=before.scope}
  obtain ⟨called,every⟩:=recursive_call_from_segment context helpers.recursive bound whole
  have beginning : Frame before.nextObject before.enterScope loopBefore [buffers.object .output,buffers.object .work] :=
    parameterFrame.trans (restrict_frame headerFrame parameterFrame.nextObject)
  have jOutside : finalIds (.inr .j)∉[buffers.object .output,buffers.object .work] := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
    exact ⟨(array_ne_slot (hl.arrays .output) (hl.bindings.slots (.inr .j))).symm,
      (array_ne_slot (hl.arrays .work) (hl.bindings.slots (.inr .j))).symm⟩
  have freshJ : before.nextObject ≤ finalIds (.inr .j) :=
    fresh_function_slot well beginning (hl.bindings.slots (.inr .j)) jOutside
  have loopRestricted : Frame before.nextObject loopBefore middle [buffers.object .output,buffers.object .work] := by
    refine ⟨loopFrame.well,beginning.nextObject.trans loopFrame.fresh,loopFrame.nextObject,
      loopFrame.nextScope,loopFrame.mode,loopFrame.foreign,?_⟩
    intro id old absent
    apply loopFrame.outside id (old.trans_le beginning.nextObject)
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at absent ⊢
    exact ⟨absent.1,absent.2,by omega⟩
  have finalFrame : Frame before.nextObject before after [buffers.object .output,buffers.object .work] := by
    have closed:=close_frame well (le_refl _) (beginning.trans loopRestricted)
    simpa only [after,enteredScope] using closed
  have post : CallPost buffers (s+1) start index step input table output work before after finalOutput finalWork := by
    refine ⟨fun r=>word_array_leave (hm.arrays r) before.environment,⟨rfl,rfl,finalFrame⟩,?_,?_,?_,?_⟩
    · have node:=FFT.IntegerModel.ExecutionTrace.node s index step _ _ _ _ leftTrace rightPost.trace progress.merge_trace
      have lengthSplit : 2^(s+1)=2^s+2^s := by omega
      rw [lengthSplit,cells_append]
      exact node
    · intro k hk
      apply progress.normalized k
      omega
    · intro k hk outside
      have outsideLoop : k<start*12 ∨ (start+2*(2^s))*12≤k := by omega
      exact (progress.outside k outsideLoop).trans
        ((rightPost.outputOutside k hk (by omega)).trans (leftPost.outputOutside k hk (by omega)))
    · intro k hk lo hi
      exact (loopWork k hk lo hi).trans
        ((rightPost.workOutside k hk lo hi).trans (leftPost.workOutside k hk lo hi))
  exact ⟨after,finalOutput,finalWork,called,post,every⟩

#print axioms nonleaf_strong_contract
end RH080Next.FFTPV.RecursiveSource
