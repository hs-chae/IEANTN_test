/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootPairedTerms
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open IncrementSource (base)

/-- All nine unchanged source instructions of one actual Taylor iteration.
Both complete arithmetic paths, all copies/divisions, both signed accumulations
and the true i increment are consumed. The frame uses the original root-param
birth as cutoff, so application-local i is not mistaken for caller memory. -/
theorem iteration_execution {F : Type} (context : Context F) (functions : Functions context)
    {before : State F} {input : Input} {owner statusId indexId j : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data (j+1))
    (tracked : Tracked input data (regionValue input.n j)) (grid : OriginalGrid input.n) (hj : j<10) :
    ∃after nextData,ExecList context before iterationStatements .normal after ∧
      EveryList context before iterationStatements .normal after ∧
      Runtime after input owner statusId indexId ids nextData (j+1+1) ∧
      Tracked input nextData (regionValue input.n (j+1)) ∧
      ApplicationBirthFrame.Frame (ids .root) before after [input.layout.object] ∧ after.scope=before.scope ∧
      ∀k,k < input.layout.size → (k < input.layout.workStart ∨ input.layout.workStart+80≤ k) →
        (k < input.layout.rootStart ∨ input.layout.rootStart+12≤ k) → nextData k=data k := by
  have workBound:=input.layout.workBound
  have rootBound:=input.layout.rootBound
  have separate:=input.layout.separate
  obtain ⟨cosNonnegative,cosSmall,sinNonnegative,sinSmall,ctSmall,stSmall,x2Small,crSmall,srSmall⟩:=original_intermediate_bounds input.n j grid hj
  obtain ⟨s6,data6,run6,every6,rt6,track6,frame6,outside6⟩:=paired_terms_execution context functions h tracked grid hj
  have flag : (j+1)%2≤1:=by have hm:=Nat.mod_lt (j+1) (show 0<2 by omega);omega
  obtain ⟨s7,data7,run7,every7,view7,output7,frame7,outside7⟩:=add_execution context functions.add functions.compare functions.canonical
    rt6.view rt6.active .root (Or.inl rfl) 0 .work (Or.inr rfl) 12 ((j+1)%2) parityIndex
    (parity_index_eval context rt6 hj) parity_index_pure flag (taylorState input.n j).cr (nextCosineTerm input.n j)
    (track6 .cr) (track6 .ct) crSmall
    (by simp only [pointerStart];omega) (by simp only [pointerStart];omega)
    (by simp only [pointerStart];rcases separate with lo|hi
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))) (by norm_num) (by norm_num)
  have rt7:=rt6.after_unary view7 frame7
  have cr : FixedValue data7 (regionStart input .cr) (taylorState input.n (j+1)).cr:=by
    rw [next_cr];exact output7
  have track7:=track6.update Region.cr _ cr outside7
  obtain ⟨s8,data8,run8,every8,view8,output8,frame8,outside8⟩:=add_execution context functions.add functions.compare functions.canonical
    rt7.view rt7.active .root (Or.inl rfl) 6 .work (Or.inr rfl) 18 ((j+1)%2) parityIndex
    (parity_index_eval context rt7 hj) parity_index_pure flag (taylorState input.n j).sr (nextSineTerm input.n j)
    (track7 .sr) (track7 .st) srSmall
    (by simp only [pointerStart];omega) (by simp only [pointerStart];omega)
    (by simp only [pointerStart];rcases separate with lo|hi
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))) (by norm_num) (by norm_num)
  have rt8:=rt7.after_unary view8 frame8
  have sr : FixedValue data8 (regionStart input .sr) (taylorState input.n (j+1)).sr:=by
    rw [next_sr];exact output8
  have track8:=track7.update Region.sr _ sr outside8
  obtain ⟨after,run9,every9,rt9,scope9,birth9⟩:=index_increment_execution context rt8 (by omega)
  have nextValues : Function.update (Function.update (updatedTerms input.n j) .cr (taylorState input.n (j+1)).cr)
      .sr (taylorState input.n (j+1)).sr=regionValue input.n (j+1):=by
    funext r
    cases r <;> simp [updatedTerms,regionValue,Function.update,next_ct,next_st]
  rw [nextValues] at track8
  have initialRoot:=h.view.params.well.objectIds _ _ (h.view.params.locals.slots Param.root).object
  have frameFirst:=full_caller_trans frame6 (full_caller_trans frame7 frame8)
  have birthFirst:=lower_frame (unary_frame frameFirst) initialRoot.le
  refine ⟨after,data8,append_normal run6 (.cons run7 (.cons run8 (.cons run9 .nil))),
    every_append every6 (every_cons every7 (every_cons every8 (every_cons every9 (every_nil after)))),rt9,track8,
    birthFirst.trans birth9,scope9.trans frameFirst.scope,?_⟩
  intro k hk outsideWork outsideRoot
  exact (outside8 k (by simp only [pointerStart];rcases outsideRoot with lo|hi <;> omega)).trans
    ((outside7 k (by simp only [pointerStart];rcases outsideRoot with lo|hi <;> omega)).trans
      (outside6 k hk outsideWork))

#print axioms iteration_execution
end RH080Next.FFTPV.RootSource
