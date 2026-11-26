/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootScaleFramed
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

theorem setup_framed {F : Type} (context : Context F)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (copySelected : findFunction context.program "copy_words"=some copy_words_ast)
    {before : State F} {input : Input} {owner statusId : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : ScaleView before input owner statusId ids data) (scope : before.scope=owner) :
    ∃after,ExecList context before setupStatements .normal after ∧
      EveryList context before setupStatements .normal after ∧
      ScaleView after input owner statusId ids (setupData input data) ∧ IncrementSource.FullCallerFrame before after input.layout.object := by
  have rootBound:=input.layout.rootBound
  have workBound:=input.layout.workBound
  have separate:=input.layout.separate
  obtain ⟨s0,run0,every0,v0,sc0⟩:=zero_slice_framed context zeroSelected h scope.ge .root (Or.inl rfl) 0 12
    (by simpa [pointerStart] using (show input.layout.rootStart< input.layout.size by omega))
    (by simpa [pointerStart] using rootBound) (by norm_num) (by norm_num)
  have scope0 : s0.scope=owner:=sc0.scope.trans scope
  obtain ⟨s1,run1,every1,v1,sc1⟩:=literal_store_framed context v0 .root (Or.inl rfl) 4 1
    (by simp only [pointerStart];omega) (by norm_num) (by norm_num)
  have scope1 : s1.scope=owner:=sc1.scope.trans scope0
  obtain ⟨s2,run2,every2,v2,sc2⟩:=literal_store_framed context v1 .work (Or.inr rfl) 16 1
    (by simp only [pointerStart];omega) (by norm_num) (by norm_num)
  have scope2 : s2.scope=owner:=sc2.scope.trans scope1
  obtain ⟨s3,run3,every3,v3,sc3⟩:=copy_slice_framed context copySelected v2 scope2.ge .work (Or.inr rfl) 18 .work (Or.inr rfl) 0
    (by simp only [pointerStart];omega) (by simp only [pointerStart];omega)
    (Or.inr (Or.inr (by simp only [pointerStart];omega))) (by norm_num) (by norm_num)
  have scope3 : s3.scope=owner:=sc3.scope.trans scope2
  obtain ⟨after,run4,every4,post,sc4⟩:=copy_slice_framed context copySelected v3 scope3.ge .root (Or.inl rfl) 6 .work (Or.inr rfl) 0
    (by simp only [pointerStart];omega) (by simp only [pointerStart];omega)
    (by simp only [pointerStart];rcases separate with lo|hi
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))) (by norm_num) (by norm_num)
  refine ⟨after,.cons run0 (.cons run1 (.cons run2 (.cons run3 (.cons run4 .nil)))),
    every_cons every0 (every_cons every1 (every_cons every2 (every_cons every3 (every_cons every4 (every_nil after))))),?_,full_caller_trans sc0 (full_caller_trans sc1 (full_caller_trans sc2 (full_caller_trans sc3 sc4)))⟩
  simpa only [setupData,pointerStart,Nat.add_zero] using post


theorem setupData_outside (input : Input) (data : Nat → Nat) (k : Nat)
    (outsideWork : k< input.layout.workStart ∨ input.layout.workStart+80≤ k)
    (outsideRoot : k< input.layout.rootStart ∨ input.layout.rootStart+12≤ k) : setupData input data k=data k := by
  have rootZero : ¬(input.layout.rootStart≤ k ∧ k< input.layout.rootStart+12):=by omega
  have rootCopy : ¬(input.layout.rootStart+6≤ k ∧ k< input.layout.rootStart+6+6):=by omega
  have workCopy : ¬(input.layout.workStart+18≤ k ∧ k< input.layout.workStart+18+6):=by omega
  have notRoot : k≠input.layout.rootStart+4:=by omega
  have notWork : k≠input.layout.workStart+16:=by omega
  simp [setupData,CopyLoop.prefixData,rootCopy,workCopy,Function.update_of_ne notRoot,
    Function.update_of_ne notWork,ZeroSlice.zeroData,CopyLoop.prefixData,rootZero]

#print axioms setup_framed
#print axioms setupData_outside
end RH080Next.FFTPV.RootSource
