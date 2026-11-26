/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootMemory
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

/-- Exact whole-allocation effect of the five actual Taylor setup statements. -/
def setupData (input : Input) (data : Nat → Nat) : Nat → Nat:=
  let cleared:=ZeroSlice.zeroData data input.layout.rootStart 12
  let cr:=Function.update cleared (input.layout.rootStart+4) 1
  let ct:=Function.update cr (input.layout.workStart+16) 1
  let st:=CopyLoop.prefixData ct (fun i=>ct (input.layout.workStart+i)) (input.layout.workStart+18) 6
  CopyLoop.prefixData st (fun i=>st (input.layout.workStart+i)) (input.layout.rootStart+6) 6

def setupStatements : List Stmt:=[zeroSliceStatement .root 0 12,literalStore .root 4 1,
  literalStore .work 16 1,copySliceStatement .work 18 .work 0,copySliceStatement .root 6 .work 0]

def setupRemainingStatements : List Stmt:=match initialize_root_ast.body with
  | .block body=>body.drop 14
  | _=>[]

theorem actual_setup : initialize_root_ast.body=.block
    (xPrefixStatements++squareStatement::setupStatements++setupRemainingStatements):=by rfl

/-- Actual root initialization of cr/ct and the two source copies of x.
One allocation may hold every role; disjointness is proved from Layout. -/
theorem setup_execution {F : Type} (context : Context F)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (copySelected : findFunction context.program "copy_words"=some copy_words_ast)
    {before : State F} {input : Input} {owner statusId : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : ScaleView before input owner statusId ids data) (scope : before.scope=owner) :
    ∃after,ExecList context before setupStatements .normal after ∧
      ScaleView after input owner statusId ids (setupData input data) ∧ after.scope=owner := by
  have rootBound:=input.layout.rootBound
  have workBound:=input.layout.workBound
  have separate:=input.layout.separate
  obtain ⟨s0,run0,v0,sc0⟩:=zero_slice_execution context zeroSelected h scope.ge .root (Or.inl rfl) 0 12
    (by simpa [pointerStart] using (show input.layout.rootStart< input.layout.size by omega))
    (by simpa [pointerStart] using rootBound) (by norm_num) (by norm_num)
  have scope0 : s0.scope=owner:=sc0.trans scope
  obtain ⟨s1,run1,v1,sc1⟩:=literal_store_execution context v0 .root (Or.inl rfl) 4 1
    (by simp only [pointerStart];omega) (by norm_num) (by norm_num)
  have scope1 : s1.scope=owner:=sc1.trans scope0
  obtain ⟨s2,run2,v2,sc2⟩:=literal_store_execution context v1 .work (Or.inr rfl) 16 1
    (by simp only [pointerStart];omega) (by norm_num) (by norm_num)
  have scope2 : s2.scope=owner:=sc2.trans scope1
  obtain ⟨s3,run3,v3,sc3⟩:=copy_slice_execution context copySelected v2 scope2.ge .work (Or.inr rfl) 18 .work (Or.inr rfl) 0
    (by simp only [pointerStart];omega) (by simp only [pointerStart];omega)
    (Or.inr (Or.inr (by simp only [pointerStart];omega))) (by norm_num) (by norm_num)
  have scope3 : s3.scope=owner:=sc3.trans scope2
  obtain ⟨after,run4,post,sc4⟩:=copy_slice_execution context copySelected v3 scope3.ge .root (Or.inl rfl) 6 .work (Or.inr rfl) 0
    (by simp only [pointerStart];omega) (by simp only [pointerStart];omega)
    (by simp only [pointerStart];rcases separate with lo|hi
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))) (by norm_num) (by norm_num)
  refine ⟨after,.cons run0 (.cons run1 (.cons run2 (.cons run3 (.cons run4 .nil)))),?_,sc4.trans scope3⟩
  simpa only [setupData,pointerStart,Nat.add_zero] using post

#print axioms actual_setup
#print axioms setup_execution
end RH080Next.FFTPV.RootSource
