/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadAbsolute
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

theorem View.prefix_execution {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo bo j cutoff : Nat}
    {ids : InputLoader.Var → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : View before input workObject fo bo 0 j cutoff ids auxIds (plannedValues input j) dataMemory workData)
    (pinned : context.program=input.profile.program) :
    ∃after finalIds,ExecList context before [eDeclaration,valueDeclaration,absoluteBranch] .normal after ∧
      EveryList context before [eDeclaration,valueDeclaration,absoluteBranch] .normal after ∧
      View after input workObject fo bo 2 j cutoff finalIds auxIds (absoluteValues input j) dataMemory workData ∧
      ApplicationBirthFrame.Frame cutoff before after [] ∧ ∀p,finalIds (.inl p)=ids (.inl p):=by
  obtain ⟨returned,s1,run1,every1,h1,f1⟩:=h.e_birth context pinned
  obtain ⟨s2,run2,every2,h2,f2⟩:=h1.pure_birth context (next:=.value) (expression:=.literal (.integer 0 "ULL")) rfl
    (ZeroFrame.u64_storable 0 (by norm_num)) (.literal _ _ _ (by rfl)) (by trivial)
  obtain ⟨after,run3,every3,h3,f3⟩:=h2.absolute_execution context
  exact ⟨after,_,.cons run1 (.cons run2 (.cons run3 .nil)),every_cons every1 (every_cons every2 (every_cons every3 (every_nil after))),h3,
    (f1.trans f2).trans f3,by intro p;simp⟩

#print axioms View.prefix_execution
end RH080Next.FFTPV.QuadSource
