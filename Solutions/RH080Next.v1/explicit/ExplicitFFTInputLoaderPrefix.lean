/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderScalar
import ExplicitFFTRootFrames
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

def valueDeclaration : Stmt:=.declare .u64 "value" (some (.literal (.integer 0 "ULL")))
def signDeclaration : Stmt:=.declare .u64 "sign" (some (.literal (.integer 0 "ULL")))
def prefixStatements : List Stmt:=[eDeclaration,valueDeclaration,signDeclaration]

theorem source_prefix : (ProductRow.items loopBody).take 3=prefixStatements:=rfl

theorem BodyView.prefix_execution {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo j cutoff : Nat}
    {ids : Var → Nat} {memory : Nat → Nat}
    (h : BodyView before input fo bo 0 j cutoff ids (plannedValues input j) memory)
    (pinned : context.program=input.profile.program) :
    ∃after finalIds,ExecList context before prefixStatements .normal after ∧ EveryList context before prefixStatements .normal after ∧
      BodyView after input fo bo 3 j cutoff finalIds (plannedValues input j) memory ∧
      ApplicationBirthFrame.Frame cutoff before after [] ∧
      ∀p,finalIds (.inl p)=ids (.inl p):=by
  obtain ⟨returned,s1,run1,every1,h1,f1⟩:=h.e_birth context pinned
  obtain ⟨s2,run2,every2,h2,f2⟩:=h1.birth context (next:=.value) (expression:=.literal (.integer 0 "ULL")) rfl
    (ZeroFrame.u64_storable 0 (by norm_num)) (.literal _ _ _ (by rfl)) (by trivial)
  obtain ⟨after,run3,every3,h3,f3⟩:=h2.birth context (next:=.sign) (expression:=.literal (.integer 0 "ULL")) rfl
    (ZeroFrame.u64_storable 0 (by norm_num)) (.literal _ _ _ (by rfl)) (by trivial)
  exact ⟨after,_,.cons run1 (.cons run2 (.cons run3 .nil)),every_cons every1 (every_cons every2 (every_cons every3 (every_nil after))),h3,
    ((lower_frame f1 h.fresh).trans (lower_frame f2 h1.fresh)).trans (lower_frame f3 h2.fresh),by intro p;simp⟩

#print axioms source_prefix
#print axioms BodyView.prefix_execution
end RH080Next.FFTPV.InputLoader
