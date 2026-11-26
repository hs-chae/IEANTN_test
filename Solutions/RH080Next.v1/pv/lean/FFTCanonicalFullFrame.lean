/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTCanonicalCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CanonicalSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings PureDeterminism

/-- Application call bookkeeping proved from its real declarations and loops;
no application initialization or successful effect is trusted as a platform fact. -/
structure FullCallerFrame {F : Type} (before after : State F) (object : Nat)
    extends CopyLoop.CallerFrame before after object : Prop where
  nextObject : before.nextObject ≤ after.nextObject
  nextScope : before.nextScope ≤ after.nextScope
  mode : after.mode = before.mode

theorem canonical_sign_call_framed {F : Type} (context : Context F)
    (selected : findFunction context.program "canonical_sign" = some FFTRecursivePV.canonical_sign_ast)
    (before : State F) (object size start : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object size old) (bound : start+6 ≤ size)
    (digits : ∀i, i < 5 → old (start+i) < 1000000000) :
    ∃after, Call context "canonical_sign" [.pointer (wordPointer object start)] before
      (.value (.integer (integer64 0))) after ∧
      WordArrayRep after object size (canonicalData old start) ∧ FullCallerFrame before after object := by
  let entry : State F := {before.enterScope with environment := []}
  have we : WellScoped entry := wellScoped_environment (wellScoped_enter well) []
  obtain ⟨aState, nzState, jState, da, dn, dj, view⟩ := initialize_parameters we rfl rep bound digits
  obtain ⟨middle, loopRun, vm⟩ := loop_execution context 5 view (by omega)
  obtain ⟨finished, branchRun, output⟩ := canonical_branch_execution context vm
  let after : State F := {finished.leaveScope entry.scope before.environment with scope := before.scope}
  have ascope : aState.scope = entry.scope := (declare_frame da).1
  have params : bindParameters entry FFTRecursivePV.canonical_sign_ast.parameters
      [.pointer (wordPointer object start)] = some aState := by
    change bindParameters entry [(.pointer .u64,"a")] [.pointer (wordPointer object start)] = some aState
    simp [bindParameters, da]
  have called : Call context "canonical_sign" [.pointer (wordPointer object start)] before
      (.value (.integer (integer64 0))) after := by
    apply Call.internal (function := FFTRecursivePV.canonical_sign_ast) (entered := aState) (middle := finished)
      selected actual_body params
    · apply Body.finish
      · exact .cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dn)
          (.cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dj)
            (.cons loopRun (.cons branchRun (.abrupt (.returnSome (.literal (.integer 0 "ULL") _
              (.integer (integer64 0)) (by rfl))) (by intro he; cases he)))))
      · intro label he
        cases he
    · exact convert64 0 (by norm_num)
    · simp only [after, ascope]
  obtain ⟨known, original, knownRep, knownFrame⟩ := canonical_sign_call context selected before object size start old well rep bound digits
  have same := (returned_call_unique selected original called).2
  cases same
  have chain : Declarations entry jState := .cons da (.cons dn (.cons dj (.nil jState)))
  have fields := chain.fields
  have loopEffect := SourceNoAlloc.exec_effect loopRun
    (by simp [loop, condition, loopBody, sumStmt, sumExpr, increment, SourceNoAlloc.Only, SourcePure.CallFree]) view.well
  have branchEffect := SourceNoAlloc.exec_effect branchRun
    (by simp [canonicalBranch, zeroTest, signStore, SourceNoAlloc.Only, SourcePure.CallFree]) vm.well
  have effect := loopEffect.trans branchEffect
  refine ⟨after, called, knownRep, knownFrame, ?_, ?_, ?_⟩
  · change entry.nextObject ≤ finished.nextObject
    rw [effect.nextObject]
    exact fields.1
  · have ns := fields.2.2.1
    have mono := effect.nextScope
    change jState.nextScope = before.nextScope+1 at ns
    change before.nextScope ≤ finished.nextScope
    omega
  · exact effect.mode.trans fields.2.2.2.1

#print axioms canonical_sign_call_framed
end RH080Next.FFTPV.CanonicalSource
