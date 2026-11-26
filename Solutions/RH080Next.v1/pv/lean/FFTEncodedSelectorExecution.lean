/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTEncodedSelectorSafe
import FFTWordSubtraction
import GoldbachDirect.SourceNoAlloc
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.EncodedSelector
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots

structure ReadOnly {F : Type} (before after : State F) : Prop where
  metadata : SourceNoAlloc.Effect before after
  objects : after.objects=before.objects

theorem ReadOnly.refl {F : Type} {state : State F} (well : WellScoped state) : ReadOnly state state:=
  ⟨SourceNoAlloc.Effect.refl well,rfl⟩

theorem close_readonly {F : Type} {before middle : State F}
    (well : WellScoped before) (effect : ReadOnly before.enterScope middle) :
    ReadOnly before {middle.leaveScope before.nextScope before.environment with scope:=before.scope}:=by
  refine ⟨SourceNoAlloc.close_effect well effect.metadata,?_⟩
  funext id
  change (middle.objects id).map _=before.objects id
  rw [effect.objects]
  change (before.objects id).map _=before.objects id
  cases present : before.objects id with
  | none=>rfl
  | some object=>
    have different : object.storage≠.automatic before.nextScope:=by
      intro same
      have invalid:=well.automatic id object before.nextScope present same
      omega
    simp [different]

/-- A real typed execution of every decision-tree branch and literal return,
with actual C block entry/exit. All caller objects are preserved exactly. -/
theorem execution {F : Type} (context : Context F) (tree : Tree) (before : State F)
    (id owner j : Nat) (safe : tree.Safe) (well : WellScoped before)
    (lookup : before.environment.lookup "j"=some (scalarPointer id .u64))
    (slot : Slot before id owner .u64 (.integer (integer64 j))) (fits : j<2^64) :
    ∃after,Exec context before tree.statement (.returned (.integer (integer64 (tree.value j)))) after ∧ ReadOnly before after:=by
  induction tree generalizing before with
  | leaf v=>
    refine ⟨before,?_,ReadOnly.refl well⟩
    exact .returnSome (.literal (.integer v "ULL") _ (.integer (integer64 v)) (by simp [Literal.value,integer64];exact safe))
  | branch cut left right ihl ihr=>
    have cond : Eval context before (.binary .lt (.variable "j") (.literal (.integer cut "ULL")))
        (.integer (.boolean (decide (j<cut)))) before:=by
      exact .binaryLR (.variable lookup slot.read)
        (.literal (.integer cut "ULL") _ (.integer (integer64 cut)) (by simp [Literal.value,integer64];exact safe.1))
        (by simp only [binary,binary64_lt j cut fits safe.1,Option.map_some])
    have inherited : Slot before.enterScope id owner .u64 (.integer (integer64 j)):=⟨slot.storable,slot.object⟩
    by_cases low : j<cut
    · obtain ⟨middle,run,effect⟩:=ihl before.enterScope safe.2.1 (wellScoped_enter well) lookup inherited
      let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
      have block : Exec context before (.block [left.statement]) (.returned (.integer (integer64 (left.value j)))) after:=
        .block rfl (.abrupt run (by simp)) rfl
      refine ⟨after,?_,close_readonly well effect⟩
      simpa only [Tree.statement,Tree.value,low,↓reduceIte] using
        Exec.ifTrue cond (by simp only [low,decide_true];rfl) block
    · obtain ⟨middle,run,effect⟩:=ihr before.enterScope safe.2.2 (wellScoped_enter well) lookup inherited
      let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
      have block : Exec context before (.block [right.statement]) (.returned (.integer (integer64 (right.value j)))) after:=
        .block rfl (.abrupt run (by simp)) rfl
      refine ⟨after,?_,close_readonly well effect⟩
      simpa only [Tree.statement,Tree.value,low,↓reduceIte] using
        Exec.ifElse cond (by simp only [low,decide_false];rfl) block

#print axioms execution
end RH080Next.FFTPV.EncodedSelector
