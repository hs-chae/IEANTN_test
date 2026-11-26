/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainFree
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource

structure FreeView {F : Type} (state : State F) (n : Nat) (objects ids owners : Role → Nat)
    (data : Role → Nat → Nat) (answerId answerOwner answer : Nat) (remaining : List Role) : Prop where
  lookup : ∀r∈remaining,state.environment.lookup (name r)=some (scalarPointer (ids r) (.pointer .u64))
  slots : ∀r∈remaining,Slot state (ids r) (owners r) (.pointer .u64) (.pointer (wordPointer (objects r) 0))
  arrays : ∀r∈remaining,WordArrayRep state (objects r) (length n r) (data r)
  distinct : Function.Injective objects
  answerLookup : state.environment.lookup "answer"=some (scalarPointer answerId .u64)
  answerSlot : Slot state answerId answerOwner .u64 (.integer (integer64 answer))
  well : WellScoped state

theorem FreeView.step {F : Type} (context : Context F) {before : State F}
    {n answerId answerOwner answer : Nat} {objects ids owners : Role → Nat} {data : Role → Nat → Nat}
    {r : Role} {remaining : List Role}
    (h : FreeView before n objects ids owners data answerId answerOwner answer (r::remaining))
    (unique : r∉remaining) (absent : findFunction context.program "free"=none)
    (has : HasMemory context) (sound : MemorySound context) :
    ∃after,NormalSegment context before [freeStatement (name r)] after ∧
      FreeView after n objects ids owners data answerId answerOwner answer remaining ∧
      MultiplyCall.CallerFrame before after [objects r] := by
  have rep:=h.arrays r (by simp)
  obtain ⟨after,called,frame,everyCall⟩:=free_words_total context (objects r) (length n r) (data r)
    absent has sound h.well rep
  have args : Args context before [.variable (name r)] [.pointer (wordPointer (objects r) 0)] before :=
    .ordered (List.Perm.refl _) (.cons (.variable (h.lookup r (by simp)) (h.slots r (by simp)).read) .nil)
      (.cons rfl .nil)
  have every : ∀other flow,Exec context before (freeStatement (name r)) flow other → flow=.normal ∧ other=after := by
    intro other flow actual
    cases actual with
    | expression ev=>
      obtain ⟨rfl,rfl⟩:=StatusCall.call_eval_unique (by intro e he;have eq:=List.mem_singleton.mp he;subst e;trivial)
        args everyCall ev
      exact ⟨rfl,rfl⟩
    | callTerminated ar ca=>
      obtain ⟨_,rfl,rfl⟩:=ApplicationPureCall.args_unique (by intro e he;have eq:=List.mem_singleton.mp he;subst e;trivial) args ar
      have impossible:=(everyCall _ _ ca).1
      cases impossible
  refine ⟨after,.single (.expression (.call args called)) every,⟨?_,?_,?_,h.distinct,?_,?_,frame.frame.well⟩,frame⟩
  · intro s member
    rw [frame.environment]
    exact h.lookup s (by simp [member])
  · intro s member
    have slot:=h.slots s (by simp [member])
    have ne:=Ne.symm (RecursiveSource.array_ne_slot rep slot)
    exact ⟨slot.storable,(frame.frame.outside _ (h.well.objectIds _ _ slot.object) (by simpa using ne)).trans slot.object⟩
  · intro s member
    have old:=h.arrays s (by simp [member])
    have ne : objects s≠objects r := by
      intro eq
      have same:=h.distinct eq
      exact unique (same ▸ member)
    exact ⟨frame.frame.mode.trans old.1,
      (frame.frame.outside _ (h.well.objectIds _ _ old.2.1) (by simpa using ne)).trans old.2.1,old.2.2⟩
  · rw [frame.environment]
    exact h.answerLookup
  · have ne:=Ne.symm (RecursiveSource.array_ne_slot rep h.answerSlot)
    exact ⟨h.answerSlot.storable,
      (frame.frame.outside _ (h.well.objectIds _ _ h.answerSlot.object) (by simpa using ne)).trans h.answerSlot.object⟩

def answerReturn : Stmt:=.returnValue (some (.variable "answer"))
def finalStatements (remaining : List Role) : List Stmt:=remaining.map (fun r=>freeStatement (name r))++[answerReturn]

/-- The actual final free sequence and return, including EVERY finite source
execution. Every released heap object is distinct from the actual answer slot. -/
theorem FreeView.return_total {F : Type} (context : Context F) {before : State F}
    {n answerId answerOwner answer : Nat} {objects ids owners : Role → Nat} {data : Role → Nat → Nat}
    (remaining : List Role) (unique : remaining.Nodup)
    (h : FreeView before n objects ids owners data answerId answerOwner answer remaining)
    (absent : findFunction context.program "free"=none) (has : HasMemory context) (sound : MemorySound context) :
    ∃after,ExecList context before (finalStatements remaining) (.returned (.integer (integer64 answer))) after ∧
      (∀other flow,ExecList context before (finalStatements remaining) flow other →
        flow=.returned (.integer (integer64 answer)) ∧ other=after) ∧
      after.environment=before.environment ∧ after.scope=before.scope ∧
      Frame before.nextObject before after (remaining.map objects) := by
  induction remaining generalizing before with
  | nil=>
    have returned : Exec context before answerReturn (.returned (.integer (integer64 answer))) before :=
      .returnSome (.variable h.answerLookup h.answerSlot.read)
    have run : ExecList context before [answerReturn] (.returned (.integer (integer64 answer))) before :=
      .abrupt returned (by intro bad;cases bad)
    refine ⟨before,run,?_,rfl,rfl,Frame.refl _ _ h.well (le_refl _)⟩
    intro other flow actual
    obtain ⟨same,states⟩:=PureDeterminism.list_unique (by intro s member;have eq:=List.mem_singleton.mp member;subst s;trivial) run actual
    exact ⟨same.symm,states.symm⟩
  | cons r rest ih=>
    have headUnique:=List.nodup_cons.mp unique
    obtain ⟨middle,first,current,frame⟩:=h.step context headUnique.1 absent has sound
    obtain ⟨after,tail,tailEvery,env,scope,tailFrame⟩:=ih headUnique.2 current
    have widenFirst : Frame before.nextObject before middle (objects r::rest.map objects) := by
      refine ⟨frame.frame.well,frame.frame.fresh,frame.frame.nextObject,frame.frame.nextScope,
        frame.frame.mode,frame.frame.foreign,?_⟩
      intro id old outside
      apply frame.frame.outside id old
      intro member
      exact outside (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp member)))
    have widenTail : Frame before.nextObject middle after (objects r::rest.map objects) := by
      have lowered:=lower_cutoff tailFrame frame.frame.nextObject
      exact ⟨lowered.well,lowered.fresh,lowered.nextObject,lowered.nextScope,lowered.mode,lowered.foreign,
        fun id old outside=>lowered.outside id old (fun member=>outside (List.mem_cons_of_mem _ member))⟩
    have headRun : Exec context before (freeStatement (name r)) .normal middle := by
      cases first.execution with
      | cons one rest=>cases rest;exact one
      | abrupt one impossible=>exact False.elim (impossible rfl)
    refine ⟨after,.cons headRun tail,?_,env.trans frame.environment,scope.trans frame.scope,widenFirst.trans widenTail⟩
    intro other flow actual
    cases actual with
    | cons one rest=>
      obtain ⟨_,same⟩:=first.every _ _ (.cons one .nil)
      subst middle
      exact tailEvery _ _ rest
    | abrupt one impossible=>
      have normal:=(first.every _ _ (.abrupt one impossible)).1
      exact False.elim (impossible normal)

#print axioms FreeView.step
#print axioms FreeView.return_total
end RH080Next.FFTPV.MainAllocation
