/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderAdvance
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

def rowStatements : List Stmt:=prefixStatements++(magnitudeBranch::([scaledDeclaration,pointerDeclaration]++
  (rawStatements++[canonicalStatement,mirrorStatement,advanceStatement])))

theorem source_row : loopBody=.block rowStatements:=rfl

/-- All fourteen actual source instructions in a loader iteration. Every birth,
lookup, unsigned branch, store, canonicalization and reflected copy is executed,
and the actual parent variable j advances without wrapping. -/
theorem row_execution {F : Type} (context : Context F) {before : State F} {input : Input} {fo j : Nat} {ids : Parameter → Nat}
    (h : LoopView before input fo ids j) (pinned : context.program=input.profile.program) (hj : j< input.profile.count) :
    ∃after,Exec context before loopBody .normal after ∧ Every context before loopBody .normal after ∧
      LoopView after input fo ids (j+1) ∧
      ApplicationBirthFrame.Frame before.nextObject before after [input.object,ids .j] ∧
      after.environment=before.environment ∧ after.scope=before.scope:=by
  have entered:=h.enter_body hj
  have zero : ∀i<12,currentData input.profile.encoded input.profile.grid j (12*j+i)=0:=by
    intro i hi
    have shape:=input.profile.shape
    exact currentData_middle _ _ j j i (le_refl _) (by omega) hi
  obtain ⟨s1,ids1,run1,every1,h1,f1,id1⟩:=entered.prefix_execution context pinned
  obtain ⟨s2,run2,every2,h2,f2⟩:=h1.magnitude_branch_execution context
  obtain ⟨s3,ids2,run3,every3,h3,f3,id2⟩:=h2.preparation_execution context
  obtain ⟨s4,run4,every4,h4,f4⟩:=h3.raw_stores_execution context
  obtain ⟨s5,run5,every5,h5,f5⟩:=h4.canonical_execution context pinned zero
  obtain ⟨s6,run6,every6,h6,f6⟩:=h5.mirror_execution context pinned
  obtain ⟨finished,run7,every7,finalArray,finalLocals,f7,env7,scope7⟩:=h6.advance_execution context
  have sameIds (p : Parameter) : ids2 (.inl p)=ids p:=(id2 p).trans (id1 p)
  have idsFunction : (fun p=>ids2 (.inl p))=ids:=funext sameIds
  rw [idsFunction] at finalLocals
  rw [sameIds .j] at f7
  have bodyRun : ExecList context before.enterScope rowStatements .normal finished:=
    append_normal run1 (.cons run2 (append_normal run3 (append_normal run4 (.cons run5 (.cons run6 (.cons run7 .nil))))))
  have bodyEvery : EveryList context before.enterScope rowStatements .normal finished:=
    every_append every1 (every_cons every2 (every_append every3 (every_append every4 (every_cons every5 (every_cons every6 (every_cons every7 (every_nil finished)))))))
  have padEmpty {a b : State F} (frame : ApplicationBirthFrame.Frame before.nextObject a b []) :
      ApplicationBirthFrame.Frame before.nextObject a b [input.object,ids .j]:=frame_widen frame (by intros;simp_all)
  have padData {a b : State F} (frame : ApplicationBirthFrame.Frame before.nextObject a b [input.object]) :
      ApplicationBirthFrame.Frame before.nextObject a b [input.object,ids .j]:=frame_widen frame (by simp)
  have whole:=(padEmpty f1).trans ((padEmpty f2).trans ((padEmpty f3).trans ((padData f4).trans ((padData f5).trans ((padData f6).trans f7)))))
  let after : State F:={finished.leaveScope before.nextScope before.environment with scope:=before.scope}
  have frame:=ApplicationBirthFrame.close_frame h.well (le_refl _) whole
  have different : before.nextScope≠fo:=by have bound:=h.locals.bound;omega
  have locals:=finalLocals.leave different before.environment h.locals.lookup before.scope
  have output : LoopView after input fo ids (j+1):=
    ⟨IncrementSource.wordArray_leave finalArray,locals,h.separate,by omega,frame.well⟩
  refine ⟨after,?_,?_,output,frame,rfl,rfl⟩
  · rw [source_row]
    exact .block (by rfl) bodyRun (by rfl)
  · rw [source_row]
    exact every_block bodyEvery

#print axioms source_row
#print axioms row_execution
end RH080Next.FFTPV.InputLoader
