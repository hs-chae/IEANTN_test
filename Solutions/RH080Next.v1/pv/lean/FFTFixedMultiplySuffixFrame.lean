/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixUniversal
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ProductInner ApplicationBirthFrame

private theorem args_for_increment {F : Type} (context : Context F) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow) :
    Args context before [v "out",lit 5] [.pointer (wordPointer outObj outStart),.integer (integer64 5)] before := by
  apply Args.ordered (order := [(0,v "out"),(1,lit 5)]) (evaluated :=
    [(0,.pointer (wordPointer outObj outStart)),(1,.integer (integer64 5))]) (by rfl)
  · exact .cons (.variable (h.locals.lookup (.inl MVar.out)) (h.locals.read (.inl MVar.out)))
      (.cons (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl)) .nil)
  · exact .cons (by rfl) (.cons (by rfl) .nil)

/-- Real source call and assignment with a birth-tolerant caller-object frame. -/
theorem increment_assignment_framed {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow cutoff : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow)
    (writes : List Nat) (fresh : cutoff ≤ before.nextObject) (outWrite : outObj∈writes)
    (overflowWrite : ids (.inr ())∈writes ∨ cutoff ≤ ids (.inr ())) :
    ∃after,Exec context before incrementOverflow .normal after ∧ Frame cutoff before after writes := by
  obtain ⟨called,callRun,outAfter,frame⟩:=IncrementSource.increment_words_call_framed context selected before
    outObj outSize outStart 5 outData h.well h.output (by have hb:=h.outBound;omega) (by omega) h.digits
  let carry := (FFT.Limbs.incrementDigits 1000000000 (fun k => outData (outStart+k)) 5).2
  have carryBound : carry ≤ 1:=
    (FFT.Limbs.incrementDigits_bounds 1000000000 5 (by norm_num) (fun k => outData (outStart+k)) h.digits).1
  have oldSlot:=h.locals.slots (.inr ())
  have slot : Slot called (ids (.inr ())) (owners (.inr ())) .u64 (.integer (integer64 overflow)) :=
    ⟨oldSlot.storable,(frame.objects _ (h.well.objectIds _ _ oldSlot.object) (h.separate (.inr ())).1.symm).trans oldSlot.object⟩
  have named : called.environment.lookup "overflow"=some (scalarPointer (ids (.inr ())) .u64) := by
    rw [frame.environment];exact h.locals.lookup (.inr ())
  obtain ⟨after,written⟩:=scalar_store_exists slot (.integer (integer64 (overflow+carry)))
    (ZeroFrame.u64_storable _ (by have ho:=h.overflowBound;omega))
  have run : Exec context before incrementOverflow .normal after :=
    .assign (.paren (.binaryLR (.variable (h.locals.lookup (.inr ())) (h.locals.read (.inr ())))
      (.call (args_for_increment context h) callRun)
      (by
        change Option.map Value.integer (Integer.binary .add (integer64 overflow) (integer64 carry)) = _
        rw [binary64_add overflow carry (by have ho:=h.overflowBound;omega) (by omega)
          (by have ho:=h.overflowBound;omega)]
        rfl))) (.variable named) written
  have fc : Frame cutoff before called writes := by
    refine ⟨frame.well,fresh.trans frame.nextObject,frame.nextObject,frame.nextScope,frame.mode,frame.foreign,?_⟩
    intro id old absent
    apply frame.objects id (old.trans_le fresh)
    intro eq
    exact absent (eq ▸ outWrite)
  exact ⟨after,run,fc.trans (ApplicationBirthFrame.store_frame cutoff writes frame.well fc.fresh overflowWrite written)⟩

private theorem sign_test {F : Type} (context : Context F) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow) :
    Eval context before roundCondition (.integer (.boolean (decide (0 < sign)))) before :=
  .binaryLR (.variable (h.locals.lookup (.inl MVar.sign)) (h.locals.read (.inl MVar.sign)))
    (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
    (by simp only [tailValues,extend,Sum.elim_inl,midValues,binary,
      binary64_gt sign 0 (by have hb:=h.signBound;omega) (by norm_num),Option.map_some])

private theorem lost_test {F : Type} (context : Context F) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow) :
    Eval context before lostPositive (.integer (.boolean (decide (0 < lost)))) before :=
  .binaryLR (.variable (h.locals.lookup (.inl MVar.lost)) (h.locals.read (.inl MVar.lost)))
    (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
    (by simp only [tailValues,extend,Sum.elim_inl,midValues,binary,
      binary64_gt lost 0 h.lostFits (by norm_num),Option.map_some])

/-- Every actual source nested-rounding execution frames all old allocations
outside the explicit output/local write set, including fresh callee lifetimes. -/
theorem rounding_frame {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast) {before after : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow cutoff : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow)
    (writes : List Nat) (fresh : cutoff ≤ before.nextObject) (outWrite : outObj∈writes)
    (overflowWrite : ids (.inr ())∈writes ∨ cutoff ≤ ids (.inr ())) {flow : Flow}
    (actual : Exec context before roundingBranch flow after) : Frame cutoff before after writes := by
  have known : ∃target,Exec context before roundingBranch .normal target ∧ Frame cutoff before target writes := by
    by_cases positive : 0 < sign
    · by_cases loss : 0 < lost
      · obtain ⟨middle,assignment,mf⟩:=increment_assignment_framed context selected h.enter.enter writes fresh outWrite overflowWrite
        let inner : State F := {middle.leaveScope before.enterScope.nextScope before.enterScope.environment with scope:=before.enterScope.scope}
        have innerRun : Exec context before.enterScope (.block [incrementOverflow]) .normal inner :=
          .block (by rfl) (.cons assignment .nil) (by rfl)
        have innerFrame : Frame cutoff before.enterScope inner writes :=
          ApplicationBirthFrame.close_frame (wellScoped_enter h.well) fresh mf
        have innerTest : Exec context before.enterScope (.ite lostPositive (.block [incrementOverflow]) none) .normal inner :=
          .ifTrue (lost_test context h.enter)
            (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,loss]) innerRun
        let target : State F := {inner.leaveScope before.nextScope before.environment with scope:=before.scope}
        have outerRun : Exec context before (.block [.ite lostPositive (.block [incrementOverflow]) none]) .normal target :=
          .block (by rfl) (.cons innerTest .nil) (by rfl)
        refine ⟨target,.ifTrue (sign_test context h) ?_ outerRun,ApplicationBirthFrame.close_frame h.well fresh innerFrame⟩
        simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]
      · let target : State F := {before.enterScope.leaveScope before.nextScope before.environment with scope:=before.scope}
        have inner : Exec context before.enterScope (.ite lostPositive (.block [incrementOverflow]) none) .normal before.enterScope :=
          .ifFalse (lost_test context h.enter)
            (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,loss])
        have outer : Exec context before (.block [.ite lostPositive (.block [incrementOverflow]) none]) .normal target :=
          .block (by rfl) (.cons inner .nil) (by rfl)
        refine ⟨target,.ifTrue (sign_test context h) ?_ outer,
          ApplicationBirthFrame.close_frame h.well fresh (Frame.refl cutoff writes (wellScoped_enter h.well) fresh)⟩
        simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]
    · exact ⟨before,.ifFalse (sign_test context h)
        (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]),Frame.refl cutoff writes h.well fresh⟩
  obtain ⟨target,run,frame⟩:=known
  obtain ⟨_,same⟩:=rounding_unique_at context selected h run actual
  cases same
  exact frame

#print axioms increment_assignment_framed
#print axioms rounding_frame
end RH080Next.FFTPV.MultiplySuffix
