/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixStore
import ExplicitFFTIncrementFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ProductInner

abbrev TVar := Sum MVar Unit
def tailName : TVar → String := extend midName "overflow"
def tailType : TVar → CType := extend midType .u64
def tailValues (outObj outStart workObj workStart sign lost overflow : Nat) : TVar → Value :=
  extend (midValues outObj outStart workObj workStart 5 sign lost) (.integer (integer64 overflow))

structure RoundView {F : Type} (state : State F)
    (outObj outSize outStart workObj workSize workStart : Nat)
    (ids owners : TVar → Nat) (outData scratch : Nat → Nat) (sign lost overflow : Nat) : Prop where
  output : WordArrayRep state outObj outSize outData
  work : ∃data,WordArrayRep state workObj workSize data ∧ ∀k,k < 10 → data (workStart+k)=scratch k
  locals : Bindings state tailName tailType ids owners (tailValues outObj outStart workObj workStart sign lost overflow)
  separate : ∀v,outObj≠ids v ∧ workObj≠ids v
  shape : workObj=outObj → workSize=outSize
  disjoint : outObj≠workObj ∨ outStart+6≤workStart ∨ workStart+10≤outStart
  outBound : outStart+6≤outSize
  workBound : workStart+10≤workSize
  digits : ∀k,k < 5 → outData (outStart+k) < 1000000000
  signBound : sign≤1
  lostFits : lost < 2^64
  overflowBound : overflow≤1000000000
  well : WellScoped state

theorem RoundView.enter {F : Type} {state : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView state outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow) :
    RoundView state.enterScope outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow :=
  ⟨h.output,h.work,h.locals.enter,h.separate,h.shape,h.disjoint,h.outBound,h.workBound,h.digits,
    h.signBound,h.lostFits,h.overflowBound,wellScoped_enter h.well⟩

private theorem bindings_after_increment {F : Type} {before after : State F}
    {outObj outStart workObj workStart sign lost overflow : Nat} {ids owners : TVar → Nat}
    (h : Bindings before tailName tailType ids owners (tailValues outObj outStart workObj workStart sign lost overflow))
    (well : WellScoped before) (frame : IncrementSource.FullCallerFrame before after outObj)
    (separate : ∀v,outObj≠ids v) :
    Bindings after tailName tailType ids owners (tailValues outObj outStart workObj workStart sign lost overflow) := by
  refine ⟨?_,?_,h.distinct,fun v => (h.bound v).trans_le frame.nextScope⟩
  · intro v;rw [frame.environment];exact h.lookup v
  · intro v
    exact ⟨(h.slots v).storable,(frame.objects _ (well.objectIds _ _ (h.slots v).object) (separate v).symm).trans (h.slots v).object⟩

/-- The actual source increment call is executed, and its computed carry is
added through the actual overflow slot. No successful output is postulated. -/
theorem increment_overflow_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow)
    (overflowDigit : overflow < 1000000000) :
    let carry := (FFT.Limbs.incrementDigits 1000000000 (fun k => outData (outStart+k)) 5).2
    ∃after,Exec context before incrementOverflow .normal after ∧
      RoundView after outObj outSize outStart workObj workSize workStart ids owners
        (IncrementSource.currentData outData outStart 5) scratch sign lost (overflow+carry) ∧
      before.scope=after.scope ∧ before.nextScope≤after.nextScope := by
  dsimp only
  let carry := (FFT.Limbs.incrementDigits 1000000000 (fun k => outData (outStart+k)) 5).2
  have bounds:=FFT.Limbs.incrementDigits_bounds 1000000000 5 (by norm_num) (fun k => outData (outStart+k)) h.digits
  have carryBound : carry≤1:=bounds.1
  obtain ⟨called,callRun,outAfter,frame⟩:=IncrementSource.increment_words_call_framed context selected before
    outObj outSize outStart 5 outData h.well h.output (by have hb:=h.outBound;omega) (by omega) h.digits
  have lc:=bindings_after_increment h.locals h.well frame (fun v => (h.separate v).1)
  obtain ⟨after,written⟩:=scalar_store_exists (lc.slots (.inr ()))
    (.integer (integer64 (overflow+carry))) (ZeroFrame.u64_storable _ (by have ho:=h.overflowBound;omega))
  have args : Args context before [v "out",lit 5]
      [.pointer (wordPointer outObj outStart),.integer (integer64 5)] before := by
    apply Args.ordered (order := [(0,v "out"),(1,lit 5)]) (evaluated :=
      [(0,.pointer (wordPointer outObj outStart)),(1,.integer (integer64 5))]) (by rfl)
    · exact .cons (.variable (h.locals.lookup (.inl MVar.out)) (h.locals.read (.inl MVar.out)))
        (.cons (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl)) .nil)
    · exact .cons (by rfl) (.cons (by rfl) .nil)
  have run : Exec context before incrementOverflow .normal after :=
    .assign (.paren (.binaryLR (.variable (h.locals.lookup (.inr ())) (h.locals.read (.inr ())))
      (.call args callRun)
      (by
        change Option.map Value.integer (Integer.binary .add (integer64 overflow) (integer64 carry)) = _
        rw [binary64_add overflow carry (by have ho:=h.overflowBound;omega) (by omega)
          (by have ho:=h.overflowBound;omega)]
        rfl)))
      (.variable (lc.lookup (.inr ()))) written
  have locals:=lc.store (.inr ()) (.integer (integer64 (overflow+carry)))
    (ZeroFrame.u64_storable _ (by have ho:=h.overflowBound;omega)) written
  have values : Function.update (tailValues outObj outStart workObj workStart sign lost overflow)
      (.inr ()) (.integer (integer64 (overflow+carry))) =
      tailValues outObj outStart workObj workStart sign lost (overflow+carry) := by
    funext x;cases x with
    | inl x => simp [tailValues,extend,Function.update]
    | inr x => cases x;simp [tailValues,extend,Function.update]
  rw [values] at locals
  obtain ⟨data,workRep,workValues⟩:=h.work
  have workAfter : ∃data',WordArrayRep called workObj workSize data' ∧ ∀k,k < 10 → data' (workStart+k)=scratch k := by
    by_cases same : workObj=outObj
    · have size:=h.shape same
      subst workObj;subst workSize
      refine ⟨IncrementSource.currentData outData outStart 5,outAfter,?_⟩
      intro k hk
      have outside : ¬(outStart≤workStart+k ∧ workStart+k < outStart+5) := by
        rcases h.disjoint with no | lo | hi
        · exact False.elim (no rfl)
        · omega
        · omega
      rw [IncrementSource.currentData,if_neg outside]
      exact (word_data_unique h.output workRep _ (by have hb:=h.workBound;omega)).trans (workValues k hk)
    · have old:=h.well.objectIds _ _ workRep.2.1
      exact ⟨data,⟨frame.mode.trans workRep.1,(frame.objects workObj old same).trans workRep.2.1,workRep.2.2⟩,workValues⟩
  obtain ⟨env,mode,scope,ns,no,outside⟩:=SourceLocals.store_frame written
  have output : WordArrayRep after outObj outSize (IncrementSource.currentData outData outStart 5) :=
    ⟨mode.trans outAfter.1,(outside outObj (h.separate (.inr ())).1).trans outAfter.2.1,outAfter.2.2⟩
  obtain ⟨data',rep,vals⟩:=workAfter
  have workFinal : ∃data',WordArrayRep after workObj workSize data' ∧ ∀k,k < 10 → data' (workStart+k)=scratch k :=
    ⟨data',⟨mode.trans rep.1,(outside workObj (h.separate (.inr ())).2).trans rep.2.1,rep.2.2⟩,vals⟩
  have digitBounds : ∀k,k < 5 → IncrementSource.currentData outData outStart 5 (outStart+k) < 1000000000 := by
    intro k hk
    rw [IncrementSource.currentData_slice outData outStart 5 k hk]
    exact bounds.2 k hk
  refine ⟨after,run,⟨output,workFinal,locals,h.separate,h.shape,h.disjoint,h.outBound,h.workBound,digitBounds,
    h.signBound,h.lostFits,?_,wellScoped_store frame.well written⟩,?_,?_⟩
  · have ho:=h.overflowBound
    -- The pre-round overflow is an actual single base-billion digit.
    omega
  · exact (scope.trans frame.scope).symm
  · rw [ns];exact frame.nextScope

private theorem wordArray_leave {F : Type} {state : State F} {object size scope restore : Nat}
    {environment : List (String × Pointer)} {data : Nat → Nat} (h : WordArrayRep state object size data) :
    WordArrayRep {state.leaveScope scope environment with scope:=restore} object size data := by
  refine ⟨h.1,?_,h.2.2⟩
  change (state.objects object).map _=some _
  rw [h.2.1]
  simp [wordObject]

theorem RoundView.leave {F : Type} {state : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow closing restore : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView state outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow)
    (different : ∀v,closing≠owners v) (environment : List (String × Pointer))
    (lookup : ∀v,environment.lookup (tailName v)=some (scalarPointer (ids v) (tailType v)))
    (fit : restore < state.nextScope) :
    RoundView {state.leaveScope closing environment with scope:=restore}
      outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow := by
  obtain ⟨data,rep,vals⟩:=h.work
  exact ⟨wordArray_leave h.output,⟨data,wordArray_leave rep,vals⟩,h.locals.leave different environment lookup,
    h.separate,h.shape,h.disjoint,h.outBound,h.workBound,h.digits,h.signBound,h.lostFits,h.overflowBound,
    wellScoped_scope (wellScoped_leave h.well closing environment) fit⟩

theorem binary64_gt (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    Integer.binary .gt (integer64 a) (integer64 b)=some (.boolean (decide (b < a))) := by
  change some (Integer.boolean ((Integer.cast .u64 (a:Int)).toInt > (Integer.cast .u64 (b:Int)).toInt)) = _
  rw [cast64_exact a ha,cast64_exact b hb,integer64_toInt,integer64_toInt]
  congr 2
  simp

private theorem sign_condition {F : Type} (context : Context F) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow) :
    Eval context before roundCondition (.integer (.boolean (decide (0 < sign)))) before :=
  .binaryLR (.variable (h.locals.lookup (.inl MVar.sign)) (h.locals.read (.inl MVar.sign)))
    (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
    (by simp only [tailValues,extend,Sum.elim_inl,midValues,binary,
      binary64_gt sign 0 (by have hb:=h.signBound;omega) (by norm_num),Option.map_some])

private theorem lost_condition {F : Type} (context : Context F) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow) :
    Eval context before lostPositive (.integer (.boolean (decide (0 < lost)))) before :=
  .binaryLR (.variable (h.locals.lookup (.inl MVar.lost)) (h.locals.read (.inl MVar.lost)))
    (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
    (by simp only [tailValues,extend,Sum.elim_inl,midValues,binary,
      binary64_gt lost 0 h.lostFits (by norm_num),Option.map_some])

def roundedData (old : Nat → Nat) (start sign lost : Nat) : Nat → Nat :=
  if 0 < sign ∧ 0 < lost then IncrementSource.currentData old start 5 else old

def roundingCarry (old : Nat → Nat) (start sign lost : Nat) : Nat :=
  if 0 < sign ∧ 0 < lost then (FFT.Limbs.incrementDigits 1000000000 (fun k => old (start+k)) 5).2 else 0

/-- Both actual nested conditions, the optional increment_words call, and the
real block-scope exits are executed. The nonzero-loss branch is not replaced
by an assumed rounding effect. -/
theorem rounding_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow)
    (overflowDigit : overflow < 1000000000) :
    ∃after,Exec context before roundingBranch .normal after ∧
      RoundView after outObj outSize outStart workObj workSize workStart ids owners
        (roundedData outData outStart sign lost) scratch sign lost (overflow+roundingCarry outData outStart sign lost) := by
  by_cases positive : 0 < sign
  · by_cases loss : 0 < lost
    · obtain ⟨middle,assignment,hm,scopeEq,ns⟩:=increment_overflow_execution context selected h.enter.enter overflowDigit
      let inner : State F := {middle.leaveScope before.enterScope.nextScope before.enterScope.environment with scope:=before.enterScope.scope}
      have innerRun : Exec context before.enterScope (.block [incrementOverflow]) .normal inner :=
        .block (by rfl) (.cons assignment .nil) (by rfl)
      have hi : RoundView inner outObj outSize outStart workObj workSize workStart ids owners
          (IncrementSource.currentData outData outStart 5) scratch sign lost
          (overflow+(FFT.Limbs.incrementDigits 1000000000 (fun k => outData (outStart+k)) 5).2) := by
        apply hm.leave (environment:=before.enterScope.environment)
          (fun v => (ne_of_lt (h.enter.locals.bound v)).symm) h.enter.locals.lookup
        have bound:=h.well.current
        change before.nextScope < middle.nextScope
        change before.nextScope+2≤middle.nextScope at ns
        omega
      have testInner : Exec context before.enterScope (.ite lostPositive (.block [incrementOverflow]) none) .normal inner :=
        .ifTrue (lost_condition context h.enter)
          (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,loss]) innerRun
      let after : State F := {inner.leaveScope before.nextScope before.environment with scope:=before.scope}
      have outerRun : Exec context before (.block [.ite lostPositive (.block [incrementOverflow]) none]) .normal after :=
        .block (by rfl) (.cons testInner .nil) (by rfl)
      have ha : RoundView after outObj outSize outStart workObj workSize workStart ids owners
          (IncrementSource.currentData outData outStart 5) scratch sign lost
          (overflow+(FFT.Limbs.incrementDigits 1000000000 (fun k => outData (outStart+k)) 5).2) := by
        apply hi.leave (environment:=before.environment)
          (fun v => (ne_of_lt (h.locals.bound v)).symm) h.locals.lookup
        have hb:=h.well.current
        have hc:=hi.well.current
        change before.scope < inner.nextScope
        change before.nextScope < inner.nextScope at hc
        omega
      refine ⟨after,.ifTrue (sign_condition context h) ?_ outerRun,?_⟩
      · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]
      · simpa only [roundedData,roundingCarry,positive,loss,and_self,ite_true] using ha
    · let after : State F := {before.enterScope.leaveScope before.nextScope before.environment with scope:=before.scope}
      have branch : Exec context before.enterScope (.ite lostPositive (.block [incrementOverflow]) none) .normal before.enterScope :=
        .ifFalse (lost_condition context h.enter)
          (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,loss])
      have body : Exec context before (.block [.ite lostPositive (.block [incrementOverflow]) none]) .normal after :=
        .block (by rfl) (.cons branch .nil) (by rfl)
      have ha : RoundView after outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow := by
        apply h.enter.leave (environment:=before.environment)
          (fun v => (ne_of_lt (h.locals.bound v)).symm) h.locals.lookup
        have bound:=h.well.current
        change before.scope < before.nextScope+1
        omega
      refine ⟨after,.ifTrue (sign_condition context h) ?_ body,?_⟩
      · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]
      · simpa [roundedData,roundingCarry,loss] using ha
  · refine ⟨before,.ifFalse (sign_condition context h) ?_,?_⟩
    · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]
    · simpa [roundedData,roundingCarry,positive] using h

#print axioms rounding_execution

#print axioms increment_overflow_execution
end RH080Next.FFTPV.MultiplySuffix
