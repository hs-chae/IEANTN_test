/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTProductAllExecutions
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ProductOuter
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open ApplicationBirthFrame

theorem rowResult_untouched (start i : Nat) (a b data : Nat→Nat) (k : Nat)
    (hi : i<5) (outside : k<start ∨ start+10≤k) : rowResult start i a b data k=data k := by
  unfold rowResult
  rw [Function.update_of_ne (by omega : k≠start+(i+5))]
  exact RH080Next.FFT.Limbs.row_untouched _ _ _ _ _ _ _ (by omega)

theorem advance_untouched (start i steps : Nat) (a b data : Nat→Nat) (k : Nat)
    (range : i+steps≤5) (outside : k<start ∨ start+10≤k) : advance start a b i data steps k=data k := by
  induction steps generalizing i data with
  | zero=>rfl
  | succ steps ih=>
    change advance start a b (i+1) (rowResult start i a b data) steps k=data k
    rw [ih (i:=i+1) (data:=rowResult start i a b data) (by omega)]
    exact rowResult_untouched start i a b data k (by omega) outside

theorem block_environment {F : Type} {context : Context F} {before after : State F} {flow : Flow}
    (run : Exec context before outerBody flow after) : after.environment=before.environment := by
  cases run with
  | block entered body closed=>subst_vars;rfl

theorem loop_execution_environment {F : Type} (context : Context F) (steps : Nat) {before : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart i : Nat}
    {ids owners : PVar→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i)
    (remaining : i+steps=5) :
    ∃after,Exec context before outerLoop .normal after ∧
      View after aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b
        (advance workStart a b i data steps) 5 ∧
      Frame before.nextObject before after [workObj,ids PVar.i] ∧ after.environment=before.environment := by
  induction steps generalizing before i data with
  | zero=>
    obtain ⟨after,run,ha,frame⟩:=loop_execution context 0 h remaining
    have equal : after=before:=by
      have hi : i=5:=by omega
      have alternative : Exec context before outerLoop .normal before:=by
        have base:=h
        subst i
        have ev : Eval context before outerCondition (.integer (.boolean (decide (5<5)))) before:=
          .binaryLR (.variable (h.locals.lookup PVar.i) (h.locals.read PVar.i))
            (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
            (by simp only [value,binary,binary64_lt 5 5 (by norm_num) (by norm_num),Option.map_some])
        exact .whileFalse ev (by decide)
      exact (outer_loop_unique context run alternative).2
    subst after
    exact ⟨before,run,ha,frame,rfl⟩
  | succ steps ih=>
    have hi : i<5:=by omega
    obtain ⟨middle,first,hm,frame⟩:=block_execution context h hi
    obtain ⟨after,rest,ha,restFrame,env⟩:=ih hm (by omega)
    have shrink : Frame before.nextObject middle after [workObj,ids PVar.i]:=
      ⟨restFrame.well,frame.fresh.trans restFrame.nextObject,restFrame.nextObject,restFrame.nextScope,
        restFrame.mode,restFrame.foreign,fun id old absent=>restFrame.outside id (old.trans_le frame.nextObject) absent⟩
    have condition : Eval context before outerCondition (.integer (.boolean true)) before:=by
      have e : Eval context before outerCondition (.integer (.boolean (decide (i<5)))) before:=
        .binaryLR (.variable (h.locals.lookup PVar.i) (h.locals.read PVar.i))
          (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
          (by simp only [value,binary,binary64_lt i 5 (by omega) (by norm_num),Option.map_some])
      simpa only [hi,decide_true] using e
    exact ⟨after,.whileNext condition (by decide) first rest,ha,frame.trans shrink,env.trans (block_environment first)⟩

theorem every_core_state {F : Type} {context : Context F} {before after : State F} {flow : Flow}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat}
    {ids owners : PVar→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data 0)
    (run : Exec context before outerLoop flow after) :
    flow=.normal ∧
      View after aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b
        (advance workStart a b 0 data 5) 5 ∧
      Frame before.nextObject before after [workObj,ids PVar.i] ∧ after.environment=before.environment := by
  obtain ⟨canonical,canonicalRun,ha,frame,env⟩:=loop_execution_environment context 5 h (by rfl)
  obtain ⟨flowEq,stateEq⟩:=outer_loop_unique context run canonicalRun
  cases stateEq
  exact ⟨flowEq,ha,frame,env⟩

/-- Real typed input words outside scratch, including the sixth sign word,
remain unchanged in every core execution even in one shared allocation. -/
theorem every_core_read {F : Type} {context : Context F} {before after : State F} {flow : Flow}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart object size index : Nat}
    {ids owners : PVar→Nat} {a b data input : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data 0)
    (rep : WordArrayRep before object size input) (bound : index<size)
    (shape : object=workObj → size=workSize) (separate : object≠ids PVar.i)
    (outside : object≠workObj ∨ index<workStart ∨ workStart+10 ≤ index)
    (run : Exec context before outerLoop flow after) :
    after.load (wordPointer object index)=some (.integer (integer64 (input index))) := by
  obtain ⟨normal,ha,frame,env⟩:=every_core_state h run
  by_cases same : object=workObj
  · have sameSize:=shape same
    subst object;subst size
    have original:=word_data_unique h.work rep index bound
    have untouched:=advance_untouched workStart 0 5 a b data index (by norm_num)
      (by rcases outside with no | low | high;exact False.elim (no rfl);exact Or.inl low;exact Or.inr high)
    have loaded:=word_load ha.work bound
    simpa only [untouched,original] using loaded
  · have old:=h.well.objectIds _ _ rep.2.1
    have preserved : WordArrayRep after object size input:=
      ⟨ha.work.1,(frame.outside object old (by simp [same,separate])).trans rep.2.1,rep.2.2⟩
    exact word_load preserved bound

#print axioms rowResult_untouched
#print axioms advance_untouched
#print axioms loop_execution_environment
#print axioms every_core_state
#print axioms every_core_read
end RH080Next.FFTPV.ProductOuter
