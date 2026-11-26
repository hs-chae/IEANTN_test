/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTProductInner
import FFTWordSubtraction
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ProductInner
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

def innerBody : Stmt:=.block ProductRow.actualInner
def innerCondition : Expr:=.binary .lt (.variable "j") (.literal (.integer 5 "ULL"))
def innerLoop : Stmt:=.whileLoop innerCondition innerBody

theorem actual_loop : (ProductRow.items (ProductRow.whileBody
    ((ProductRow.items fixed_multiply_ast.body).getD 2 (.block [])))).getD 2 (.block [])=innerLoop := by rfl

private theorem array_leave {F : Type} {state : State F} {object size scope restore : Nat}
    {data : Nat→Nat} (environment : List (String×Pointer)) (h : WordArrayRep state object size data) :
    WordArrayRep {state.leaveScope scope environment with scope:=restore} object size data := by
  refine ⟨h.1,?_,h.2.2⟩
  change (state.objects object).map _=some (wordObject size data)
  rw [h.2.1]
  rfl

private theorem slice_leave {F : Type} {state : State F} {object size start scope restore : Nat}
    {coeff : Nat→Nat} (environment : List (String×Pointer)) (h : Slice state object size start coeff) :
    Slice {state.leaveScope scope environment with scope:=restore} object size start coeff := by
  obtain ⟨data,rep,vals⟩:=h
  exact ⟨data,array_leave environment rep,vals⟩

/-- The complete real source block closes both k and t lifetimes and restores
all source bindings while preserving input slices and the scratch invariant. -/
theorem block_execution {F : Type} (context : Context F) {before : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart i j carry : Nat}
    {ids owners : Var→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i j carry)
    (hj : j<5) :
    let total:=data (workStart+(i+j))+a i*b j+carry
    ∃after,Exec context before innerBody .normal after ∧
      View after aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b
        (Function.update data (workStart+(i+j)) (total%1000000000)) i (j+1) (total/1000000000) ∧
      Frame before.nextObject before after [workObj,ids Var.carry,ids Var.j] := by
  dsimp only
  obtain ⟨middle,run,hm,frame⟩:=contents_execution context h.enter hj
  let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
  have blockRun : Exec context before innerBody .normal after:=.block (by rfl) run (by rfl)
  have closed:=close_frame h.well (le_refl _) frame
  have different : ∀v,before.nextScope≠owners v:=by intro v;have ho:=h.locals.bound v;omega
  have locals:=hm.locals.leave (restore:=before.scope) different before.environment h.locals.lookup
  exact ⟨after,blockRun,⟨array_leave before.environment hm.work,slice_leave before.environment hm.aInput,
    slice_leave before.environment hm.bInput,locals,hm.separate,hm.aShape,hm.bShape,hm.aDisjoint,hm.bDisjoint,
    hm.aBound,hm.bBound,hm.workBound,hm.aDigits,hm.bDigits,hm.workDigits,hm.carryBound,hm.row,hm.active,closed.well⟩,closed⟩

private theorem condition_eval {F : Type} (context : Context F) {before : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart i j carry : Nat}
    {ids owners : Var→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i j carry) :
    Eval context before innerCondition (.integer (.boolean (decide (j<5)))) before := by
  exact .binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
    (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
    (by simp only [value,binary,binary64_lt j 5 (by have hj:=h.active;omega) (by norm_num),Option.map_some])

/-- The exact imperative row recurrence, parameterized by the real scratch
subrange. This functional model is a target for source refinement, not an
assumed arithmetic or execution fact. -/
def advance (workStart i : Nat) (a b : Nat→Nat) : Nat → Nat → (Nat→Nat) → Nat → ((Nat→Nat)×Nat)
  | _,carry,data,0=>(data,carry)
  | j,carry,data,steps+1=>
      let total:=data (workStart+(i+j))+a i*b j+carry
      advance workStart i a b (j+1) (total/1000000000)
        (Function.update data (workStart+(i+j)) (total%1000000000)) steps

/-- Constructive termination and exact output of the actual C inner while,
for every remaining step count through the fixed five digits. -/
theorem loop_execution {F : Type} (context : Context F) (steps : Nat) {before : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart i j carry : Nat}
    {ids owners : Var→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i j carry)
    (remaining : j+steps=5) :
    ∃after,Exec context before innerLoop .normal after ∧
      View after aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b
        (advance workStart i a b j carry data steps).1 i 5
        (advance workStart i a b j carry data steps).2 ∧
      Frame before.nextObject before after [workObj,ids Var.carry,ids Var.j] := by
  induction steps generalizing before j carry data with
  | zero =>
    have he : j=5:=by omega
    subst j
    exact ⟨before,.whileFalse (condition_eval context h)
      (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed]),h,
      Frame.refl _ _ h.well (le_refl _)⟩
  | succ steps ih =>
    have hj : j<5:=by omega
    obtain ⟨middle,first,hm,frame⟩:=block_execution context h hj
    obtain ⟨after,rest,ha,restFrame⟩:=ih hm (by omega)
    have shrink : Frame before.nextObject middle after [workObj,ids Var.carry,ids Var.j]:=
      ⟨restFrame.well,frame.fresh.trans restFrame.nextObject,restFrame.nextObject,restFrame.nextScope,
        restFrame.mode,restFrame.foreign,fun id old absent=>restFrame.outside id (old.trans_le frame.nextObject) absent⟩
    refine ⟨after,.whileNext (condition_eval context h) ?_ first rest,ha,frame.trans shrink⟩
    simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hj]

/-- Five source updates are definitionally the schoolbook row recurrence,
after proving the scratch-offset addition identities. -/
theorem five_step_model (workStart i : Nat) (a b data : Nat→Nat) :
    advance workStart i a b 0 0 data 5=
      RH080Next.FFT.Limbs.row 1000000000 (workStart+i) (a i) b data 5 := by
  simp only [advance,RH080Next.FFT.Limbs.row,Nat.add_zero,Nat.zero_add,Nat.add_assoc]

/-- Actual complete five-digit source loop, preserved caller inputs, and
full integer-valued row conservation; no product/output certificate is assumed. -/
theorem source_five_digit_row {F : Type} (context : Context F) {before : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart i : Nat}
    {ids owners : Var→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i 0 0) :
    let r:=RH080Next.FFT.Limbs.row 1000000000 (workStart+i) (a i) b data 5
    ∃after,Exec context before innerLoop .normal after ∧
      View after aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b r.1 i 5 r.2 ∧
      Frame before.nextObject before after [workObj,ids Var.carry,ids Var.j] ∧
      RH080Next.FFT.Limbs.value 1000000000 workSize r.1+(r.2:Int)*1000000000^(workStart+i+5)=
        RH080Next.FFT.Limbs.value 1000000000 workSize data+
          (a i:Int)*RH080Next.FFT.Limbs.value 1000000000 5 b*1000000000^(workStart+i) := by
  obtain ⟨after,run,ha,frame⟩:=loop_execution context 5 h (by rfl)
  rw [five_step_model] at ha
  exact ⟨after,run,ha,frame,RH080Next.FFT.Limbs.row_value _ _ _ _ _ _ _
    (by have hb:=h.workBound;have hi:=h.row;omega)⟩

#print axioms five_step_model
#print axioms source_five_digit_row
#print axioms actual_loop
#print axioms block_execution
#print axioms loop_execution
end RH080Next.FFTPV.ProductInner
