/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTProductTail
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ProductOuter
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

def outerBody : Stmt:=.block (rowDeclarations++[ProductInner.innerLoop,carryStore,incrementI])
def outerCondition : Expr:=.binary .lt (.variable "i") (.literal (.integer 5 "ULL"))
def outerLoop : Stmt:=.whileLoop outerCondition outerBody

theorem actual_outer_loop : (ProductRow.items fixed_multiply_ast.body).getD 2 (.block [])=outerLoop:=by rfl

theorem View.enter {F : Type} {state : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart i : Nat}
    {ids owners : PVar→Nat} {a b data : Nat→Nat}
    (h : View state aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i) :
    View state.enterScope aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i := by
  obtain ⟨ad,ar,av⟩:=h.aInput
  obtain ⟨bd,br,bv⟩:=h.bInput
  exact ⟨h.work,⟨ad,ar,av⟩,⟨bd,br,bv⟩,h.locals.enter,h.separate,h.aShape,h.bShape,h.aDisjoint,h.bDisjoint,
    h.aBound,h.bBound,h.workBound,h.aDigits,h.bDigits,h.workDigits,h.row,wellScoped_enter h.well⟩

private theorem append_normal {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} (first : ExecList context before xs .normal middle)
    (second : ExecList context middle ys .normal after) :
    ExecList context before (xs++ys) .normal after := by
  induction xs generalizing before with
  | nil => cases first;exact second
  | cons x xs ih =>
    cases first with
    | cons run rest => exact .cons run (ih rest)
    | abrupt run ne => exact False.elim (ne rfl)

/-- Exact source row output, before the next row is initialized. -/
def rowResult (workStart i : Nat) (a b data : Nat→Nat) : Nat→Nat:=
  let r:=RH080Next.FFT.Limbs.row 1000000000 (workStart+i) (a i) b data 5
  Function.update r.1 (workStart+(i+5)) r.2

/-- One complete actual outer source row: row-local births, the entire five
product-digit loop, terminal carry write, i increment and real scope exit.
All old caller data outside scratch and i are framed. -/
theorem block_execution {F : Type} (context : Context F) {before : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart i : Nat}
    {ids owners : PVar→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i)
    (hi : i<5) :
    ∃after,Exec context before outerBody .normal after ∧
      View after aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b
        (rowResult workStart i a b data) (i+1) ∧
      Frame before.nextObject before after [workObj,ids PVar.i] := by
  obtain ⟨initialized,initRun,ih,initFrame⟩:=initialize_row context h.enter hi
  obtain ⟨rowState,rowRun,rh,rowFrame,rowValue⟩:=ProductInner.source_five_digit_row context ih
  obtain ⟨middle,tailRun,mh,tailFrame⟩:=tail_execution context rh
  have initWide : Frame before.nextObject before.enterScope initialized [workObj,ids PVar.i]:=
    ⟨initFrame.well,initFrame.fresh,initFrame.nextObject,initFrame.nextScope,initFrame.mode,initFrame.foreign,
      fun id old _=>initFrame.outside id old (by simp)⟩
  have rowNarrow : Frame before.nextObject initialized rowState [workObj,ids PVar.i]:=by
    refine ⟨rowFrame.well,initWide.fresh.trans rowFrame.nextObject,rowFrame.nextObject,rowFrame.nextScope,
      rowFrame.mode,rowFrame.foreign,?_⟩
    intro id old absent
    apply rowFrame.outside id (old.trans_le initWide.nextObject)
    simp only [rowIds,List.mem_cons,List.not_mem_nil,or_false,not_or] at absent ⊢
    exact ⟨absent.1,by change id≠before.nextObject+1;omega,by change id≠before.nextObject;omega⟩
  have leadingFrame:=initWide.trans rowNarrow
  have tailNarrow : Frame before.nextObject rowState middle [workObj,ids PVar.i]:=
    ⟨tailFrame.well,leadingFrame.fresh.trans tailFrame.nextObject,tailFrame.nextObject,tailFrame.nextScope,
      tailFrame.mode,tailFrame.foreign,fun id old absent=>tailFrame.outside id (old.trans_le leadingFrame.nextObject) absent⟩
  have bodyFrame:=leadingFrame.trans tailNarrow
  let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
  have bodyRun : Exec context before outerBody .normal after:=by
    apply Exec.block (by rfl) ?_ (by rfl)
    exact append_normal initRun (.cons rowRun tailRun)
  have closed:=close_frame h.well (le_refl _) bodyFrame
  have locals:=mh.locals.leave (scope:=before.nextScope) (restore:=before.scope)
    (by intro v;have ho:=h.locals.bound v;omega) before.environment h.locals.lookup
  have arrayLeave {object size : Nat} {d : Nat→Nat} (rep : WordArrayRep middle object size d) :
      WordArrayRep after object size d:=by
    refine ⟨rep.1,?_,rep.2.2⟩
    change (middle.objects object).map _=some (wordObject size d)
    rw [rep.2.1];rfl
  obtain ⟨ad,ar,av⟩:=mh.aInput
  obtain ⟨bd,br,bv⟩:=mh.bInput
  exact ⟨after,bodyRun,⟨arrayLeave mh.work,⟨ad,arrayLeave ar,av⟩,⟨bd,arrayLeave br,bv⟩,
    locals,mh.separate,mh.aShape,mh.bShape,mh.aDisjoint,mh.bDisjoint,mh.aBound,mh.bBound,mh.workBound,
    mh.aDigits,mh.bDigits,mh.workDigits,mh.row,closed.well⟩,closed⟩

private theorem condition_eval {F : Type} (context : Context F) {before : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart i : Nat}
    {ids owners : PVar→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i) :
    Eval context before outerCondition (.integer (.boolean (decide (i<5)))) before:=
  .binaryLR (.variable (h.locals.lookup PVar.i) (h.locals.read PVar.i))
    (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
    (by simp only [value,binary,binary64_lt i 5 (by have hi:=h.row;omega) (by norm_num),Option.map_some])

def advance (workStart : Nat) (a b : Nat→Nat) : Nat→(Nat→Nat)→Nat→(Nat→Nat)
  | _,data,0=>data
  | i,data,steps+1=>advance workStart a b (i+1) (rowResult workStart i a b data) steps

/-- The complete actual nested source multiplication while loops, for all
five rows, refine the exact row algorithm with bounded UInt64 operations.
This is the multiplication core, before sign/drop/copy/rounding code. -/
theorem loop_execution {F : Type} (context : Context F) (steps : Nat) {before : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart i : Nat}
    {ids owners : PVar→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i)
    (remaining : i+steps=5) :
    ∃after,Exec context before outerLoop .normal after ∧
      View after aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b
        (advance workStart a b i data steps) 5 ∧
      Frame before.nextObject before after [workObj,ids PVar.i] := by
  induction steps generalizing before i data with
  | zero =>
    have hi : i=5:=by omega
    subst i
    exact ⟨before,.whileFalse (condition_eval context h)
      (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed]),h,
      Frame.refl _ _ h.well (le_refl _)⟩
  | succ steps ih =>
    have hi : i<5:=by omega
    obtain ⟨middle,first,hm,frame⟩:=block_execution context h hi
    obtain ⟨after,rest,ha,restFrame⟩:=ih hm (by omega)
    have shrink : Frame before.nextObject middle after [workObj,ids PVar.i]:=
      ⟨restFrame.well,frame.fresh.trans restFrame.nextObject,restFrame.nextObject,restFrame.nextScope,
        restFrame.mode,restFrame.foreign,fun id old absent=>restFrame.outside id (old.trans_le frame.nextObject) absent⟩
    refine ⟨after,.whileNext (condition_eval context h) ?_ first rest,ha,frame.trans shrink⟩
    simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hi]

#print axioms actual_outer_loop
#print axioms block_execution
#print axioms loop_execution
end RH080Next.FFTPV.ProductOuter
