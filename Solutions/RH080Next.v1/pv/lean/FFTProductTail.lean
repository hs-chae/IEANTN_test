/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTProductOuter
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ProductOuter
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

def carryIndex : Expr:=.paren (.binary .add (.variable "i") (.literal (.integer 5 "ULL")))
def carryStore : Stmt:=.assign (.index (.variable "work") carryIndex) (.variable "carry")
def incrementI : Stmt:=.assign (.variable "i") (.paren (.binary .add (.variable "i") (.literal (.integer 1 "ULL"))))

theorem actual_tail : (ProductRow.items (ProductRow.whileBody
    ((ProductRow.items fixed_multiply_ast.body).getD 2 (.block [])))).drop 3=[carryStore,incrementI] := by rfl

def embed : PVar→ProductInner.Var | .a=>.a | .b=>.b | .work=>.work | .i=>.i

theorem embed_injective : Function.Injective embed := by intro u v h;cases u <;> cases v <;> cases h <;> rfl

theorem persistent_bindings {F : Type} {state : State F}
    {aObj aStart bObj bStart workObj workStart i j carry jId cId rowScope : Nat}
    {ids owners : PVar→Nat}
    (h : ProductInner.Bindings state ProductInner.name ProductInner.type
      (rowIds ids jId cId) (rowOwners owners rowScope)
      (ProductInner.value aObj aStart bObj bStart workObj workStart i j carry)) :
    ProductInner.Bindings state name type ids owners (value aObj aStart bObj bStart workObj workStart i) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro v;cases v
    · exact h.lookup ProductInner.Var.a
    · exact h.lookup ProductInner.Var.b
    · exact h.lookup ProductInner.Var.work
    · exact h.lookup ProductInner.Var.i
  · intro v;cases v
    · exact h.slots ProductInner.Var.a
    · exact h.slots ProductInner.Var.b
    · exact h.slots ProductInner.Var.work
    · exact h.slots ProductInner.Var.i
  · intro u v same
    apply embed_injective
    apply h.distinct
    cases u <;> cases v <;> exact same
  · intro v;cases v
    · exact h.bound ProductInner.Var.a
    · exact h.bound ProductInner.Var.b
    · exact h.bound ProductInner.Var.work
    · exact h.bound ProductInner.Var.i

/-- A genuine scratch-word write preserves arbitrary aliased input allocations
when the five input words and ten scratch words are disjoint slices. -/
theorem slice_word_store {F : Type} {before after : State F}
    {workObj workSize workStart object size start k digit : Nat} {data coeff : Nat→Nat}
    (work : WordArrayRep before workObj workSize data)
    (input : ProductInner.Slice before object size start coeff)
    (shape : object=workObj → size=workSize)
    (disjoint : object≠workObj ∨ start+5≤workStart ∨ workStart+10≤start)
    (bound : start+5≤size) (hk : k<10)
    (updated : WordArrayRep after workObj workSize (Function.update data (workStart+k) digit))
    (written : before.store (wordPointer workObj (workStart+k)) (.integer (integer64 digit))=some after) :
    ProductInner.Slice after object size start coeff := by
  obtain ⟨old,inputRep,vals⟩:=input
  by_cases same : object=workObj
  · have sizeEq:=shape same
    subst object;subst size
    refine ⟨Function.update data (workStart+k) digit,updated,?_⟩
    intro j hj
    have different : start+j≠workStart+k:=by rcases disjoint with no | lo | hi <;> omega
    rw [Function.update_of_ne different]
    exact (word_data_unique work inputRep _ (by omega)).trans (vals j hj)
  · exact ⟨old,ProductInner.array_store_old inputRep same written,vals⟩

/-- Actual row-tail scratch carry assignment and i increment. The next outer
state has genuine preserved persistent bindings; row-block locals retain their
own owners until the enclosing block is actually closed. -/
theorem tail_execution {F : Type} (context : Context F) {before : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart i carry jId cId rowScope : Nat}
    {ids owners : PVar→Nat} {a b data : Nat→Nat}
    (h : ProductInner.View before aObj aSize aStart bObj bSize bStart workObj workSize workStart
      (rowIds ids jId cId) (rowOwners owners rowScope) a b data i 5 carry) :
    ∃after,ExecList context before [carryStore,incrementI] .normal after ∧
      View after aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b
        (Function.update data (workStart+(i+5)) carry) (i+1) ∧
      Frame before.nextObject before after [workObj,ids PVar.i] := by
  have indexFit : workStart+(i+5)<workSize:=by have hb:=h.workBound;have hi:=h.row;omega
  have cFit : carry<2^64:=by have hc:=h.carryBound;omega
  obtain ⟨middle,written,wm⟩:=word_store_with_rep h.work indexFit cFit
  have indexEval : Eval context before carryIndex (.integer (integer64 (i+5))) before:=
    .paren (.binaryLR (.variable (h.locals.lookup ProductInner.Var.i) (h.locals.read ProductInner.Var.i))
      (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
      (by simp only [ProductInner.value,binary,binary64_add i 5 (by have hi:=h.row;omega) (by norm_num) (by have hi:=h.row;omega),Option.map_some]))
  have carryRun : Exec context before carryStore .normal middle:=
    .assign (.variable (h.locals.lookup ProductInner.Var.carry) (h.locals.read ProductInner.Var.carry))
      (.index (.variable (h.locals.lookup ProductInner.Var.work) (h.locals.read ProductInner.Var.work))
        indexEval (slice_pointer_add h.work indexFit)) written
  have lm:=h.locals.store_other (fun v=>(h.separate v).1.symm) written
  have am:=slice_word_store h.work h.aInput h.aShape h.aDisjoint h.aBound (by have hi:=h.row;omega) wm written
  have bm:=slice_word_store h.work h.bInput h.bShape h.bDisjoint h.bBound (by have hi:=h.row;omega) wm written
  obtain ⟨after,iWritten⟩:=ProductInner.slot_store_exists (lm.slots ProductInner.Var.i)
    (.integer (integer64 (i+1))) (ZeroFrame.u64_storable _ (by have hi:=h.row;omega))
  have iRun : Exec context middle incrementI .normal after:=
    .assign (.paren (.binaryLR (.variable (lm.lookup ProductInner.Var.i) (lm.read ProductInner.Var.i))
      (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
      (by simp only [ProductInner.value,binary,binary64_add i 1 (by have hi:=h.row;omega) (by norm_num) (by have hi:=h.row;omega),Option.map_some])))
      (.variable (lm.lookup ProductInner.Var.i)) iWritten
  have la:=lm.store ProductInner.Var.i _ (ZeroFrame.u64_storable _ (by have hi:=h.row;omega)) iWritten
  have veq : Function.update (ProductInner.value aObj aStart bObj bStart workObj workStart i 5 carry)
      ProductInner.Var.i (.integer (integer64 (i+1)))=
      ProductInner.value aObj aStart bObj bStart workObj workStart (i+1) 5 carry := by
    funext v;cases v <;> simp [ProductInner.value,Function.update]
  rw [veq] at la
  have wa:=ProductInner.array_store_old wm (h.separate ProductInner.Var.i).1 iWritten
  have aa:=ProductInner.slice_store_old am (h.separate ProductInner.Var.i).2.1 iWritten
  have ba:=ProductInner.slice_store_old bm (h.separate ProductInner.Var.i).2.2 iWritten
  have first : Frame before.nextObject before middle [workObj,ids PVar.i]:=
    ApplicationBirthFrame.store_frame _ _ h.well (le_refl _) (Or.inl (by simp [wordPointer])) written
  have second : Frame before.nextObject middle after [workObj,ids PVar.i]:=
    ApplicationBirthFrame.store_frame _ _ first.well first.fresh
      (Or.inl (by simp [scalarPointer,rowIds])) iWritten
  refine ⟨after,.cons carryRun (.cons iRun .nil),⟨wa,aa,ba,persistent_bindings la,?_,h.aShape,h.bShape,
    h.aDisjoint,h.bDisjoint,h.aBound,h.bBound,h.workBound,h.aDigits,h.bDigits,?_,by have hi:=h.row;omega,second.well⟩,
    first.trans second⟩
  · intro v;cases v
    · exact h.separate ProductInner.Var.a
    · exact h.separate ProductInner.Var.b
    · exact h.separate ProductInner.Var.work
    · exact h.separate ProductInner.Var.i
  · intro k hk
    by_cases same : workStart+k=workStart+(i+5)
    · simpa [Function.update,same] using h.carryBound
    · simpa [Function.update_of_ne same] using h.workDigits k hk

#print axioms actual_tail
#print axioms persistent_bindings
#print axioms slice_word_store
#print axioms tail_execution
end RH080Next.FFTPV.ProductOuter
