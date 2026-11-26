/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTProductRowPrefix
import FFTWordBounds
import FFTProductBindings
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ProductInner
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

inductive Var where | a | b | work | i | j | carry deriving DecidableEq

def name : Var → String | .a=>"a" | .b=>"b" | .work=>"work" | .i=>"i" | .j=>"j" | .carry=>"carry"
def type : Var → CType | .a|.b|.work=>.pointer .u64 | .i|.j|.carry=>.u64
def value (aObj aStart bObj bStart workObj workStart i j carry : Nat) : Var → Value
  | .a=>.pointer (wordPointer aObj aStart)
  | .b=>.pointer (wordPointer bObj bStart)
  | .work=>.pointer (wordPointer workObj workStart)
  | .i=>.integer (integer64 i)
  | .j=>.integer (integer64 j)
  | .carry=>.integer (integer64 carry)

def Slice {F : Type} (state : State F) (object size start : Nat) (coeff : Nat→Nat) : Prop :=
  ∃data,WordArrayRep state object size data ∧ ∀j,j<5 → data (start+j)=coeff j

structure View {F : Type} (state : State F)
    (aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat)
    (ids owners : Var→Nat) (a b data : Nat→Nat) (i j carry : Nat) : Prop where
  work : WordArrayRep state workObj workSize data
  aInput : Slice state aObj aSize aStart a
  bInput : Slice state bObj bSize bStart b
  locals : Bindings state name type ids owners (value aObj aStart bObj bStart workObj workStart i j carry)
  separate : ∀v,workObj≠ids v ∧ aObj≠ids v ∧ bObj≠ids v
  aShape : aObj=workObj → aSize=workSize
  bShape : bObj=workObj → bSize=workSize
  aDisjoint : aObj≠workObj ∨ aStart+5≤workStart ∨ workStart+10≤aStart
  bDisjoint : bObj≠workObj ∨ bStart+5≤workStart ∨ workStart+10≤bStart
  aBound : aStart+5≤aSize
  bBound : bStart+5≤bSize
  workBound : workStart+10≤workSize
  aDigits : ∀k,k<5 → a k<1000000000
  bDigits : ∀k,k<5 → b k<1000000000
  workDigits : ∀k,k<10 → data (workStart+k)<1000000000
  carryBound : carry<1000000000
  row : i<5
  active : j≤5
  well : WellScoped state

private theorem slice_enter {F : Type} {state : State F} {object size start : Nat} {a : Nat→Nat}
    (h : Slice state object size start a) : Slice state.enterScope object size start a := by
  obtain ⟨data,rep,vals⟩:=h
  exact ⟨data,rep,vals⟩

theorem slice_declare {F : Type} {before after : State F} {object size start : Nat}
    {a : Nat→Nat} {cname : String} {ctype : CType} {v : Value}
    (well : WellScoped before) (h : Slice before object size start a)
    (declared : Declaration before after cname ctype v) : Slice after object size start a := by
  obtain ⟨data,rep,vals⟩:=h
  exact ⟨data,array_declare_old well rep declared,vals⟩

theorem array_store_old {F : Type} {before after : State F} {object size : Nat}
    {data : Nat→Nat} {p : Pointer} {v : Value}
    (rep : WordArrayRep before object size data) (different : object≠p.object)
    (written : before.store p v=some after) : WordArrayRep after object size data := by
  obtain ⟨_,mode,_,_,_,outside⟩:=SourceLocals.store_frame written
  exact ⟨mode.trans rep.1,(outside object different).trans rep.2.1,rep.2.2⟩

theorem slice_store_old {F : Type} {before after : State F} {object size start : Nat}
    {a : Nat→Nat} {p : Pointer} {v : Value}
    (h : Slice before object size start a) (different : object≠p.object)
    (written : before.store p v=some after) : Slice after object size start a := by
  obtain ⟨data,rep,vals⟩:=h
  exact ⟨data,array_store_old rep different written,vals⟩

theorem slot_store_exists {F : Type} {state : State F} {id owner : Nat}
    {ctype : CType} {old : Value} (h : Slot state id owner ctype old)
    (v : Value) (hv : Storable ctype v) : ∃after,state.store (scalarPointer id ctype) v=some after := by
  obtain ⟨oldType,present⟩:=h
  have same : old.byteSize=v.byteSize:=Option.some.inj (oldType.typeWidth.symm.trans hv.typeWidth)
  rw [same] at present
  simp [State.store,scalarPointer,present,scalarObject,State.accessible,hv.typeWidth,hv.converted]

theorem View.enter {F : Type} {state : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart i j carry : Nat}
    {ids owners : Var→Nat} {a b data : Nat→Nat}
    (h : View state aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i j carry) :
    View state.enterScope aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i j carry :=
  ⟨h.work,slice_enter h.aInput,slice_enter h.bInput,h.locals.enter,h.separate,h.aShape,h.bShape,
    h.aDisjoint,h.bDisjoint,h.aBound,h.bBound,h.workBound,h.aDigits,h.bDigits,h.workDigits,h.carryBound,
    h.row,h.active,wellScoped_enter h.well⟩

private theorem prefix_locals {F : Type} {before after : State F}
    {workObj t aObj aStart bObj bStart workStart i j carry : Nat} {ids owners : Var→Nat}
    (well : WellScoped before)
    (locals : Bindings before name type ids owners (value aObj aStart bObj bStart workObj workStart i j carry))
    (sep : ∀v,workObj≠ids v) (frame : ProductRow.PrefixFrame before after workObj t) :
    Bindings after name type ids owners (value aObj aStart bObj bStart workObj workStart i j carry) := by
  refine ⟨?_,?_,locals.distinct,?_⟩
  · intro v
    rw [frame.environment]
    have named:=locals.lookup v
    cases v <;> simpa [name,List.lookup] using named
  · intro v
    have old:=well.objectIds _ _ (locals.slots v).object
    exact ⟨(locals.slots v).storable,by rw [frame.oldObjects _ old (sep v).symm]; exact (locals.slots v).object⟩
  · intro v;rw [frame.nextScope];exact locals.bound v

private theorem prefix_slice {F : Type} {before after : State F}
    {workObj workSize workStart object size start k digit t : Nat} {data coeff : Nat→Nat}
    (work : WordArrayRep before workObj workSize data)
    (input : Slice before object size start coeff) (well : WellScoped before)
    (shape : object=workObj → size=workSize)
    (disjoint : object≠workObj ∨ start+5≤workStart ∨ workStart+10≤start)
    (bound : start+5≤size) (hk : k<10)
    (updated : WordArrayRep after workObj workSize (Function.update data (workStart+k) digit))
    (frame : ProductRow.PrefixFrame before after workObj t) : Slice after object size start coeff := by
  obtain ⟨old,inputRep,vals⟩:=input
  by_cases same : object=workObj
  · have sizeEq:=shape same
    subst object;subst size
    refine ⟨Function.update data (workStart+k) digit,updated,?_⟩
    intro j hj
    have different : start+j≠workStart+k := by rcases disjoint with no | lo | hi <;> omega
    rw [Function.update_of_ne different]
    exact (word_data_unique work inputRep _ (by omega)).trans (vals j hj)
  · have oldId:=well.objectIds _ _ inputRep.2.1
    exact ⟨old,⟨updated.1,(frame.oldObjects object oldId same).trans inputRep.2.1,inputRep.2.2⟩,vals⟩

private theorem append_normal {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} (first : ExecList context before xs .normal middle)
    (second : ExecList context middle ys .normal after) :
    ExecList context before (xs++ys) .normal after := by
  induction xs generalizing before with
  | nil => cases first; exact second
  | cons x xs ih =>
    cases first with
    | cons run rest => exact .cons run (ih rest)
    | abrupt run ne => exact False.elim (ne rfl)

/-- The actual five-statement schoolbook source body, including the two
fresh block locals, UInt64 arithmetic, scratch update and carry/counter stores.
The input slices may share an allocation with disjoint scratch space. -/
theorem contents_execution {F : Type} (context : Context F) {before : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart i j carry : Nat}
    {ids owners : Var→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i j carry)
    (hj : j<5) :
    let total:=data (workStart+(i+j))+a i*b j+carry
    ∃after,ExecList context before ProductRow.actualInner .normal after ∧
      View after aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b
        (Function.update data (workStart+(i+j)) (total%1000000000)) i (j+1) (total/1000000000) ∧
      Frame before.nextObject before after [workObj,ids Var.carry,ids Var.j] := by
  dsimp only
  let total:=data (workStart+(i+j))+a i*b j+carry
  have hij : i+j<10:=by have hi:=h.row;omega
  have ht : total<2^64:=schoolbook_digit_safe _ _ _ _ (h.aDigits i h.row) (h.bDigits j hj)
    (h.workDigits (i+j) hij) h.carryBound
  have carryFits : total/1000000000<1000000000:=(schoolbook_next_bounds _ _ _ _
    (h.aDigits i h.row) (h.bDigits j hj) (h.workDigits (i+j) hij) h.carryBound).2
  have kEval : Eval context before ProductRow.kExpr (.integer (integer64 (i+j))) before := by
    exact .paren (.binaryLR (.variable (h.locals.lookup Var.i) (h.locals.read Var.i))
      (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
      (by simp only [value,binary,binary64_add i j (by have hi:=h.row;omega) (by omega) (by omega),Option.map_some]))
  obtain ⟨kState,kDecl⟩:=ZeroFrame.declare_exists h.well .u64 "k" (.integer (integer64 (i+j)))
    (ZeroFrame.u64_storable (i+j) (by omega))
  have dk : Declaration before kState "k" .u64 (.integer (integer64 (i+j))):=
    declare_storable (ZeroFrame.u64_storable (i+j) (by omega)) (convert64 (i+j) (by omega)) kDecl
  have kRun : Exec context before (.declare .u64 "k" (some ProductRow.kExpr)) .normal kState:=.declareSome kEval kDecl
  have kw:=wellScoped_declare h.well kDecl
  have kl:=h.locals.declare h.well (by intro v;cases v <;> decide) dk
  have workK:=array_declare_old h.well h.work dk
  have aK:=slice_declare h.well h.aInput dk
  have bK:=slice_declare h.well h.bInput dk
  obtain ⟨ad,aRep,aVals⟩:=aK
  obtain ⟨bd,bRep,bVals⟩:=bK
  have readA : Eval context kState (ProductRow.arrayAt "a" "i") (.integer (integer64 (a i))) kState := by
    have e:=ProductRow.source_index_eval context kState "a" "i" _ _ aRep (by have hb:=h.aBound;have hi:=h.row;omega)
      (kl.lookup Var.a) (kl.read Var.a) (kl.lookup Var.i) (kl.read Var.i)
    simpa only [aVals i h.row] using e
  have readB : Eval context kState (ProductRow.arrayAt "b" "j") (.integer (integer64 (b j))) kState := by
    have e:=ProductRow.source_index_eval context kState "b" "j" _ _ bRep (by have hb:=h.bBound;omega)
      (kl.lookup Var.b) (kl.read Var.b) (kl.lookup Var.j) (kl.read Var.j)
    simpa only [bVals j hj] using e
  obtain ⟨middle,prefixRun,workM,carryEval,conservation,prefixFrame⟩:=
    ProductRow.t_digit_prefix_execution context kState kw (ids Var.work) (owners Var.work) before.nextObject before.scope
      workObj workSize workStart (i+j) (a i) (b j) carry data workK
      (by have hb:=h.workBound;omega) (kl.lookup Var.work) (kl.slots Var.work)
      (by rw [dk.environment];rfl) dk.slot
      (h.aDigits i h.row) (h.bDigits j hj) (h.workDigits (i+j) hij) h.carryBound
      readA readB (.variable (kl.lookup Var.carry) (kl.read Var.carry))
  have lm:=prefix_locals kw kl (fun v=>(h.separate v).1) prefixFrame
  have am:=prefix_slice workK ⟨ad,aRep,aVals⟩ kw h.aShape h.aDisjoint h.aBound hij workM prefixFrame
  have bm:=prefix_slice workK ⟨bd,bRep,bVals⟩ kw h.bShape h.bDisjoint h.bBound hij workM prefixFrame
  obtain ⟨cState,cWritten⟩:=slot_store_exists (lm.slots Var.carry) (.integer (integer64 (total/1000000000)))
    (ZeroFrame.u64_storable _ (by omega))
  have carryRun : Exec context middle (.assign (.variable "carry") ProductRow.carryExpr) .normal cState:=
    .assign carryEval (.variable (lm.lookup Var.carry)) cWritten
  have lc:=lm.store Var.carry _ (ZeroFrame.u64_storable _ (by omega)) cWritten
  have wc:=array_store_old workM (h.separate Var.carry).1 cWritten
  have ac:=slice_store_old am (h.separate Var.carry).2.1 cWritten
  have bc:=slice_store_old bm (h.separate Var.carry).2.2 cWritten
  have valueC : Function.update (value aObj aStart bObj bStart workObj workStart i j carry) Var.carry
      (.integer (integer64 (total/1000000000)))=
      value aObj aStart bObj bStart workObj workStart i j (total/1000000000) := by
    funext v;cases v <;> simp [value,Function.update]
  rw [valueC] at lc
  obtain ⟨after,jWritten⟩:=slot_store_exists (lc.slots Var.j) (.integer (integer64 (j+1)))
    (ZeroFrame.u64_storable _ (by omega))
  have jRun : Exec context cState ZeroLoop.increment .normal after := by
    exact .assign (.paren (.binaryLR (.variable (lc.lookup Var.j) (lc.read Var.j))
      (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
      (by simp only [value,binary,binary64_add j 1 (by omega) (by norm_num) (by omega),Option.map_some])))
      (.variable (lc.lookup Var.j)) jWritten
  have la:=lc.store Var.j _ (ZeroFrame.u64_storable _ (by omega)) jWritten
  have valueJ : Function.update (value aObj aStart bObj bStart workObj workStart i j (total/1000000000)) Var.j
      (.integer (integer64 (j+1)))=value aObj aStart bObj bStart workObj workStart i (j+1) (total/1000000000) := by
    funext v;cases v <;> simp [value,Function.update]
  rw [valueJ] at la
  have wa:=array_store_old wc (h.separate Var.j).1 jWritten
  have aa:=slice_store_old ac (h.separate Var.j).2.1 jWritten
  have ba:=slice_store_old bc (h.separate Var.j).2.2 jWritten
  have frameK : Frame before.nextObject before kState [workObj,ids Var.carry,ids Var.j]:=
    ApplicationBirthFrame.declare_frame _ _ h.well (le_refl _) kDecl
  have frameM : Frame before.nextObject kState middle [workObj,ids Var.carry,ids Var.j] := by
    refine ⟨prefixFrame.well,?_,?_,?_,?_,prefixFrame.foreign,?_⟩
    · rw [prefixFrame.nextObject,dk.nextObject];omega
    · rw [prefixFrame.nextObject];omega
    · rw [prefixFrame.nextScope]
    · exact workM.1.trans workK.1.symm
    · intro id old absent
      apply prefixFrame.oldObjects id (by rw [dk.nextObject];omega)
      simp only [List.mem_cons,List.mem_singleton,not_or] at absent
      exact absent.1
  have frameC : Frame before.nextObject middle cState [workObj,ids Var.carry,ids Var.j]:=
    ApplicationBirthFrame.store_frame _ _ prefixFrame.well frameM.fresh (Or.inl (by simp [scalarPointer])) cWritten
  have frameA : Frame before.nextObject cState after [workObj,ids Var.carry,ids Var.j]:=
    ApplicationBirthFrame.store_frame _ _ frameC.well frameC.fresh (Or.inl (by simp [scalarPointer])) jWritten
  refine ⟨after,?_,⟨wa,aa,ba,la,h.separate,h.aShape,h.bShape,h.aDisjoint,h.bDisjoint,h.aBound,h.bBound,
    h.workBound,h.aDigits,h.bDigits,?_,carryFits,h.row,by omega,frameA.well⟩,
    (frameK.trans frameM).trans (frameC.trans frameA)⟩
  · rw [ProductRow.actual_inner_shape]
    exact .cons kRun (by simpa using append_normal prefixRun (.cons carryRun (.cons jRun .nil)))
  · intro k hk
    by_cases same : workStart+k=workStart+(i+j)
    · simp [Function.update,same,Nat.mod_lt _ (by norm_num : 0<1000000000)]
    · simpa [Function.update_of_ne same] using h.workDigits k hk

#print axioms contents_execution
end RH080Next.FFTPV.ProductInner
