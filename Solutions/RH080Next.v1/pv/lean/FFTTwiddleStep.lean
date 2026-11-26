/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTwiddleInput
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.TwiddleSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

structure Functions {F : Type} (context : Context F) : Prop where
  complex : findFunction context.program "complex_multiply"=some complex_multiply_ast
  multiply : findFunction context.program "fixed_multiply"=some fixed_multiply_ast
  zero : findFunction context.program "zero_words"=some zero_words_ast
  increment : findFunction context.program "increment_words"=some increment_words_ast
  add : findFunction context.program "fixed_add"=some fixed_add_ast
  compare : findFunction context.program "magnitude_compare"=some magnitude_compare_ast
  canonical : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast

theorem locals_after_call {F : Type} {before after : State F} {tableObject workObject n owner j : Nat}
    {ids : Var→Nat} {tableData workData : Nat→Nat} {seed : FFT.IntegerModel.CInt}
    (h : View before tableObject workObject n ids owner j tableData workData seed)
    (frame : MultiplyCall.CallerFrame before after [tableObject,workObject]) :
    Locals after name type ids owner (values tableObject workObject n j) := by
  refine ⟨?_,?_,h.locals.distinct,h.locals.bound.trans_le frame.frame.nextScope⟩
  · intro v;rw [frame.environment];exact h.locals.lookup v
  · intro v
    exact ComplexSource.slot_after_call h.well (h.locals.slots v) frame (by simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or];exact ⟨(h.separate v).1.symm,(h.separate v).2.symm⟩)

theorem pair_congr (a b : Nat→Nat) (ast bst : Nat) (same : ∀d,d<12 → a (ast+d)=b (bst+d)) :
    ComplexSource.pair a ast=ComplexSource.pair b bst := by
  apply Prod.ext
  · exact ComplexSource.represented_congr a b ast bst (fun d hd=>same d (by omega))
  · apply ComplexSource.represented_congr
    intro d hd
    simpa only [Nat.add_assoc] using same (6+d) (by omega)

/-- The actual status assignment executes the verified complex helper at the
actual table/previous/root/work addresses. It preserves the root and every
previous table cell by physical word footprints, not object-frame shortcuts. -/
theorem call_execution {F : Type} (context : Context F) (functions : Functions context)
    {before : State F} {tableObject workObject n owner j : Nat}
    {ids : Var→Nat} {tableData workData : Nat→Nat} {seed : FFT.IntegerModel.CInt}
    (h : View before tableObject workObject n ids owner j tableData workData seed) (inside : j<n/2) :
    ∃after nextTable nextWork,
      Exec context before callStmt .normal after ∧
      View after tableObject workObject n ids owner j nextTable nextWork seed ∧
      ComplexSource.pair nextTable (j*12)=sequence seed j ∧
      (∀c : Fin 2,∀d,d<5 → nextTable (j*12+6*c.val+d)<1000000000) ∧
      (∀c : Fin 2,nextTable (j*12+6*c.val+5)≤1) ∧
      MultiplyCall.CallerFrame before after [tableObject,workObject] ∧
      (∀k,k<512 →46≤k → nextWork k=workData k) ∧
      (∀k,k<n/2*12 → (k<j*12 ∨ j*12+12≤k) → nextTable k=tableData k) ∧
      (∀other flow,Exec context before callStmt flow other → flow=.normal ∧ other=after) := by
  let actualInput:=input h inside
  obtain ⟨after,nextWork,nextTable,called,tableRep,workRep,value,digits,signs,outWork,outTable,frame,every⟩ :=
    ComplexSource.complex_multiply_correct context functions.complex functions.multiply functions.zero functions.increment
      functions.add functions.compare functions.canonical before actualInput h.well (input_arrays h inside)
  have inputOut : actualInput.layout.object MultiplyParameters.Var.output=tableObject := rfl
  have inputWork : actualInput.layout.object MultiplyParameters.Var.work=workObject := rfl
  have frame' : MultiplyCall.CallerFrame before after [tableObject,workObject] := frame
  have params := locals_after_call h frame'
  have selectedCall : Call context "complex_multiply"
      [.pointer (wordPointer tableObject (j*12)),.pointer (wordPointer tableObject ((j-1)*12)),
        .pointer (wordPointer workObject 128),.pointer (wordPointer workObject 0)] before (.value (.integer (integer64 0))) after :=
    (input_arguments h inside) ▸ called
  have actualArgs:=arguments_eval context h inside
  have statusSlot : Slot before (ids Var.status) owner .u64 (.integer (integer64 0)):=h.locals.slots Var.status
  have afterSlot : Slot after (ids Var.status) owner .u64 (.integer (integer64 0)):=params.slots Var.status
  have assignment : Exec context before callStmt .normal after :=
    StatusCall.assignment_execution (h.locals.lookup Var.status) (params.lookup Var.status) statusSlot afterSlot actualArgs selectedCall
  have allTable : ∀k,k<n/2*12 → (k<j*12 ∨ j*12+12≤k) → nextTable k=tableData k := by
    intro k hk away
    simpa only [actualInput,input,layout,objectAt,startAt,extent,currentData,if_neg h.different] using
      outTable k (by simpa only [actualInput,input,layout,objectAt,extent,if_neg h.different] using hk) away (Or.inl h.different)
  have allWork : ∀k,k<512 → 46≤k → nextWork k=workData k := by
    intro k hk away
    simpa only [actualInput,input,layout,objectAt,startAt,extent,currentData,ite_true,Nat.zero_add] using
      outWork k (by simpa only [actualInput,input,layout,objectAt,extent,ite_true] using hk) (Or.inr away) (Or.inl h.different.symm)
  have oldCell : ∀k,k<j → ∀d,d<12 → nextTable (k*12+d)=tableData (k*12+d) := by
    intro k hk d hd
    exact allTable _ (by omega) (Or.inl (by omega))
  have rootCell : ∀d,d<12 → nextWork (128+d)=workData (128+d) := by
    intro d hd;exact allWork _ (by omega) (by omega)
  have post : View after tableObject workObject n ids owner j nextTable nextWork seed := by
    refine ⟨params,?_,?_,h.different,h.separate,h.nbound,h.active,?_,?_,?_,?_,?_,?_,h.rootSmall,h.valuesSmall,frame'.frame.well⟩
    · simpa only [actualInput,input,layout,objectAt,extent,if_neg h.different] using tableRep
    · simpa only [actualInput,input,layout,objectAt,extent,ite_true] using workRep
    · intro k hk c d hd
      rw [show k*12+6*c.val+d=k*12+(6*c.val+d) by omega,oldCell k hk _ (by have cc:=c.isLt;omega)]
      simpa only [Nat.add_assoc] using h.tableDigits k hk c d hd
    · intro k hk c
      rw [show k*12+6*c.val+5=k*12+(6*c.val+5) by omega,oldCell k hk _ (by have cc:=c.isLt;omega)]
      exact h.tableSigns k hk c
    · intro k hk
      exact (pair_congr nextTable tableData _ _ (oldCell k hk)).trans (h.tableValues k hk)
    · intro c d hd
      rw [show 128+6*c.val+d=128+(6*c.val+d) by omega,rootCell _ (by have cc:=c.isLt;omega)]
      simpa only [Nat.add_assoc] using h.rootDigits c d hd
    · intro c
      rw [show 128+6*c.val+5=128+(6*c.val+5) by omega,rootCell _ (by have cc:=c.isLt;omega)]
      exact h.rootSigns c
    · exact (pair_congr nextWork workData 128 128 rootCell).trans h.rootValue
  have computed : ComplexSource.pair nextTable (j*12)=sequence seed j :=
    value.trans (computed_value h inside)
  refine ⟨after,nextTable,nextWork,assignment,post,computed,digits,signs,frame',allWork,allTable,?_⟩
  intro other flow run
  apply StatusCall.assignment_every_execution (h.locals.lookup Var.status) (params.lookup Var.status) statusSlot afterSlot
    (by intro e member;simp only [arguments,List.mem_cons,List.mem_nil_iff,or_false] at member;rcases member with rfl|rfl|rfl|rfl <;> trivial)
    actualArgs ?_ run
  intro other result callRun
  exact every other result ((input_arguments h inside).symm ▸ callRun)

#print axioms locals_after_call
#print axioms pair_congr
#print axioms call_execution
end RH080Next.FFTPV.TwiddleSource
