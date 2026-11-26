/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTCompareLoop
import ExplicitFFTCompareDeterminism
import FFTSource

set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CompareSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

structure ReadOnlyCallerFrame {F : Type} (before after : State F) : Prop where
  environment : after.environment=before.environment
  scope : after.scope=before.scope
  foreign : after.foreign=before.foreign
  well : WellScoped after
  objects : ∀id,id<before.nextObject → after.objects id=before.objects id

def localDeclaration : Stmt := .declare .u64 "j" (some (.literal (.integer 5 "ULL")))
def functionStatements : List Stmt := [localDeclaration,loop,returnStmt 1]

theorem compareDigits_le_two (a b : Nat → Nat) (n : Nat) : FFT.Limbs.compareDigits a b n≤2 := by
  induction n with
  | zero => simp [FFT.Limbs.compareDigits]
  | succ n ih =>
    unfold FFT.Limbs.compareDigits
    split <;> try omega
    split <;> omega

/-- Full actual source function call: pointer binding, local initialization,
all reverse comparison iterations, return conversion, and caller restoration.
Both arbitrary input arrays and every other pre-existing caller object survive. -/
theorem magnitude_compare_call {F : Type} (context : Context F)
    (selected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (before : State F) (ao al ast bo bl bst : Nat) (a b : Nat → Nat)
    (well : WellScoped before) (left : WordArrayRep before ao al a) (right : WordArrayRep before bo bl b)
    (leftBound : ast+5≤al) (rightBound : bst+5≤bl) :
    ∃after,Call context "magnitude_compare"
      [.pointer (wordPointer ao ast),.pointer (wordPointer bo bst)] before
      (.value (.integer (integer64 (FFT.Limbs.compareDigits (fun i=>a (ast+i)) (fun i=>b (bst+i)) 5)))) after ∧
      WordArrayRep after ao al a ∧ WordArrayRep after bo bl b ∧ ReadOnlyCallerFrame before after := by
  let entry : State F := {before.enterScope with environment:=[]}
  have we : WellScoped entry := wellScoped_environment (wellScoped_enter well) []
  obtain ⟨sa,sb,sj,da,db,dj,view⟩ := initialize_parameters we rfl left right leftBound rightBound
  obtain ⟨middle,k,loopRun,post⟩ := loop_execution context 5 view
  let cmp := FFT.Limbs.compareDigits (fun i=>a (ast+i)) (fun i=>b (bst+i)) 5
  have hCmp : cmp≤2 := compareDigits_le_two _ _ _
  have hFit : cmp<2^64 := by omega
  have loopRun' : Exec context sj loop
      (if cmp=1 then .normal else .returned (.integer (integer64 cmp))) middle := by
    simpa only [comparedFlow_eq] using loopRun
  let after : State F := {middle.leaveScope entry.scope before.environment with scope:=before.scope}
  have sbScope : sb.scope=entry.scope := (declare_frame db).1.trans (declare_frame da).1
  have params : bindParameters entry magnitude_compare_ast.parameters
      [.pointer (wordPointer ao ast),.pointer (wordPointer bo bst)]=some sb := by
    change bindParameters entry [(.pointer .u64,"a"),(.pointer .u64,"b")]
      [.pointer (wordPointer ao ast),.pointer (wordPointer bo bst)]=some sb
    simp [bindParameters,da,db]
  have bodyRun : ExecList context sb functionStatements (.returned (.integer (integer64 cmp))) middle := by
    have declared : Exec context sb localDeclaration .normal sj :=
      .declareSome (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl)) dj
    by_cases he : cmp=1
    · rw [he]
      exact .cons declared (.cons (by simpa [he] using loopRun')
        (.abrupt (.returnSome (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))) (by simp)))
    · exact .cons declared (.abrupt (by simpa only [if_neg he] using loopRun') (by simp))
  have called : Call context "magnitude_compare"
      [.pointer (wordPointer ao ast),.pointer (wordPointer bo bst)] before
      (.value (.integer (integer64 cmp))) after := by
    apply Call.internal (function:=magnitude_compare_ast) (entered:=sb) (middle:=middle)
      selected actual_body params
    · exact Body.finish bodyRun (by intro label he; cases he)
    · exact convert64 cmp hFit
    · simp only [after,sbScope]
  have chain : Declarations entry sj := .cons da (.cons db (.cons dj (.nil sj)))
  have fields := chain.fields
  have noalloc : SourceNoAlloc.Only loop := by
    simp [loop,loopBody,condition,decrement,branch,comparison,index,returnStmt,
      SourceNoAlloc.Only,SourcePure.CallFree]
  have effect := SourceNoAlloc.exec_effect loopRun noalloc view.well
  have frame := loop_frame view loopRun
  have oldObjects : ∀id,id<before.nextObject → after.objects id=before.objects id := by
    intro id old
    have untouched : id∉[ids entry.nextObject Var.j] := by
      simp only [List.mem_singleton,ids]
      change id≠before.nextObject+2
      omega
    have same : middle.objects id=before.objects id :=
      (frame.outside id untouched).trans (fields.2.2.2.2 id old)
    change (middle.objects id).map _=before.objects id
    rw [same]
    cases present : before.objects id with
    | none => rfl
    | some obj =>
      have storage : obj.storage≠.automatic entry.scope := by
        intro bad
        have bound := well.automatic id obj before.nextScope present bad
        omega
      simp [storage]
  have afterWell : WellScoped after := by
    apply wellScoped_scope (wellScoped_leave effect.well entry.scope before.environment)
    have b := well.current
    have nsDecl := fields.2.2.1
    have nsLoop := frame.nextScope
    change sj.nextScope=before.nextScope+1 at nsDecl
    change before.scope<middle.nextScope
    omega
  have leftAfter : WordArrayRep after ao al a := by
    refine ⟨post.left.1,?_,post.left.2.2⟩
    change (middle.objects ao).map _=some (wordObject al a)
    rw [post.left.2.1]
    simp [wordObject]
  have rightAfter : WordArrayRep after bo bl b := by
    refine ⟨post.right.1,?_,post.right.2.2⟩
    change (middle.objects bo).map _=some (wordObject bl b)
    rw [post.right.2.1]
    simp [wordObject]
  refine ⟨after,called,leftAfter,rightAfter,rfl,rfl,?_,afterWell,oldObjects⟩
  have fdecl : sj.foreign=entry.foreign := (declare_foreign dj).trans ((declare_foreign db).trans (declare_foreign da))
  exact effect.foreign.trans fdecl

theorem function_statements_unique {F : Type} (context : Context F) :
    ∀s∈functionStatements,Unique context s := by
  intro stmt member
  simp only [functionStatements,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact fun first second => PureDeterminism.simple_unique
      (by simp [localDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) first second
  · exact actual_loop_unique context
  · exact fun first second => PureDeterminism.simple_unique
      (by simp [returnStmt,PureDeterminism.Simple,SourcePure.CallFree]) first second

theorem function_body_unique {F : Type} {context : Context F}
    {before a b : State F} {fa fb : Flow}
    (first : Body context functionStatements before functionStatements fa a)
    (second : Body context functionStatements before functionStatements fb b) : fa=fb ∧ a=b := by
  cases first with
  | finish run _ =>
    cases second with
    | finish run' _ => exact list_unique (function_statements_unique context) run run'
    | jump run' target tail => simp [functionStatements,localDeclaration,loop,returnStmt,labelTail] at target
  | jump run target tail => simp [functionStatements,localDeclaration,loop,returnStmt,labelTail] at target

/-- Every full Call has the same return and resulting caller state as the
constructed terminating execution. This discharges universal correctness;
no favorable-trace interpretation is used. -/
theorem returned_call_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    {before a b : State F} {args : List Value} {value : Value} {result : CallResult}
    (first : Call context "magnitude_compare" args before (.value value) a)
    (second : Call context "magnitude_compare" args before result b) :
    result=.value value ∧ b=a := by
  cases first with
  | external absent named foreign => rw [selected] at absent; cases absent
  | internal selectedA shapeA paramsA bodyA convertA finishA =>
    have functionA := Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    have statementsA : functionStatements=_ := Stmt.block.inj (actual_body.symm.trans shapeA)
    subst_vars
    cases second with
    | external absent named foreign => rw [selected] at absent; cases absent
    | internal selectedB shapeB paramsB bodyB convertB finishB =>
      have functionB := Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements=_ := Stmt.block.inj (actual_body.symm.trans shapeB)
      subst_vars
      have enteredEq := Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      obtain ⟨flowEq,middleEq⟩ := function_body_unique bodyA bodyB
      cases flowEq
      cases middleEq
      have valueEq := Option.some.inj (convertA.symm.trans convertB)
      cases valueEq
      exact ⟨rfl,rfl⟩
    | internalVoid selectedB shapeB void paramsB bodyB finishB =>
      have functionB := Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      cases void
    | internalTerminated selectedB shapeB paramsB bodyB =>
      have functionB := Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements=_ := Stmt.block.inj (actual_body.symm.trans shapeB)
      subst_vars
      have enteredEq := Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      cases (function_body_unique bodyA bodyB).1
  | internalVoid selectedA shapeA void paramsA bodyA finishA =>
    have functionA := Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    cases void

#print axioms magnitude_compare_call
#print axioms function_body_unique
#print axioms returned_call_unique
end RH080Next.FFTPV.CompareSource
