/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTConvertBoundParameters
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ConvertBoundSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

/-- Full actual Call on a six-word unsigned magnitude. Actual upper-word
sentinel checks, two-limb conversion, parameters, scope exits and caller
storage are proved from the preserved C source. -/
theorem convert_bound_call {F : Type} (context : Context F)
    (selected : findFunction context.program "convert_bound"=some convert_bound_ast)
    (before : State F) (object size start : Nat) (data : Nat→Nat)
    (well : WellScoped before) (array : WordArrayRep before object size data)
    (bound : start+6≤size) (digits : ∀k,k<6 → data (start+k)<base) :
    ∃after,Call context "convert_bound" [.pointer (wordPointer object start),.integer (integer64 6)] before
      (.value (.integer (integer64 (result data start)))) after ∧
      WordArrayRep after object size data ∧ MultiplyCall.CallerFrame before after [] := by
  let entry : State F := {before.enterScope with environment:=[]}
  have we : WellScoped entry := wellScoped_environment (wellScoped_enter well) []
  obtain ⟨sa,sn,si,da,dn,di,view⟩ := initialize_parameters we rfl array bound digits
  obtain ⟨middle,k,loopRun,post⟩ := loop_execution context 4 view (by norm_num)
  let after : State F := {middle.leaveScope entry.scope before.environment with scope:=before.scope}
  have snScope : sn.scope=entry.scope := (declare_frame dn).1.trans (declare_frame da).1
  have params : bindParameters entry convert_bound_ast.parameters
      [.pointer (wordPointer object start),.integer (integer64 6)]=some sn := by
    change bindParameters entry [(.pointer .u64,"a"),(.u64,"n")]
      [.pointer (wordPointer object start),.integer (integer64 6)]=some sn
    simp [bindParameters,da,dn]
  have bodyRun : ExecList context sn statements (.returned (.integer (integer64 (result data start)))) middle := by
    have declared : Exec context sn declaration .normal si :=
      .declareSome (.literal (.integer 2 "ULL") _ (.integer (integer64 2)) (by rfl)) di
    by_cases hz : allZero data start 4 2=true
    · have returnRun : Exec context middle returnLower (.returned (.integer (integer64 (lower data start)))) middle :=
        .returnSome (lower_eval context post)
      simpa only [statements,result,if_pos hz] using
        (ExecList.cons declared (.cons (by simpa only [loopFlow,if_pos hz] using loopRun) (.abrupt returnRun (by simp))))
    · simpa only [statements,result,if_neg hz] using
        (ExecList.cons declared (.abrupt (by simpa only [loopFlow,if_neg hz] using loopRun) (by simp)))
  have called : Call context "convert_bound" [.pointer (wordPointer object start),.integer (integer64 6)] before
      (.value (.integer (integer64 (result data start)))) after := by
    apply Call.internal (function:=convert_bound_ast) (entered:=sn) (middle:=middle) selected actual_body params
    · exact Body.finish bodyRun (by intro label he;cases he)
    · exact convert64 (result data start) (result_fits data start digits)
    · simp only [after,snScope]
  have chain : Declarations entry si := .cons da (.cons dn (.cons di (.nil si)))
  have fields := chain.fields
  have noalloc : SourceNoAlloc.Only loop := by
    simp [loop,loopBody,condition,advance,branch,test,returnSentinel,SourceNoAlloc.Only,SourcePure.CallFree]
  have effect := SourceNoAlloc.exec_effect loopRun noalloc view.well
  have frame := loop_frame view loopRun
  have oldObjects : ∀id,id<before.nextObject → after.objects id=before.objects id := by
    intro id old
    have untouched : id∉[paramIds entry.nextObject Var.i] := by
      simp only [List.mem_singleton,paramIds]
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
        have bb := well.automatic id obj before.nextScope present bad
        omega
      simp [storage]
  have afterWell : WellScoped after := by
    apply wellScoped_scope (wellScoped_leave effect.well entry.scope before.environment)
    have bb := well.current
    have nsDecl := fields.2.2.1
    have nsLoop := frame.nextScope
    change si.nextScope=before.nextScope+1 at nsDecl
    change before.scope<middle.nextScope
    omega
  have fdecl : si.foreign=entry.foreign := (declare_foreign di).trans ((declare_foreign dn).trans (declare_foreign da))
  have no : before.nextObject≤after.nextObject := by
    have bb := fields.1
    have nc := frame.nextObject
    change entry.nextObject≤si.nextObject at bb
    change before.nextObject≤middle.nextObject
    change before.nextObject≤si.nextObject at bb
    omega
  have ns : before.nextScope≤after.nextScope := by
    have nd := fields.2.2.1
    have nl := frame.nextScope
    change si.nextScope=before.nextScope+1 at nd
    change before.nextScope≤middle.nextScope
    omega
  have mode : after.mode=before.mode := frame.mode.trans fields.2.2.2.1
  refine ⟨after,called,ComplexSource.word_array_leave post.array entry.scope before.scope before.environment,
    rfl,rfl,afterWell,no,no,ns,mode,effect.foreign.trans fdecl,?_⟩
  intro id old outside
  exact oldObjects id old

theorem function_statements_unique {F : Type} (context : Context F) :
    ∀s∈statements,CompareSource.Unique context s := by
  intro stmt member
  simp only [statements,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact fun first second => PureDeterminism.simple_unique
      (by simp [declaration,PureDeterminism.Simple,SourcePure.CallFree]) first second
  · exact loop_unique context
  · exact fun first second => PureDeterminism.simple_unique
      (by simp [returnLower,base,PureDeterminism.Simple,SourcePure.CallFree]) first second

theorem function_body_unique {F : Type} {context : Context F}
    {before a b : State F} {fa fb : Flow}
    (first : Body context statements before statements fa a)
    (second : Body context statements before statements fb b) : fa=fb ∧ a=b := by
  cases first with
  | finish run _ =>
    cases second with
    | finish run' _ => exact CompareSource.list_unique (function_statements_unique context) run run'
    | jump run' target tail => simp [statements,declaration,loop,returnLower,labelTail] at target
  | jump run target tail => simp [statements,declaration,loop,returnLower,labelTail] at target

/-- Every full Call has the same return and resulting caller state as the
constructed terminating execution. This discharges universal correctness;
no favorable-trace interpretation is used. -/
theorem returned_call_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "convert_bound"=some convert_bound_ast)
    {before a b : State F} {args : List Value} {value : Value} {result : CallResult}
    (first : Call context "convert_bound" args before (.value value) a)
    (second : Call context "convert_bound" args before result b) :
    result=.value value ∧ b=a := by
  cases first with
  | external absent named foreign => rw [selected] at absent; cases absent
  | internal selectedA shapeA paramsA bodyA convertA finishA =>
    have functionA := Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    have statementsA : statements=_ := Stmt.block.inj (actual_body.symm.trans shapeA)
    subst_vars
    cases second with
    | external absent named foreign => rw [selected] at absent; cases absent
    | internal selectedB shapeB paramsB bodyB convertB finishB =>
      have functionB := Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : statements=_ := Stmt.block.inj (actual_body.symm.trans shapeB)
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
      have statementsB : statements=_ := Stmt.block.inj (actual_body.symm.trans shapeB)
      subst_vars
      have enteredEq := Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      cases (function_body_unique bodyA bodyB).1
  | internalVoid selectedA shapeA void paramsA bodyA finishA =>
    have functionA := Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    cases void


#print axioms convert_bound_call
#print axioms function_body_unique
#print axioms returned_call_unique
end RH080Next.FFTPV.ConvertBoundSource
