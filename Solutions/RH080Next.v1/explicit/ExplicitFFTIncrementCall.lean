/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTIncrementLoop
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.IncrementSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs

structure CallerFrame {F : Type} (before after : State F) (written : Nat) : Prop where
  environment : after.environment=before.environment
  scope : after.scope=before.scope
  foreign : after.foreign=before.foreign
  well : WellScoped after
  objects : ∀id,id < before.nextObject → id ≠ written → after.objects id=before.objects id

def jDeclaration : Stmt := .declare .u64 "j" (some (.literal (.integer 0 "ULL")))
def carryDeclaration : Stmt := .declare .u64 "carry" (some (.literal (.integer 1 "ULL")))
def returnStatement : Stmt := .returnValue (some (.variable "carry"))
def functionStatements : List Stmt := [jDeclaration,carryDeclaration,loop,returnStatement]

/-- Complete actual source call: parameter binding, both local births, all
forward iterations, the returned carry, and caller-state restoration. -/
theorem increment_words_call {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast)
    (before : State F) (object length start n : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n ≤ length) (small : n ≤ 6) (digits : ∀i < n,old (start+i) < base) :
    ∃after,Call context "increment_words"
      [.pointer (wordPointer object start),.integer (integer64 n)] before
      (.value (.integer (integer64 (incrementDigits base (fun k=>old (start+k)) n).2))) after ∧
      WordArrayRep after object length (currentData old start n) ∧ CallerFrame before after object := by
  let entry : State F:={before.enterScope with environment:=[]}
  have we : WellScoped entry:=wellScoped_environment (wellScoped_enter well) []
  obtain ⟨sa,sn,sj,sc,da,dn,dj,dc,view⟩:=initialize_parameters we rfl rep bound small digits
  obtain ⟨middle,loopRun,post,frame⟩:=loop_execution context n (j:=0) (n:=n) (by omega) view
  let carry:=(incrementDigits base (fun k=>old (start+k)) n).2
  have hc : carry ≤ 1 := post.carry_bound
  have hc64 : carry < 2^64 := by omega
  have params : bindParameters entry increment_words_ast.parameters
      [.pointer (wordPointer object start),.integer (integer64 n)]=some sn := by
    change bindParameters entry [(.pointer .u64,"a"),(.u64,"n")]
      [.pointer (wordPointer object start),.integer (integer64 n)]=some sn
    simp [bindParameters,da,dn]
  have bodyRun : ExecList context sn functionStatements (.returned (.integer (integer64 carry))) middle :=
    .cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dj)
      (.cons (.declareSome (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl)) dc)
        (.cons loopRun (.abrupt (.returnSome (.variable (post.locals.lookup Var.carry)
          (post.locals.read Var.carry))) (by simp))))
  let after : State F:={middle.leaveScope entry.scope before.environment with scope:=before.scope}
  have snScope : sn.scope=entry.scope:=(declare_frame dn).1.trans (declare_frame da).1
  have called : Call context "increment_words"
      [.pointer (wordPointer object start),.integer (integer64 n)] before
      (.value (.integer (integer64 carry))) after := by
    apply Call.internal (function:=increment_words_ast) (entered:=sn) (middle:=middle)
      selected actual_body params
    · exact Body.finish bodyRun (by intro label he; cases he)
    · exact convert64 carry hc64
    · simp only [after,snScope]
  have chain : Declarations entry sc:=.cons da (.cons dn (.cons dj (.cons dc (.nil sc))))
  have fields:=chain.fields
  have oldObjects : ∀id,id < before.nextObject → id ≠ object → after.objects id=before.objects id := by
    intro id old different
    have oldEntry : id < entry.nextObject:=old
    have oldSc : id < sc.nextObject := lt_of_lt_of_le oldEntry fields.1
    have absent : id∉writes object (ids entry.nextObject) := by
      have nj : id≠ids entry.nextObject Var.j := by change id≠before.nextObject+2; omega
      have nc : id≠ids entry.nextObject Var.carry := by change id≠before.nextObject+3; omega
      simp [writes,different,nj,nc]
    have same : middle.objects id=before.objects id:=
      (frame.outside id oldSc absent).trans (fields.2.2.2.2 id oldEntry)
    change (middle.objects id).map _=before.objects id
    rw [same]
    cases present : before.objects id with
    | none=>rfl
    | some obj=>
      have storage : obj.storage≠.automatic entry.scope := by
        intro bad
        have hb:=well.automatic id obj before.nextScope present bad
        omega
      simp [storage]
  have afterWell : WellScoped after := by
    apply wellScoped_scope (wellScoped_leave post.well entry.scope before.environment)
    have current:=well.current
    have ns:=fields.2.2.1
    have mono:=frame.nextScope
    change sc.nextScope=before.nextScope+1 at ns
    change before.scope < middle.nextScope
    omega
  have declForeign : sc.foreign=entry.foreign :=
    (declare_foreign dc).trans ((declare_foreign dj).trans ((declare_foreign dn).trans (declare_foreign da)))
  have foreign : after.foreign=before.foreign := by
    change middle.foreign=entry.foreign
    exact frame.foreign.trans declForeign
  exact ⟨after,called,wordArray_leave post.array,rfl,rfl,foreign,afterWell,oldObjects⟩

theorem function_statements_unique {F : Type} (context : Context F) :
    ∀s∈functionStatements,CompareSource.Unique context s := by
  intro stmt member
  simp only [functionStatements,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact fun a b=>PureDeterminism.simple_unique (by simp [jDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) a b
  · exact fun a b=>PureDeterminism.simple_unique (by simp [carryDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) a b
  · exact actual_loop_unique context
  · exact fun a b=>PureDeterminism.simple_unique (by simp [returnStatement,PureDeterminism.Simple,SourcePure.CallFree]) a b

theorem function_body_unique {F : Type} {context : Context F}
    {before a b : State F} {fa fb : Flow}
    (first : Body context functionStatements before functionStatements fa a)
    (second : Body context functionStatements before functionStatements fb b) : fa=fb ∧ a=b := by
  cases first with
  | finish run _=>
    cases second with
    | finish run' _=>exact CompareSource.list_unique (function_statements_unique context) run run'
    | jump run' target tail=>simp [functionStatements,jDeclaration,carryDeclaration,loop,returnStatement,labelTail] at target
  | jump run target tail=>simp [functionStatements,jDeclaration,carryDeclaration,loop,returnStatement,labelTail] at target

theorem returned_call_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "increment_words"=some increment_words_ast)
    {before a b : State F} {args : List Value} {value : Value} {result : CallResult}
    (first : Call context "increment_words" args before (.value value) a)
    (second : Call context "increment_words" args before result b) : result=.value value ∧ b=a := by
  cases first with
  | external absent named foreign=>rw [selected] at absent; cases absent
  | internal selectedA shapeA paramsA bodyA convertA finishA=>
    have functionA:=Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    have statementsA : functionStatements=_:=Stmt.block.inj (actual_body.symm.trans shapeA)
    subst_vars
    cases second with
    | external absent named foreign=>rw [selected] at absent; cases absent
    | internal selectedB shapeB paramsB bodyB convertB finishB=>
      have functionB:=Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements=_:=Stmt.block.inj (actual_body.symm.trans shapeB)
      subst_vars
      have enteredEq:=Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      obtain ⟨flowEq,middleEq⟩:=function_body_unique bodyA bodyB
      cases flowEq
      cases middleEq
      have valueEq:=Option.some.inj (convertA.symm.trans convertB)
      cases valueEq
      exact ⟨rfl,rfl⟩
    | internalVoid selectedB shapeB void paramsB bodyB finishB=>
      have functionB:=Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      cases void
    | internalTerminated selectedB shapeB paramsB bodyB=>
      have functionB:=Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements=_:=Stmt.block.inj (actual_body.symm.trans shapeB)
      subst_vars
      have enteredEq:=Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      cases (function_body_unique bodyA bodyB).1
  | internalVoid selectedA shapeA void paramsA bodyA finishA=>
    have functionA:=Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    cases void

#print axioms increment_words_call
#print axioms function_body_unique
#print axioms returned_call_unique
end RH080Next.FFTPV.IncrementSource
