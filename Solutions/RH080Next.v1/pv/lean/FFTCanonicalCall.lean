/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTCanonicalSign
import ExplicitFFTCompareDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CanonicalSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings PureDeterminism

def parameterIds (base : Nat) : Var → Nat | .a => base | .nonzero => base+1 | .j => base+2
private theorem slot_declare_other {F : Type} {before after : State F}
    {id owner : Nat} {oldtype newtype : CType} {oldvalue newvalue : Value} {cname : String}
    (h : Slot before id owner oldtype oldvalue) (d : Declaration before after cname newtype newvalue)
    (different : id ≠ before.nextObject) : Slot after id owner oldtype oldvalue :=
  ⟨h.storable, by rw [d.outside id different]; exact h.object⟩

theorem initialize_parameters {F : Type} {entry : State F} {object size start : Nat} {old : Nat → Nat}
    (well : WellScoped entry) (emptyEnv : entry.environment = [])
    (rep : WordArrayRep entry object size old) (bound : start+6 ≤ size)
    (digits : ∀i, i < 5 → old (start+i) < 1000000000) :
    ∃aState nzState jState,
      entry.declare (.pointer .u64) "a" (some (.pointer (wordPointer object start))) = some aState ∧
      aState.declare .u64 "nonzero" (some (.integer (integer64 0))) = some nzState ∧
      nzState.declare .u64 "j" (some (.integer (integer64 0))) = some jState ∧
      View jState object size start entry.scope (parameterIds entry.nextObject) old 0 := by
  obtain ⟨aState, da⟩ := ZeroFrame.declare_exists well _ "a" _ (CopyLoop.pointer_storable object start)
  have wa := wellScoped_declare well da
  obtain ⟨nzState, dn⟩ := ZeroFrame.declare_exists wa _ "nonzero" _ (ZeroFrame.u64_storable 0 (by norm_num))
  have wn := wellScoped_declare wa dn
  obtain ⟨jState, dj⟩ := ZeroFrame.declare_exists wn _ "j" _ (ZeroFrame.u64_storable 0 (by norm_num))
  have ia := declare_storable (CopyLoop.pointer_storable object start) (CopyLoop.pointer_storable object start).converted da
  have inn := declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (ZeroFrame.u64_storable 0 (by norm_num)).converted dn
  have ij := declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (ZeroFrame.u64_storable 0 (by norm_num)).converted dj
  have oa := ia.nextObject
  have onn := inn.nextObject
  have sa := ia.scope
  have sn := inn.scope
  have oldId : object < entry.nextObject := well.objectIds _ _ rep.2.1
  have hlocals : Locals jState name type (parameterIds entry.nextObject) entry.scope (values object start old 0) := by
    constructor
    · intro v
      cases v <;> simp [parameterIds, name, type, ij.environment, inn.environment, ia.environment,
        emptyEnv, oa, onn, scalarPointer, List.lookup]
    · intro v
      cases v with
      | a =>
        have ha := slot_declare_other ia.slot inn (by omega)
        have haj := slot_declare_other ha ij (by omega)
        simpa only [parameterIds, type, values] using haj
      | nonzero =>
        have hn := slot_declare_other inn.slot ij (by omega)
        simpa only [parameterIds, type, values, digitSum_zero, oa, sa] using hn
      | j =>
        simpa only [parameterIds, type, values, oa, onn, sa, sn] using ij.slot
    · intro v w he
      cases v <;> cases w <;> simp_all [parameterIds] <;> omega
    · rw [ij.nextScope, inn.nextScope, ia.nextScope]
      exact well.current
  have host : jState.mode = .host := ij.mode.trans (inn.mode.trans (ia.mode.trans rep.1))
  have present : jState.objects object = some (wordObject size old) := by
    rw [ij.outside object (by omega), inn.outside object (by omega), ia.outside object (by omega)]
    exact rep.2.1
  refine ⟨aState, nzState, jState, da, dn, dj, ⟨host, present, rep.2.2⟩, hlocals,
    ?_, bound, digits, wellScoped_declare wn dj, by omega⟩
  intro v
  cases v <;> simp only [parameterIds] <;> omega

def nzDeclaration : Stmt := .declare .u64 "nonzero" (some (.literal (.integer 0 "ULL")))
def jDeclaration : Stmt := .declare .u64 "j" (some (.literal (.integer 0 "ULL")))
def returnZero : Stmt := .returnValue (some (.literal (.integer 0 "ULL")))
def functionStatements : List Stmt := [nzDeclaration, jDeclaration, loop, canonicalBranch, returnZero]

theorem canonical_sign_call {F : Type} (context : Context F)
    (selected : findFunction context.program "canonical_sign" = some FFTRecursivePV.canonical_sign_ast)
    (before : State F) (object size start : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object size old) (bound : start+6 ≤ size)
    (digits : ∀i, i < 5 → old (start+i) < 1000000000) :
    ∃after, Call context "canonical_sign" [.pointer (wordPointer object start)] before
      (.value (.integer (integer64 0))) after ∧
      WordArrayRep after object size (canonicalData old start) ∧ CopyLoop.CallerFrame before after object := by
  let entry : State F := {before.enterScope with environment := []}
  have we : WellScoped entry := wellScoped_environment (wellScoped_enter well) []
  obtain ⟨aState, nzState, jState, da, dn, dj, view⟩ := initialize_parameters we rfl rep bound digits
  obtain ⟨middle, loopRun, vm⟩ := loop_execution context 5 view (by omega)
  obtain ⟨finished, branchRun, output⟩ := canonical_branch_execution context vm
  have loopFrame := loop_frame view loopRun
  have branchFrame := canonical_branch_frame vm branchRun
  let after : State F := {finished.leaveScope entry.scope before.environment with scope := before.scope}
  have ascope : aState.scope = entry.scope := (declare_frame da).1
  have params : bindParameters entry FFTRecursivePV.canonical_sign_ast.parameters
      [.pointer (wordPointer object start)] = some aState := by
    change bindParameters entry [(.pointer .u64,"a")] [.pointer (wordPointer object start)] = some aState
    simp [bindParameters, da]
  have called : Call context "canonical_sign" [.pointer (wordPointer object start)] before
      (.value (.integer (integer64 0))) after := by
    apply Call.internal (function := FFTRecursivePV.canonical_sign_ast) (entered := aState) (middle := finished)
      selected actual_body params
    · apply Body.finish
      · exact .cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dn)
          (.cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dj)
            (.cons loopRun (.cons branchRun (.abrupt (.returnSome (.literal (.integer 0 "ULL") _
              (.integer (integer64 0)) (by rfl))) (by intro he; cases he)))))
      · intro label he
        cases he
    · exact convert64 0 (by norm_num)
    · simp only [after, ascope]
  have chain : Declarations entry jState := .cons da (.cons dn (.cons dj (.nil jState)))
  have fields := chain.fields
  have loopEffect := SourceNoAlloc.exec_effect loopRun
    (by simp [loop, condition, loopBody, sumStmt, sumExpr, increment, SourceNoAlloc.Only, SourcePure.CallFree]) view.well
  have branchEffect := SourceNoAlloc.exec_effect branchRun
    (by simp [canonicalBranch, zeroTest, signStore, SourceNoAlloc.Only, SourcePure.CallFree]) vm.well
  have effect := loopEffect.trans branchEffect
  have oldObjects : ∀id, id < before.nextObject → id ≠ object → after.objects id = before.objects id := by
    intro id oldId different
    have untouched : id ∉ [parameterIds entry.nextObject Var.nonzero, parameterIds entry.nextObject Var.j] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
      constructor
      · change id ≠ before.nextObject+1; omega
      · change id ≠ before.nextObject+2; omega
    have same : finished.objects id = before.objects id :=
      (branchFrame.outside id (by simpa using different)).trans
        ((loopFrame.outside id untouched).trans (fields.2.2.2.2 id oldId))
    change (finished.objects id).map _ = before.objects id
    rw [same]
    cases present : before.objects id with
    | none => rfl
    | some obj =>
      have storage : obj.storage ≠ .automatic entry.scope := by
        intro bad
        have hb := well.automatic id obj before.nextScope present bad
        omega
      simp [storage]
  have afterWell : WellScoped after := by
    apply wellScoped_scope (wellScoped_leave effect.well entry.scope before.environment)
    change before.scope < finished.nextScope
    have b := well.current
    have nss := fields.2.2.1
    have nsf := effect.nextScope
    change jState.nextScope = before.nextScope+1 at nss
    omega
  have afterRep : WordArrayRep after object size (canonicalData old start) := by
    refine ⟨output.1, ?_, output.2.2⟩
    change (finished.objects object).map _ = some _
    rw [output.2.1]
    simp [wordObject]
  refine ⟨after, called, afterRep, rfl, rfl, ?_, afterWell, oldObjects⟩
  have fa : aState.foreign = entry.foreign := declare_foreign da
  have fn : nzState.foreign = aState.foreign := declare_foreign dn
  have fj : jState.foreign = nzState.foreign := declare_foreign dj
  exact effect.foreign.trans (fj.trans (fn.trans fa))

/-- The loop is deterministic under every allowed operand evaluation order. -/
theorem loop_unique {F : Type} (context : Context F) : CompareSource.Unique context loop := by
  apply CompareSource.while_unique (by simp [condition, SourcePure.CallFree])
  intro before a b fa fb first second
  exact PureDeterminism.block_unique
    (by simp [loopBody, sumStmt, sumExpr, increment, Simple, SourcePure.CallFree]) first second

theorem canonical_branch_unique {F : Type} (context : Context F) : CompareSource.Unique context canonicalBranch := by
  intro before a b fa fb first second
  cases first with
  | ifTrue ev tr run =>
    cases second with
    | ifTrue ev' tr' run' =>
      obtain ⟨rfl, rfl⟩ := PureDeterminism.eval_unique (by simp [zeroTest, SourcePure.CallFree]) ev ev'
      exact PureDeterminism.block_unique (by simp [signStore, Simple, SourcePure.CallFree]) run run'
    | ifFalse ev' tr' =>
      cases (PureDeterminism.eval_unique (by simp [zeroTest, SourcePure.CallFree]) ev ev').1
      simp_all
  | ifFalse ev tr =>
    cases second with
    | ifTrue ev' tr' run' =>
      cases (PureDeterminism.eval_unique (by simp [zeroTest, SourcePure.CallFree]) ev ev').1
      simp_all
    | ifFalse ev' tr' => exact ⟨rfl, (PureDeterminism.eval_unique (by simp [zeroTest, SourcePure.CallFree]) ev ev').2⟩

theorem function_statements_unique {F : Type} (context : Context F) :
    ∀s ∈ functionStatements, CompareSource.Unique context s := by
  intro stmt member
  simp only [functionStatements, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact fun first second => PureDeterminism.simple_unique (by trivial) first second
  · exact fun first second => PureDeterminism.simple_unique (by trivial) first second
  · exact loop_unique context
  · exact canonical_branch_unique context
  · exact fun first second => PureDeterminism.simple_unique (by trivial) first second

theorem function_body_unique {F : Type} {context : Context F} {before a b : State F} {fa fb : Flow}
    (first : Body context functionStatements before functionStatements fa a)
    (second : Body context functionStatements before functionStatements fb b) : fa = fb ∧ a = b := by
  cases first with
  | finish run _ =>
    cases second with
    | finish run' _ => exact CompareSource.list_unique (function_statements_unique context) run run'
    | jump run' target tail => simp [functionStatements, nzDeclaration, jDeclaration, loop, canonicalBranch, returnZero, labelTail] at target
  | jump run target tail => simp [functionStatements, nzDeclaration, jDeclaration, loop, canonicalBranch, returnZero, labelTail] at target

/-- Universal full-call uniqueness derives from the real source rules. -/
theorem returned_call_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "canonical_sign" = some FFTRecursivePV.canonical_sign_ast)
    {before a b : State F} {args : List Value} {value : Value} {result : CallResult}
    (first : Call context "canonical_sign" args before (.value value) a)
    (second : Call context "canonical_sign" args before result b) : result = .value value ∧ b = a := by
  cases first with
  | external absent named foreign => rw [selected] at absent; cases absent
  | internal selectedA shapeA paramsA bodyA convertA finishA =>
    have functionA := Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    have statementsA : functionStatements = _ := Stmt.block.inj (actual_body.symm.trans shapeA)
    subst_vars
    cases second with
    | external absent named foreign => rw [selected] at absent; cases absent
    | internal selectedB shapeB paramsB bodyB convertB finishB =>
      have functionB := Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements = _ := Stmt.block.inj (actual_body.symm.trans shapeB)
      subst_vars
      have enteredEq := Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      obtain ⟨flowEq, middleEq⟩ := function_body_unique bodyA bodyB
      cases flowEq
      cases middleEq
      have valueEq := Option.some.inj (convertA.symm.trans convertB)
      cases valueEq
      exact ⟨rfl, rfl⟩
    | internalVoid selectedB shapeB void paramsB bodyB finishB =>
      have functionB := Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      cases void
    | internalTerminated selectedB shapeB paramsB bodyB =>
      have functionB := Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements = _ := Stmt.block.inj (actual_body.symm.trans shapeB)
      subst_vars
      have enteredEq := Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      cases (function_body_unique bodyA bodyB).1
  | internalVoid selectedA shapeA void paramsA bodyA finishA =>
    have functionA := Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    cases void

#print axioms canonical_sign_call
#print axioms loop_unique
#print axioms returned_call_unique
end RH080Next.FFTPV.CanonicalSource
