/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTZeroSlices
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ZeroSlice
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings PureDeterminism
abbrev parameterIds := ZeroFrame.parameterIds

private theorem slot_declare_other {F : Type} {before after : State F}
    {id owner : Nat} {oldtype newtype : CType} {oldvalue newvalue : Value} {cname : String}
    (h : Slot before id owner oldtype oldvalue) (d : Declaration before after cname newtype newvalue)
    (different : id ≠ before.nextObject) : Slot after id owner oldtype oldvalue :=
  ⟨h.storable, by rw [d.outside id different]; exact h.object⟩

/-- Source parameters/local j are really allocated, also for a proper slice
of an already typed caller allocation. -/
theorem initialize_parameters {F : Type} {entry : State F} {object size start length : Nat}
    {old : Nat → Nat} (well : WellScoped entry) (emptyEnv : entry.environment = [])
    (rep : WordArrayRep entry object size old) (bound : start+length ≤ size) (fits : length < 2^64) :
    ∃aState nState jState,
      entry.declare (.pointer .u64) "a" (some (.pointer (wordPointer object start))) = some aState ∧
      aState.declare .u64 "n" (some (.integer (integer64 length))) = some nState ∧
      nState.declare .u64 "j" (some (.integer (integer64 0))) = some jState ∧
      View jState object size start length entry.scope (parameterIds entry.nextObject) old 0 := by
  obtain ⟨aState, da⟩ := ZeroFrame.declare_exists well _ "a" _ (CopyLoop.pointer_storable object start)
  have wa := wellScoped_declare well da
  obtain ⟨nState, dn⟩ := ZeroFrame.declare_exists wa _ "n" _ (ZeroFrame.u64_storable length fits)
  have wn := wellScoped_declare wa dn
  obtain ⟨jState, dj⟩ := ZeroFrame.declare_exists wn _ "j" _ (ZeroFrame.u64_storable 0 (by norm_num))
  have ia := declare_storable (CopyLoop.pointer_storable object start) (CopyLoop.pointer_storable object start).converted da
  have inn := declare_storable (ZeroFrame.u64_storable length fits) (ZeroFrame.u64_storable length fits).converted dn
  have ij := declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (ZeroFrame.u64_storable 0 (by norm_num)).converted dj
  have oa := ia.nextObject
  have onn := inn.nextObject
  have sa := ia.scope
  have sn := inn.scope
  have oldId : object < entry.nextObject := well.objectIds _ _ rep.2.1
  have hlocals : Locals jState name type (parameterIds entry.nextObject) entry.scope (value object start length 0) := by
    constructor
    · intro v
      cases v <;> simp [parameterIds, ZeroFrame.parameterIds, name, type, ZeroFrame.name, ZeroFrame.type,
        ij.environment, inn.environment, ia.environment, emptyEnv, oa, onn, scalarPointer, List.lookup]
    · intro v
      cases v with
      | a =>
        have ha := slot_declare_other ia.slot inn (by omega)
        have haj := slot_declare_other ha ij (by omega)
        simpa only [parameterIds, ZeroFrame.parameterIds, type, ZeroFrame.type, value] using haj
      | n =>
        have hn := slot_declare_other inn.slot ij (by omega)
        simpa only [parameterIds, ZeroFrame.parameterIds, type, ZeroFrame.type, value, oa, sa] using hn
      | j =>
        simpa only [parameterIds, ZeroFrame.parameterIds, type, ZeroFrame.type, value, oa, onn, sa, sn] using ij.slot
    · intro v w he
      cases v <;> cases w <;> simp_all [parameterIds, ZeroFrame.parameterIds] <;> omega
    · rw [ij.nextScope, inn.nextScope, ia.nextScope]
      exact well.current
  have host : jState.mode = .host := ij.mode.trans (inn.mode.trans (ia.mode.trans rep.1))
  have present : jState.objects object = some (wordObject size old) := by
    rw [ij.outside object (by omega), inn.outside object (by omega), ia.outside object (by omega)]
    exact rep.2.1
  refine ⟨aState, nState, jState, da, dn, dj, ?_, hlocals, ?_, bound, wellScoped_declare wn dj, by omega, fits⟩
  · simpa only [zeroData_zero] using (show WordArrayRep jState object size old from ⟨host, present, rep.2.2⟩)
  · intro v
    cases v <;> simp only [parameterIds, ZeroFrame.parameterIds] <;> omega

/-- Total actual zero_words Call for an arbitrary already initialized slice.
The reset interval can be a proper part of the allocation, at any valid offset. -/
theorem zero_words_call {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words" = some zero_words_ast)
    (before : State F) (object size start length : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object size old)
    (bound : start+length ≤ size) (fits : length < 2^64) :
    ∃after, Call context "zero_words" [.pointer (wordPointer object start), .integer (integer64 length)]
      before (.value (.integer (integer64 0))) after ∧
      WordArrayRep after object size (zeroData old start length) ∧ CopyLoop.CallerFrame before after object := by
  let entry : State F := {before.enterScope with environment := []}
  have we : WellScoped entry := wellScoped_environment (wellScoped_enter well) []
  obtain ⟨aState, nState, jState, da, dn, dj, view⟩ := initialize_parameters we rfl rep bound fits
  obtain ⟨middle, run, result⟩ := loop_execution context length view (by omega)
  have frame := loop_frame view run
  let after : State F := {middle.leaveScope entry.scope before.environment with scope := before.scope}
  have nscope : nState.scope = entry.scope := (declare_frame dn).1.trans (declare_frame da).1
  have params : bindParameters entry zero_words_ast.parameters
      [.pointer (wordPointer object start), .integer (integer64 length)] = some nState := by
    change bindParameters entry [(.pointer .u64,"a"), (.u64,"n")]
      [.pointer (wordPointer object start), .integer (integer64 length)] = some nState
    simp [bindParameters, da, dn]
  have called : Call context "zero_words" [.pointer (wordPointer object start), .integer (integer64 length)]
      before (.value (.integer (integer64 0))) after := by
    apply Call.internal (function := zero_words_ast) (entered := nState) (middle := middle)
      selected ZeroLoop.loop_is_actual params
    · apply Body.finish
      · exact .cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dj)
          (.cons run (.abrupt (.returnSome (.literal (.integer 0 "ULL") _
            (.integer (integer64 0)) (by rfl))) (by intro he; cases he)))
      · intro label he
        cases he
    · exact convert64 0 (by norm_num)
    · simp only [after, nscope]
  have chain : Declarations entry jState := .cons da (.cons dn (.cons dj (.nil jState)))
  have fields := chain.fields
  have effect := SourceNoAlloc.exec_effect run
    (by simp [ZeroLoop.loop, ZeroLoop.condition, ZeroLoop.loopBody, ZeroLoop.increment, zeroStoreStmt,
      SourceNoAlloc.Only, SourcePure.CallFree]) view.well
  have oldObjects : ∀id, id < before.nextObject → id ≠ object → after.objects id = before.objects id := by
    intro id oldId different
    have untouched : id ∉ [parameterIds entry.nextObject ZeroFrame.Var.j, object] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
      exact ⟨by simp only [parameterIds, ZeroFrame.parameterIds]; change id ≠ before.nextObject+2; omega, different⟩
    have same : middle.objects id = before.objects id :=
      (frame.outside id untouched).trans (fields.2.2.2.2 id oldId)
    change (middle.objects id).map _ = before.objects id
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
    change before.scope < middle.nextScope
    have b := well.current
    have nss := fields.2.2.1
    have nsf := frame.nextScope
    change jState.nextScope = before.nextScope+1 at nss
    omega
  have afterRep : WordArrayRep after object size (zeroData old start length) := by
    refine ⟨result.buffer.1, ?_, result.buffer.2.2⟩
    change (middle.objects object).map _ = some _
    rw [result.buffer.2.1]
    simp [wordObject]
  refine ⟨after, called, afterRep, rfl, rfl, ?_, afterWell, oldObjects⟩
  have fa : aState.foreign = entry.foreign := declare_foreign da
  have fn : nState.foreign = aState.foreign := declare_foreign dn
  have fj : jState.foreign = nState.foreign := declare_foreign dj
  exact effect.foreign.trans (fj.trans (fn.trans fa))

def localDeclaration : Stmt := .declare .u64 "j" (some (.literal (.integer 0 "ULL")))
def zeroReturn : Stmt := .returnValue (some (.literal (.integer 0 "ULL")))
def functionStatements : List Stmt := [localDeclaration, ZeroLoop.loop, zeroReturn]

private theorem tail_postcondition {F : Type} {context : Context F} {before after : State F}
    {object size start length owner j : Nat} {ids : Var → Nat} {old : Nat → Nat} {flow : Flow}
    (h : View before object size start length owner ids old j)
    (run : ExecList context before [ZeroLoop.loop, zeroReturn] flow after) :
    flow = .returned (.integer (integer64 0)) ∧ View after object size start length owner ids old length := by
  cases run with
  | cons first rest =>
    have post := loop_postcondition (length-j) h (by have ha := h.active; omega) first
    cases rest with
    | cons ret rest => cases ret
    | abrupt ret abrupt =>
      cases ret with
      | returnSome evaluated =>
        obtain ⟨rfl, rfl⟩ := eval_unique (by trivial)
          (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) evaluated
        exact ⟨rfl, post.2⟩
  | abrupt first abrupt =>
    exact False.elim (abrupt (loop_postcondition (length-j) h (by have ha := h.active; omega) first).1)

private theorem statements_postcondition {F : Type} {context : Context F}
    {before initialized after : State F} {object size start length owner : Nat}
    {ids : Var → Nat} {old : Nat → Nat} {flow : Flow}
    (declared : before.declare .u64 "j" (some (.integer (integer64 0))) = some initialized)
    (h : View initialized object size start length owner ids old 0)
    (run : ExecList context before functionStatements flow after) :
    flow = .returned (.integer (integer64 0)) ∧ View after object size start length owner ids old length := by
  have known : Exec context before localDeclaration .normal initialized := .declareSome (.literal _ _ _ (by rfl)) declared
  change ExecList context before (localDeclaration :: [ZeroLoop.loop, zeroReturn]) flow after at run
  cases run with
  | cons first rest =>
    obtain ⟨_, rfl⟩ := simple_unique (by trivial) known first
    exact tail_postcondition h rest
  | abrupt first abrupt => exact False.elim (abrupt (simple_unique (by trivial) known first).1.symm)

private theorem body_postcondition {F : Type} {context : Context F}
    {before initialized after : State F} {object size start length owner : Nat}
    {ids : Var → Nat} {old : Nat → Nat} {flow : Flow}
    (declared : before.declare .u64 "j" (some (.integer (integer64 0))) = some initialized)
    (h : View initialized object size start length owner ids old 0)
    (run : Body context functionStatements before functionStatements flow after) :
    flow = .returned (.integer (integer64 0)) ∧ View after object size start length owner ids old length := by
  cases run with
  | finish run finished => exact statements_postcondition declared h run
  | jump run target tail => simp [functionStatements, localDeclaration, ZeroLoop.loop, zeroReturn, labelTail] at target

/-- Every allowed full Call resets exactly the requested typed slice. -/
theorem every_zero_words_call {F : Type} {context : Context F}
    (selected : findFunction context.program "zero_words" = some zero_words_ast)
    (before after : State F) (object size start length : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object size old)
    (bound : start+length ≤ size) (fits : length < 2^64) (result : CallResult)
    (run : Call context "zero_words" [.pointer (wordPointer object start), .integer (integer64 length)] before result after) :
    result = .value (.integer (integer64 0)) ∧ WordArrayRep after object size (zeroData old start length) := by
  let entry : State F := {before.enterScope with environment := []}
  have we : WellScoped entry := wellScoped_environment (wellScoped_enter well) []
  obtain ⟨aState, nState, jState, da, dn, dj, view⟩ := initialize_parameters we rfl rep bound fits
  have params : bindParameters entry zero_words_ast.parameters
      [.pointer (wordPointer object start), .integer (integer64 length)] = some nState := by
    change bindParameters entry [(.pointer .u64,"a"), (.u64,"n")]
      [.pointer (wordPointer object start), .integer (integer64 length)] = some nState
    simp [bindParameters, da, dn]
  cases run with
  | external absent named foreign => exact False.elim (by rw [selected] at absent; cases absent)
  | internal selected' shapeRun parameters body converted finished =>
    have functionEq := Option.some.inj (selected.symm.trans selected')
    subst_vars
    have statementsEq : functionStatements = _ := Stmt.block.inj (ZeroLoop.loop_is_actual.symm.trans shapeRun)
    subst_vars
    have stateEq := Option.some.inj (params.symm.trans parameters)
    subst_vars
    obtain ⟨flowEq, post⟩ := body_postcondition dj view body
    cases flowEq
    have converted0 : Value.convert .u64 (.integer (integer64 0)) = some (.integer (integer64 0)) := convert64 0 (by norm_num)
    have resultEq := Option.some.inj (converted0.symm.trans converted)
    subst_vars
    refine ⟨rfl, post.buffer.1, ?_, post.buffer.2.2⟩
    change (State.objects _ object).map _ = some _
    rw [post.buffer.2.1]
    simp [wordObject]
  | internalVoid selected' shapeRun void parameters body finished =>
    have functionEq := Option.some.inj (selected.symm.trans selected')
    subst_vars
    cases void
  | internalTerminated selected' shapeRun parameters body =>
    have functionEq := Option.some.inj (selected.symm.trans selected')
    subst_vars
    have statementsEq : functionStatements = _ := Stmt.block.inj (ZeroLoop.loop_is_actual.symm.trans shapeRun)
    subst_vars
    have stateEq := Option.some.inj (params.symm.trans parameters)
    subst_vars
    have impossible := (body_postcondition dj view body).1
    cases impossible

/-- Actual independent source syntax, termination, and universal full-call
correctness of zero_words on typed initialized subranges. -/
theorem source_zero_slice_total (before : State Unit) (object size start length : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object size old)
    (bound : start+length ≤ size) (fits : length < 2^64) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
    (∃after, Call CopyLoop.sourceContext "zero_words" [.pointer (wordPointer object start), .integer (integer64 length)]
      before (.value (.integer (integer64 0))) after ∧
      WordArrayRep after object size (zeroData old start length) ∧ CopyLoop.CallerFrame before after object) ∧
    (∀after result, Call CopyLoop.sourceContext "zero_words" [.pointer (wordPointer object start), .integer (integer64 length)]
      before result after → result = .value (.integer (integer64 0)) ∧ WordArrayRep after object size (zeroData old start length)) := by
  exact ⟨FFTRecursivePV.actual_source_syntax,
    zero_words_call _ (by rfl) before object size start length old well rep bound fits,
    fun after result run => every_zero_words_call (by rfl) before after object size start length old well rep bound fits result run⟩

#print axioms initialize_parameters
#print axioms zero_words_call
#print axioms every_zero_words_call
#print axioms source_zero_slice_total
end RH080Next.FFTPV.ZeroSlice
