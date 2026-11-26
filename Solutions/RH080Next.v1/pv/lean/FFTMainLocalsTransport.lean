/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainRootBirthBase
import FFTTwiddleSource
import FFTBlockWhileEnvironment
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainTransport
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

/-- Retain the actual initialized source slots through an application frame.
The lookup premise describes actual lexical scope, independently of values. -/
theorem locals_of_frame {F I : Type} {before after : State F}
    {names : I → String} {types : I → CType} {ids : I → Nat} {owner : Nat}
    {values : I → Value} {writes : List Nat}
    (well : WellScoped before) (locals : Locals before names types ids owner values)
    (frame : Frame before.nextObject before after writes)
    (lookup : ∀v,after.environment.lookup (names v)=before.environment.lookup (names v))
    (away : ∀v,ids v∉writes) : Locals after names types ids owner values := by
  refine ⟨fun v=>(lookup v).trans (locals.lookup v),?_,locals.distinct,
    lt_of_lt_of_le locals.bound frame.nextScope⟩
  intro v
  exact ⟨(locals.slots v).storable,
    (frame.outside _ (well.objectIds _ _ (locals.slots v).object) (away v)).trans
      (locals.slots v).object⟩

theorem array_of_frame {F : Type} {before after : State F}
    {object length : Nat} {data : Nat → Nat} {writes : List Nat}
    (well : WellScoped before) (rep : WordArrayRep before object length data)
    (frame : Frame before.nextObject before after writes) (away : object∉writes) :
    WordArrayRep after object length data :=
  ⟨frame.mode.trans rep.1,
    (frame.outside _ (well.objectIds _ _ rep.2.1) away).trans rep.2.1,rep.2.2⟩

theorem pure_assignment_environment {F : Type} {context : Context F}
    {before after : State F} {target expression : Expr} {flow : Flow}
    (closedTarget : SourcePure.CallFree target) (closedExpression : SourcePure.CallFree expression)
    (actual : Exec context before (.assign target expression) flow after) :
    after.environment=before.environment := by
  cases actual with
  | assign evaluated placed stored=>
    have first:=SourcePure.eval_state evaluated closedExpression
    have second:=SourcePure.place_state placed closedTarget
    subst_vars
    exact (SourceLocals.store_frame stored).1

theorem pure_declaration_lookup {F : Type} {context : Context F}
    {before after : State F} {type : CType} {cname keep : String}
    {expression : Expr} {flow : Flow}
    (closed : SourcePure.CallFree expression) (different : keep≠cname)
    (actual : Exec context before (.declare type cname (some expression)) flow after) :
    after.environment.lookup keep=before.environment.lookup keep := by
  cases actual with
  | declareSome evaluated declared=>
    have same:=SourcePure.eval_state evaluated closed
    subst_vars
    rw [SourceLocals.declare_environment declared]
    simp only [List.lookup,beq_eq_false_iff_ne.mpr different]

theorem full_name_ne_j (v : MainRootBirth.FullVar) : MainRootBirth.fullName v≠"j" := by
  cases v with
  | none=>decide
  | some v=>
    cases v with
    | inl v=>cases v with
      | none=>decide
      | some r=>cases r <;> decide
    | inr p=>cases p <;> decide

/-- All ten actual preexisting main bindings survive the unit store, j birth
and complete source twiddle while-loop.  No selected subset of locals is
silently substituted for the complete main environment. -/
theorem table_lookup {F : Type} {context : Context F} {before after : State F}
    (actual : ExecList context before
      [TwiddleSource.unitAssignment,TwiddleSource.jDeclaration,TwiddleSource.loop] .normal after)
    (v : MainRootBirth.FullVar) :
    after.environment.lookup (MainRootBirth.fullName v)=
      before.environment.lookup (MainRootBirth.fullName v) := by
  cases actual with
  | abrupt first impossible=>exact False.elim (impossible rfl)
  | cons first rest=>
    have firstEnv:=pure_assignment_environment (by trivial) (by trivial) first
    cases rest with
    | abrupt second impossible=>exact False.elim (impossible rfl)
    | cons second rest=>
      have secondLookup:=pure_declaration_lookup (by trivial) (full_name_ne_j v) second
      cases rest with
      | abrupt third impossible=>exact False.elim (impossible rfl)
      | cons third rest=>
        cases rest
        have thirdEnv:=BlockEnvironment.while_block_environment (by trivial) third
        rw [thirdEnv,secondLookup,firstEnv]

theorem full_main_after_table {F : Type} {context : Context F} {before after : State F}
    {n nId owner base status : Nat} {objects oldIds : MainAllocation.Role → Nat}
    {tableData workData : Nat → Nat}
    (locals : MainRootBirth.FullMainLocals before n nId owner objects oldIds base status)
    (well : WellScoped before)
    (table : WordArrayRep before (objects .twiddle) (n/2*12) tableData)
    (work : WordArrayRep before (objects .work) 512 workData)
    (frame : Frame before.nextObject before after [objects .twiddle,objects .work])
    (actual : ExecList context before
      [TwiddleSource.unitAssignment,TwiddleSource.jDeclaration,TwiddleSource.loop] .normal after) :
    MainRootBirth.FullMainLocals after n nId owner objects oldIds base status := by
  apply locals_of_frame well locals frame (table_lookup actual)
  intro v
  have t:=MultiplyParameters.array_slot_different table (locals.slots v)
  have w:=MultiplyParameters.array_slot_different work (locals.slots v)
  simp only [List.mem_cons,List.mem_nil_iff,or_false]
  exact fun h=>h.elim (fun h=>t h.symm) (fun h=>w h.symm)

#print axioms locals_of_frame
#print axioms array_of_frame
#print axioms pure_assignment_environment
#print axioms table_lookup
#print axioms full_main_after_table
end RH080Next.FFTPV.MainTransport
