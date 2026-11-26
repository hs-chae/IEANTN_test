/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTCopyAllExecutions
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CopyLoop
open GoldbachDirect GoldbachDirect.Semantics WordArrays PureDeterminism
open SourceLocals SourceScalarSlots SourceBindings

def zeroReturn : Stmt := .returnValue (some (.literal (.integer 0 "ULL")))
def localDeclaration : Stmt := .declare .u64 "j" (some (.literal (.integer 0 "ULL")))
def functionStatements : List Stmt := [localDeclaration, loop, zeroReturn]

private theorem tail_postcondition {F : Type} {context : Context F} {before after : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat} {flow : Flow}
    (h : View before outObject outLength outStart inObject inLength inStart length owner ids old input j)
    (run : ExecList context before [loop, zeroReturn] flow after) :
    flow = .returned (.integer (integer64 0)) ∧
      View after outObject outLength outStart inObject inLength inStart length owner ids old input length := by
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
    {before initialized after : State F}
    {outObject outLength outStart inObject inLength inStart length owner : Nat}
    {ids : Var → Nat} {old input : Nat → Nat} {flow : Flow}
    (declared : before.declare .u64 "j" (some (.integer (integer64 0))) = some initialized)
    (h : View initialized outObject outLength outStart inObject inLength inStart length owner ids old input 0)
    (run : ExecList context before functionStatements flow after) :
    flow = .returned (.integer (integer64 0)) ∧
      View after outObject outLength outStart inObject inLength inStart length owner ids old input length := by
  have known : Exec context before localDeclaration .normal initialized :=
    .declareSome (.literal _ _ _ (by rfl)) declared
  change ExecList context before (localDeclaration :: [loop, zeroReturn]) flow after at run
  cases run with
  | cons first rest =>
    obtain ⟨_, rfl⟩ := simple_unique (by trivial) known first
    exact tail_postcondition h rest
  | abrupt first abrupt =>
    exact False.elim (abrupt (simple_unique (by trivial) known first).1.symm)

private theorem body_postcondition {F : Type} {context : Context F}
    {before initialized after : State F}
    {outObject outLength outStart inObject inLength inStart length owner : Nat}
    {ids : Var → Nat} {old input : Nat → Nat} {flow : Flow}
    (declared : before.declare .u64 "j" (some (.integer (integer64 0))) = some initialized)
    (h : View initialized outObject outLength outStart inObject inLength inStart length owner ids old input 0)
    (run : Body context functionStatements before functionStatements flow after) :
    flow = .returned (.integer (integer64 0)) ∧
      View after outObject outLength outStart inObject inLength inStart length owner ids old input length := by
  cases run with
  | finish run finished => exact statements_postcondition declared h run
  | jump run target tail =>
    simp [functionStatements, localDeclaration, loop, zeroReturn, labelTail] at target

/-- Universal functional correctness for every allowed full source Call,
including actual parameter binding, declaration, loop, return and scope exit.
No selection of a favorable execution is needed for this postcondition. -/
theorem every_copy_words_call {F : Type} {context : Context F}
    (selected : findFunction context.program "copy_words" = some copy_words_ast)
    (before after : State F)
    (outObject outLength outStart inObject inLength inStart length : Nat)
    (old input : Nat → Nat) (well : WellScoped before)
    (outRep : WordArrayRep before outObject outLength old)
    (inRep : WordArrayRep before inObject inLength input)
    (shape : inObject = outObject → inLength = outLength)
    (ranges : outObject ≠ inObject ∨ outStart = inStart ∨ outStart+length ≤ inStart ∨ inStart+length ≤ outStart)
    (outBound : outStart+length ≤ outLength) (inBound : inStart+length ≤ inLength)
    (fits : length < 2^64) (result : CallResult)
    (run : Call context "copy_words"
      [.pointer (wordPointer outObject outStart), .pointer (wordPointer inObject inStart), .integer (integer64 length)]
      before result after) :
    result = .value (.integer (integer64 0)) ∧
      WordArrayRep after outObject outLength (prefixData old (fun i => input (inStart+i)) outStart length) ∧
      (∀i, i < length → after.load (wordPointer inObject (inStart+i)) = some (.integer (integer64 (input (inStart+i))))) := by
  let entry : State F := {before.enterScope with environment := []}
  have we : WellScoped entry := wellScoped_environment (wellScoped_enter well) []
  obtain ⟨outState, inState, nState, jState, dout, din, dn, dj, view⟩ :=
    initialize_parameters we rfl outRep inRep shape ranges outBound inBound fits
  have params : bindParameters entry copy_words_ast.parameters
      [.pointer (wordPointer outObject outStart), .pointer (wordPointer inObject inStart), .integer (integer64 length)] = some nState := by
    change bindParameters entry [(.pointer .u64,"out"), (.pointer .u64,"in"), (.u64,"n")]
      [.pointer (wordPointer outObject outStart), .pointer (wordPointer inObject inStart), .integer (integer64 length)] = some nState
    simp [bindParameters, dout, din, dn]
  cases run with
  | external absent named foreign => exact False.elim (by rw [selected] at absent; cases absent)
  | internal selected' shapeRun parameters body converted finished =>
    have functionEq := Option.some.inj (selected.symm.trans selected')
    subst_vars
    have statementsEq : functionStatements = _ := Stmt.block.inj (iterative_body_actual.symm.trans shapeRun)
    subst_vars
    have stateEq := Option.some.inj (params.symm.trans parameters)
    subst_vars
    obtain ⟨flowEq, post⟩ := body_postcondition dj view body
    cases flowEq
    have converted0 : Value.convert .u64 (.integer (integer64 0)) = some (.integer (integer64 0)) :=
      convert64 0 (by norm_num)
    have resultEq := Option.some.inj (converted0.symm.trans converted)
    subst_vars
    rename_i entered middle
    refine ⟨rfl, ⟨post.output.1, ?_, post.output.2.2⟩, ?_⟩
    · change (State.objects _ outObject).map _ = some _
      rw [post.output.2.1]
      simp [wordObject]
    · obtain ⟨data, rep, values⟩ := post.source
      have afterRep : WordArrayRep {middle.leaveScope entered.scope before.environment with scope := before.scope} inObject inLength data := by
        refine ⟨rep.1, ?_, rep.2.2⟩
        change (State.objects _ inObject).map _ = some _
        rw [rep.2.1]
        simp [wordObject]
      intro i hi
      have hib : inStart+i < inLength := by omega
      simpa only [values i hi] using word_load afterRep hib
  | internalVoid selected' shapeRun void parameters body finished =>
    have functionEq := Option.some.inj (selected.symm.trans selected')
    subst_vars
    cases void
  | internalTerminated selected' shapeRun parameters body =>
    have functionEq := Option.some.inj (selected.symm.trans selected')
    subst_vars
    have statementsEq : functionStatements = _ := Stmt.block.inj (iterative_body_actual.symm.trans shapeRun)
    subst_vars
    have stateEq := Option.some.inj (params.symm.trans parameters)
    subst_vars
    have impossible := (body_postcondition dj view body).1
    cases impossible

#print axioms every_copy_words_call
end RH080Next.FFTPV.CopyLoop
