/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTCopyParameters
import FFTRecursiveSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CopyLoop
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

structure CallerFrame {F : Type} (before after : State F) (object : Nat) : Prop where
  environment : after.environment = before.environment
  scope : after.scope = before.scope
  foreign : after.foreign = before.foreign
  well : WellScoped after
  objects : ∀id, id < before.nextObject → id ≠ object → after.objects id = before.objects id

theorem recursive_function_actual : FFTRecursivePV.copy_words_ast = copy_words_ast := by rfl

/-- Actual complete copy_words call, including source parameter binding, local
initialization, all iterations, return conversion, and caller scope restoration.
The actual typed input slice is preserved even in one shared allocation. -/
theorem copy_words_call {F : Type} (context : Context F)
    (selected : findFunction context.program "copy_words" = some copy_words_ast)
    (before : State F)
    (outObject outLength outStart inObject inLength inStart length : Nat)
    (old input : Nat → Nat)
    (well : WellScoped before)
    (outRep : WordArrayRep before outObject outLength old)
    (inRep : WordArrayRep before inObject inLength input)
    (shape : inObject = outObject → inLength = outLength)
    (ranges : outObject ≠ inObject ∨ outStart = inStart ∨ outStart+length ≤ inStart ∨ inStart+length ≤ outStart)
    (outBound : outStart+length ≤ outLength) (inBound : inStart+length ≤ inLength)
    (fits : length < 2^64) :
    ∃after, Call context "copy_words"
      [.pointer (wordPointer outObject outStart), .pointer (wordPointer inObject inStart), .integer (integer64 length)]
      before (.value (.integer (integer64 0))) after ∧
      WordArrayRep after outObject outLength (prefixData old (fun i => input (inStart+i)) outStart length) ∧
      (∀i, i < length → after.load (wordPointer inObject (inStart+i)) = some (.integer (integer64 (input (inStart+i))))) ∧
      CallerFrame before after outObject := by
  let entry : State F := {before.enterScope with environment := []}
  have we : WellScoped entry := wellScoped_environment (wellScoped_enter well) []
  obtain ⟨outState, inState, nState, jState, dout, din, dn, dj, view⟩ :=
    initialize_parameters we rfl outRep inRep shape ranges outBound inBound fits
  obtain ⟨middle, run, result, _, frame⟩ := loop_copy_output_frame context view
  let after : State F := {middle.leaveScope entry.scope before.environment with scope := before.scope}
  have nscope : nState.scope = entry.scope :=
    (declare_frame dn).1.trans ((declare_frame din).1.trans (declare_frame dout).1)
  have params : bindParameters entry copy_words_ast.parameters
      [.pointer (wordPointer outObject outStart), .pointer (wordPointer inObject inStart), .integer (integer64 length)] = some nState := by
    change bindParameters entry [(.pointer .u64,"out"), (.pointer .u64,"in"), (.u64,"n")]
      [.pointer (wordPointer outObject outStart), .pointer (wordPointer inObject inStart), .integer (integer64 length)] = some nState
    simp [bindParameters, dout, din, dn]
  have called : Call context "copy_words"
      [.pointer (wordPointer outObject outStart), .pointer (wordPointer inObject inStart), .integer (integer64 length)]
      before (.value (.integer (integer64 0))) after := by
    apply Call.internal (function := copy_words_ast) (entered := nState) (middle := middle)
      selected iterative_body_actual params
    · apply Body.finish
      · exact .cons (.declareSome
          (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dj)
          (.cons run (.abrupt (.returnSome (.literal (.integer 0 "ULL") _
            (.integer (integer64 0)) (by rfl))) (by intro he; cases he)))
      · intro label he
        cases he
    · exact convert64 0 (by norm_num)
    · simp only [after, nscope]
  have chain : Declarations entry jState :=
    .cons dout (.cons din (.cons dn (.cons dj (.nil jState))))
  have fields := chain.fields
  have effect := SourceNoAlloc.exec_effect run
    (by simp [loop, condition, ZeroLoop.condition, loopBody, increment, ZeroLoop.increment,
      storeStmt, SourceNoAlloc.Only, SourcePure.CallFree]) view.well
  have oldObjects : ∀id, id < before.nextObject → id ≠ outObject → after.objects id = before.objects id := by
    intro id oldId different
    have untouched : id ∉ [parameterIds entry.nextObject Var.j, outObject] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
      exact ⟨by simp only [parameterIds]; change id ≠ before.nextObject+3; omega, different⟩
    have same : middle.objects id = before.objects id :=
      (frame.outside id untouched).trans (fields.2.2.2.2 id oldId)
    change (middle.objects id).map _ = before.objects id
    rw [same]
    cases present : before.objects id with
    | none => rfl
    | some obj =>
      have storage : obj.storage ≠ .automatic entry.scope := by
        intro bad
        have bound := well.automatic id obj before.nextScope present bad
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
  have output : WordArrayRep after outObject outLength
      (prefixData old (fun i => input (inStart+i)) outStart length) := by
    refine ⟨result.output.1, ?_, result.output.2.2⟩
    change (middle.objects outObject).map _ = some _
    rw [result.output.2.1]
    simp [wordObject]
  have source : ∀i, i < length → after.load (wordPointer inObject (inStart+i)) =
      some (.integer (integer64 (input (inStart+i)))) := by
    obtain ⟨data, rep, values⟩ := result.source
    have afterRep : WordArrayRep after inObject inLength data := by
      refine ⟨rep.1, ?_, rep.2.2⟩
      change (middle.objects inObject).map _ = some _
      rw [rep.2.1]
      simp [wordObject]
    intro i hi
    have hiBound : inStart+i < inLength := by omega
    have load := word_load afterRep hiBound
    simpa only [values i hi] using load
  refine ⟨after, called, output, source, rfl, rfl, ?_, afterWell, oldObjects⟩
  have fo : outState.foreign = entry.foreign := declare_foreign dout
  have fi : inState.foreign = outState.foreign := declare_foreign din
  have fn : nState.foreign = inState.foreign := declare_foreign dn
  have fj : jState.foreign = nState.foreign := declare_foreign dj
  exact effect.foreign.trans (fj.trans (fn.trans (fi.trans fo)))

def sourceContext : Context Unit :=
  {program := FFTRecursivePV.program, foreign := fun _ _ _ _ _ => False,
   headerConstant := fun _ => none, builtin := fun _ _ => none}

/-- Independent recursive-C source syntax correspondence is consumed together
with the full actual source helper execution. This does not claim correctness
or numerical output of the complete FFT application. -/
theorem source_copy_words_call (before : State Unit)
    (outObject outLength outStart inObject inLength inStart length : Nat)
    (old input : Nat → Nat) (well : WellScoped before)
    (outRep : WordArrayRep before outObject outLength old)
    (inRep : WordArrayRep before inObject inLength input)
    (shape : inObject = outObject → inLength = outLength)
    (ranges : outObject ≠ inObject ∨ outStart = inStart ∨ outStart+length ≤ inStart ∨ inStart+length ≤ outStart)
    (outBound : outStart+length ≤ outLength) (inBound : inStart+length ≤ inLength)
    (fits : length < 2^64) :
    GoldbachDirect.Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
    ∃after, Call sourceContext "copy_words"
      [.pointer (wordPointer outObject outStart), .pointer (wordPointer inObject inStart), .integer (integer64 length)]
      before (.value (.integer (integer64 0))) after ∧
      WordArrayRep after outObject outLength (prefixData old (fun i => input (inStart+i)) outStart length) ∧
      (∀i, i < length → after.load (wordPointer inObject (inStart+i)) = some (.integer (integer64 (input (inStart+i))))) ∧
      CallerFrame before after outObject :=
  ⟨FFTRecursivePV.actual_source_syntax,
    copy_words_call sourceContext (by rfl) before outObject outLength outStart inObject inLength inStart length
      old input well outRep inRep shape ranges outBound inBound fits⟩

#print axioms recursive_function_actual
#print axioms copy_words_call
#print axioms source_copy_words_call
end RH080Next.FFTPV.CopyLoop
