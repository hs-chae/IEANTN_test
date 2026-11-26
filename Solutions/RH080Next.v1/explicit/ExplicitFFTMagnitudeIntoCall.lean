/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTMagnitudeInto
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MagnitudeIntoSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

def arguments (input : Input) : List Value:=[.pointer (wordPointer input.object input.start),.integer (integer64 input.value)]

theorem magnitude_into_call {F : Type} (context : Context F)
    (selected : findFunction context.program "magnitude_into"=some magnitude_into_ast)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (before : State F) (input : Input) (well : WellScoped before)
    (rep : WordArrayRep before input.object input.size input.old) :
    ∃after,Call context "magnitude_into" (arguments input) before (.value (.integer (integer64 0))) after ∧
      EveryCall context before "magnitude_into" (arguments input) (.value (.integer (integer64 0))) after ∧
      WordArrayRep after input.object input.size (finalData input) ∧ IncrementSource.FullCallerFrame before after input.object:=by
  let entry : State F:={before.enterScope with environment:=[]}
  have we : WellScoped entry:=wellScoped_environment (wellScoped_enter well) []
  obtain ⟨s1,s2,d1,d2,view⟩:=initialize_parameters input we rfl rep
  dsimp only [value] at d1 d2
  have declarations : Declarations entry s2:=.cons d1 (.cons d2 (.nil s2))
  have scope : s2.scope=entry.scope:=declarations.fields.2.1
  obtain ⟨zeroed,zeroRun,zeroEvery,zeroView,zeroFrame⟩:=zero_execution context zeroSelected view scope.ge
  have modBound : input.value%base<base:=Nat.mod_lt _ (by norm_num [base])
  have divBound : input.value/base<base:= (Nat.div_lt_iff_lt_mul (by norm_num [base])).mpr input.small
  obtain ⟨low,lowRun,lowEvery,lowView,lowFrame⟩:=store_execution context zeroView 0 (input.value%base) (by norm_num) (by norm_num) .mod
    (lt_trans modBound (by norm_num [base])) (binary64_mod input.value base (input_small64 input) (by norm_num [base]) (by norm_num [base]))
  obtain ⟨high,highRun,highEvery,highView,highFrame⟩:=store_execution context lowView 1 (input.value/base) (by norm_num) (by norm_num) .div
    (lt_trans divBound (by norm_num [base])) (binary64_div input.value base (input_small64 input) (by norm_num [base]) (by norm_num [base]))
  have returnRun : Exec context high (.returnValue (some (.literal (.integer 0 "ULL")))) (.returned (.integer (integer64 0))) high:=
    .returnSome (.literal _ _ _ (by rfl))
  have returnEvery:=every_pure (by constructor) returnRun
  have bodyRun : ExecList context s2 statements (.returned (.integer (integer64 0))) high:=
    .cons zeroRun (.cons lowRun (.cons highRun (.abrupt returnRun (by simp))))
  have bodyEvery : EveryList context s2 statements (.returned (.integer (integer64 0))) high:=
    every_cons zeroEvery (every_cons lowEvery (every_cons highEvery (every_abrupt returnEvery (by simp))))
  have parameters : bindParameters entry magnitude_into_ast.parameters (arguments input)=some s2:=by
    change bindParameters entry [(.pointer .u64,"out"),(.u64,"value")] (arguments input)=some s2
    simp [bindParameters,arguments,d1,d2]
  let after : State F:={high.leaveScope entry.scope before.environment with scope:=before.scope}
  have run : Call context "magnitude_into" (arguments input) before (.value (.integer (integer64 0))) after:=by
    apply Call.internal (function:=magnitude_into_ast) (entered:=s2) (middle:=high) selected actual_body parameters
    · exact Body.finish bodyRun (by intro label impossible;cases impossible)
    · exact convert64 0 (by norm_num)
    · simp only [after,scope]
  have every : EveryCall context before "magnitude_into" (arguments input) (.value (.integer (integer64 0))) after:=by
    apply every_call_from_body selected actual_body (by intro bad;cases bad) parameters bodyEvery
      (by intro label;rfl) (convert64 0 (by norm_num))
    simp only [after,scope]
  have w1:=wellScoped_declare we d1
  have birth1:=ApplicationBirthFrame.declare_frame entry.nextObject [input.object] we (le_refl _) d1
  have birth2:=ApplicationBirthFrame.declare_frame entry.nextObject [input.object] w1 birth1.fresh d2
  have paramsFrame:=birth1.trans birth2
  have bodyFrame:=full_caller_trans zeroFrame (full_caller_trans lowFrame highFrame)
  have whole:=paramsFrame.trans (lower_frame (unary_frame bodyFrame) paramsFrame.nextObject)
  have enteredFrame : ApplicationBirthFrame.Frame before.nextObject before.enterScope high [input.object]:=
    ⟨whole.well,whole.fresh,whole.nextObject,whole.nextScope,whole.mode,whole.foreign,whole.outside⟩
  have callerFrame:=ApplicationBirthFrame.close_frame well (le_refl _) enteredFrame
  exact ⟨after,run,every,IncrementSource.wordArray_leave highView.array,full_caller_frame rfl rfl callerFrame⟩

#print axioms magnitude_into_call
end RH080Next.FFTPV.MagnitudeIntoSource
