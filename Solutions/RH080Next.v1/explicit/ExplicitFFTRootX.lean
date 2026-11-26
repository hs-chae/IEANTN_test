/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootScale
import FFTCanonicalSourceFinal
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open IncrementSource (base)
open FFT.Limbs

def xPrefixStatements : List Stmt:=prefixStatements++[scaleStatement,divideStatement]
def xRemainingStatements : List Stmt:=match initialize_root_ast.body with
  | .block body=>body.drop 8
  | _=>[]

theorem actual_x_prefix : initialize_root_ast.body=.block (xPrefixStatements++xRemainingStatements):=by rfl

theorem xData_outside_first_five (input : Input) (index : Nat)
    (outside : ¬(input.layout.workStart≤ index ∧ index< input.layout.workStart+5)) :
    xData input index=ZeroSlice.zeroData input.old input.layout.workStart 80 index := by
  rw [xData,DivideSource.roundedData_outside _ _ _ _ _ _ outside]
  simp only [twicePiData,MultiplySmallSource.currentData,if_neg outside]
  exact piData_outside _ _ _ _ outside

theorem xData_zero_work (input : Input) (k : Nat) (lower : 5≤k) (upper : k<80) :
    xData input (input.layout.workStart+k)=0 := by
  rw [xData_outside_first_five input _ (by omega),ZeroSlice.zeroData_inside _ _ _ k upper]

theorem xData_outside_work (input : Input) (index : Nat)
    (outside : index< input.layout.workStart ∨ input.layout.workStart+80≤ index) :
    xData input index=input.old index := by
  rw [xData_outside_first_five input index (by omega),ZeroSlice.zeroData_outside _ _ _ index outside]

/-- The actual C floor divisions agree with the existing mathematical integer
root model's first value; no literal numerical root is supplied as a premise. -/
theorem xData_integer (input : Input) :
    CanonicalSource.represented (xData input) input.layout.workStart=
      (2*FFT.IntegerModel.piInteger)/(input.n:Int) := by
  have sign := xData_zero_work input 5 (by omega) (by omega)
  simp only [CanonicalSource.represented,sign,ne_eq,not_true_eq_false,decide_false,FFT.Limbs.signed]
  change (magnitude base 5 (fun i=>xData input (input.layout.workStart+i)):Int)=_
  rw [xData_value,Int.natCast_ediv,Int.natCast_mul]
  have piCast : (FFT.IntegerModel.piInteger.toNat:Int)=FFT.IntegerModel.piInteger:=by rfl
  rw [piCast]
  rfl

/-- Every source statement through the runtime x=2*pi/n construction is proved
for arbitrary live caller memory. The status id is the real post-callee fresh
identity, rather than a guessed allocation count. -/
theorem x_prefix_execution {F : Type} (context : Context F)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (multiplySelected : findFunction context.program "multiply_small"=some multiply_small_ast)
    (divideSelected : findFunction context.program "divide_small"=some divide_small_ast)
    (incrementSelected : findFunction context.program "increment_words"=some increment_words_ast)
    {before : State F} {input : Input} {owner : Nat} {ids : Param → Nat}
    (h : ParamView before input owner ids input.old) (scope : before.scope=owner) :
    ∃after statusId,ExecList context before xPrefixStatements .normal after ∧
      ScaleView after input owner statusId ids (xData input) ∧ after.scope=owner := by
  obtain ⟨piState,piRun,piView,piScope⟩:=pi_prefix_execution context zeroSelected h scope
  obtain ⟨returned,scaleState,scaleRun,statusDeclared,scaleView,scaleScope⟩:=scale_execution context multiplySelected piView piScope
  obtain ⟨after,divideRun,post,restored⟩:=divide_execution context divideSelected incrementSelected scaleView scaleScope
  exact ⟨after,returned.nextObject,append_normal piRun (.cons scaleRun (.cons divideRun .nil)),post,restored⟩

#print axioms actual_x_prefix
#print axioms xData_integer
#print axioms x_prefix_execution
end RH080Next.FFTPV.RootSource
