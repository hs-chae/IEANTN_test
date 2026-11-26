/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixFront
import FFTRecursiveOutputSummary
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.MainCertificate
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource MainRootBirth

def exponent : InputLoader.Profile → Nat | .fap=>17 | .w4=>24
theorem grid_power (p : InputLoader.Profile) : p.grid=2^(exponent p) := by cases p <;> rfl

/-- Independently kernel-proved mathematical FFT data. This record contains
no actual C state, execution, source status, observed output or norm answer.
Its fields are instantiated by the literal accepted N17/N24 trace proofs. -/
structure Certificate (p : InputLoader.Profile) where
  rest : List FFT.IntegerModel.CInt
  stages : Nat → List FFT.IntegerModel.CInt
  output : List FFT.IntegerModel.CInt
  twiddles : FFT.IntegerModel.TwiddleTrace (FFT.IntegerModel.root p.grid) (FFT.IntegerModel.unit,0) rest
  length : ((FFT.IntegerModel.unit,0)::rest).length=p.grid/2
  chains : ∀t,t<exponent p → FFT.IntegerModel.DecimationTrace (exponent p-(t+1))
    ((FFT.IntegerModel.unit,0)::rest) (stages (t+1))
  mass : FFT.coefficientMass p.grid (fun j=>FFT.IntegerModel.decode (p.mathematicalInput j))≤362
  stageError : ∀t,t<exponent p → ∀j,j<2^t →
    ‖FFT.IntegerModel.decode ((stages (t+1)).getD j (0,0))-FFT.negativeRoot (2*2^t)^j‖≤
      (1/10000000000000000000:ℝ)
  trace : FFT.IntegerModel.ExecutionTrace stages p.mathematicalInput (exponent p) 0 1 output

theorem Certificate.output_norm {p : InputLoader.Profile} (certificate : Certificate p)
    (k : Nat) (hk : k<p.grid) : ‖FFT.IntegerModel.decode (certificate.output.getD k (0,0))‖≤400 := by
  have mass : FFT.coefficientMass (2^exponent p) (fun j=>FFT.IntegerModel.decode (p.mathematicalInput j))≤362 := by
    rw [←grid_power]
    exact certificate.mass
  have inside : k<2^exponent p := by rw [←grid_power];exact hk
  exact certificate.trace.subtransform_norm_le (S:=exponent p) (le_refl _)
    (by cases p <;> decide) (by decide) (by simp) mass certificate.stageError k inside

theorem input_cell_normalized (e : Nat) (bound : e<2*InputCell.scale) :
    NormalizedCell (InputCell.cell e) 0 := by
  have mag : InputCell.magnitudeValue e≤InputCell.scale := by
    unfold InputCell.magnitudeValue
    split_ifs <;> dsimp [InputCell.scale] at * <;> omega
  have top : InputCell.magnitudeValue e*100/InputCell.base/InputCell.base<InputCell.base := by
    dsimp [InputCell.base,InputCell.scale] at *
    omega
  have mod1:=Nat.mod_lt (InputCell.magnitudeValue e*100) (by norm_num [InputCell.base] : 0<InputCell.base)
  have mod2:=Nat.mod_lt (InputCell.magnitudeValue e*100/InputCell.base) (by norm_num [InputCell.base] : 0<InputCell.base)
  have sign : InputCell.signValue e≤1 := by unfold InputCell.signValue;split_ifs <;> omega
  constructor
  · intro c d hd
    fin_cases c <;> interval_cases d <;>
      simp only [InputCell.cell,CanonicalSource.canonicalData] <;> split_ifs <;>
      simp [InputCell.rawCell,InputCell.packed,Function.update,InputCell.base] <;>
      first | exact top | exact mod1 | exact mod2 | omega
  · intro c
    fin_cases c <;>
      simp only [InputCell.cell,CanonicalSource.canonicalData] <;> split_ifs <;>
      simp [InputCell.rawCell,InputCell.packed,Function.update] <;> omega

theorem loaded_normalized (p : InputLoader.Profile) (k : Nat) (hk : k<p.grid) :
    NormalizedCell (MainSuffix.loadedData p) k := by
  have shape:=p.shape
  have digits : ∀c : Fin 2,∀d,d<5 → MainSuffix.loadedData p (12*k+6*c.val+d)<1000000000 := by
    intro c d hd
    have small : 6*c.val+d<12 := by have h:=c.isLt;omega
    rw [show 12*k+6*c.val+d=12*k+(6*c.val+d) by omega]
    unfold MainSuffix.loadedData
    rw [InputLoader.currentData_decoded _ _ _ k _ shape.2.1 hk small]
    split_ifs with front mirror
    · simpa only [Nat.mul_zero,Nat.zero_add] using (input_cell_normalized _ (p.encoded_bound k front)).1 c d hd
    · simpa only [Nat.mul_zero,Nat.zero_add] using (input_cell_normalized _ (p.encoded_bound _ mirror)).1 c d hd
    · norm_num
  have signs : ∀c : Fin 2,MainSuffix.loadedData p (12*k+6*c.val+5)≤1 := by
    intro c
    have small : 6*c.val+5<12 := by have h:=c.isLt;omega
    rw [show 12*k+6*c.val+5=12*k+(6*c.val+5) by omega]
    unfold MainSuffix.loadedData
    rw [InputLoader.currentData_decoded _ _ _ k _ shape.2.1 hk small]
    split_ifs with front mirror
    · simpa only [Nat.mul_zero,Nat.zero_add] using (input_cell_normalized _ (p.encoded_bound k front)).2 c
    · simpa only [Nat.mul_zero,Nat.zero_add] using (input_cell_normalized _ (p.encoded_bound _ mirror)).2 c
    · norm_num
  exact ⟨digits,signs⟩

def bufferRole : Buffer → MainAllocation.Role
  | .output=>.output | .input=>.data | .twiddle=>.twiddle | .work=>.work
theorem buffer_role_injective : Function.Injective bufferRole := by
  intro a b same
  cases a <;> cases b <;> simp_all [bufferRole]

def buffers (p : InputLoader.Profile) (objects : MainAllocation.Role → Nat)
    (different : Function.Injective objects) : Buffers p.grid where
  object:=fun r=>objects (bufferRole r)
  length:=fun r=>MainAllocation.length p.grid (bufferRole r)
  distinct:=different.comp buffer_role_injective
  outputBound:=by simp [bufferRole,MainAllocation.length,Nat.mul_comm]
  inputBound:=by simp [bufferRole,MainAllocation.length,Nat.mul_comm]
  twiddleBound:=by cases p <;> norm_num [bufferRole,MainAllocation.length,InputLoader.Profile.grid]
  workBound:=by norm_num [bufferRole,MainAllocation.length]

theorem helpers {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) : Helpers context := by
  constructor <;> rw [pinned] <;> cases p <;> rfl

#print axioms input_cell_normalized
#print axioms loaded_normalized
#print axioms helpers
#print axioms Certificate.output_norm
end RH080Next.FFTPV.MainCertificate
