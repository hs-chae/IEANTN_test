/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FapSource
import FapMain
import FapRationalBridge
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FapPV
open GoldbachDirect ScalarHost RH080Next.Explicit

/-- Actual captured scalar arguments of the locked Fap400 C host harness. -/
def SourceScalarOutput (f0 area height v0 v1 mu2 maximum : Nat) : Prop :=
  Correspondence.SourceSyntaxCorresponds source program ∧
    mainOutput program (fun f => Execution.call 10000 f []) =
      some [f0,area,height,v0,v1,mu2,maximum]

theorem actual_source_scalar_output :
    SourceScalarOutput 799999999999990000 16297236881532502 1142770022680000
      14047086942420000 40617111385600000 760944122290429 6915614327570000 :=
  ⟨actual_source_syntax,actual_main_output⟩

theorem source_output_finite_specification (f0 area height v0 v1 mu2 maximum : Nat)
    (h : SourceScalarOutput f0 area height v0 v1 mu2 maximum) :
    f0=Model.f0Numerator ∧ area=Model.positiveAreaNumerator ∧
    height=Model.heightNumerator ∧ v0=Model.firstVariationNumerator ∧
    v1=Model.derivativeVariationNumerator ∧ mu2=Model.secondMomentNumerator ∧
    maximum=Model.maximumNumerator := by
  have he := actual_main_output.symm.trans h.2
  simp only [Option.some.injEq,List.cons.injEq,and_true] at he
  rcases he with ⟨hf0,harea,hheight,hv0,hv1,hmu2,hmaximum⟩
  subst f0; subst area; subst height; subst v0; subst v1; subst mu2; subst maximum
  exact ⟨Model.f0Numerator_exact.symm,Model.positiveAreaNumerator_exact.symm,
    Model.heightNumerator_exact.symm,Model.firstVariationNumerator_exact.symm,
    Model.derivativeVariationNumerator_exact.symm,Model.secondMomentNumerator_exact.symm,
    Model.maximumNumerator_exact.symm⟩

theorem source_output_mathematical_boundaries (f0 area height v0 v1 mu2 maximum : Nat)
    (h : SourceScalarOutput f0 area height v0 v1 mu2 maximum) :
    nodalF0 Data.affineNodes 80 = (f0 : ℝ)/(80*10000000000000000) ∧
    nodalH Data.affineNodes 80 = (height : ℝ)/10000000000000000 ∧
    nodalV1 Data.affineNodes 80 = (v1 : ℝ)/10000000000000000 ∧
    nodalMu2Upper Data.affineNodes 80 ≤ (mu2 : ℝ)/(6*80^3*1000000000) := by
  have he := actual_main_output.symm.trans h.2
  simp only [Option.some.injEq,List.cons.injEq,and_true] at he
  rcases he with ⟨hf0,harea,hheight,hv0,hv1,hmu2,hmaximum⟩
  subst f0; subst area; subst height; subst v0; subst v1; subst mu2; subst maximum
  constructor
  · rw [←qF0_cast,actual_qF0]
    norm_num
  constructor
  · rw [←qH_cast,actual_qH]
    norm_num
  constructor
  · rw [←qV1_cast,actual_qV1]
    norm_num
  · have hq : (qMu2 Data.affineNodes 80 : ℝ) ≤
        (((760944122290429 : ℚ)/(6*80^3*1000000000) : ℚ) : ℝ) := by
      exact_mod_cast actual_qMu2
    rw [qMu2_cast] at hq
    convert hq using 1 <;> norm_num

theorem source_first_nodal_boundaries :
    nodalF0 Data.affineNodes 80 = (799999999999990000 : ℝ)/(80*10000000000000000) ∧
    nodalH Data.affineNodes 80 = (1142770022680000 : ℝ)/10000000000000000 ∧
    nodalV1 Data.affineNodes 80 = (40617111385600000 : ℝ)/10000000000000000 ∧
    nodalMu2Upper Data.affineNodes 80 ≤ (760944122290429 : ℝ)/(6*80^3*1000000000) := by
  simpa only [Nat.cast_ofNat] using
    source_output_mathematical_boundaries _ _ _ _ _ _ _ actual_source_scalar_output

#print axioms actual_source_scalar_output
#print axioms source_output_finite_specification
#print axioms source_output_mathematical_boundaries
#print axioms source_first_nodal_boundaries
end RH080Next.FapPV
