/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Consumer
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Real.Pi.Bounds
namespace MertensPositive
open Real Finset ArithmeticFunction MeasureTheory Set

/-- Paper zeros: the nonreal zeta zeros in the open critical strip. The actual pole and
negative-even trivial zeros are excluded by this concrete domain. -/
def PaperZero := {s : ℂ // 0 < s.re ∧ s.re < 1 ∧ s.im ≠ 0 ∧ riemannZeta s = 0}
/-- Actual order of vanishing; counted with multiplicity, rather than enumerating distinct
zeros as if all were simple. This is Mathlib's meromorphic order, converted to Nat. -/
noncomputable def zeroMultiplicity (s : PaperZero) : ℕ :=
  ((meromorphicOrderAt riemannZeta s.val).untopD 0).toNat
noncomputable def reciprocalWeight (s : PaperZero) : ℝ :=
  (zeroMultiplicity s : ℝ) / s.val.im^2
noncomputable def reciprocalMass : ℝ := ∑' s : PaperZero, reciprocalWeight s
/-- BFKNW (29), specialized to m=1, on the actual zero domain and multiplicities. -/
noncomputable def J1 (x : ℝ) : ℝ :=
  ∑' s : PaperZero, (zeroMultiplicity s : ℝ) * x^(s.val.re-1) / s.val.im^2
/-- Original published BFKNW Proposition29(ii), (154), x≥2. -/
def SourceBFKNW154 : Prop := ∀ x : ℝ, 2 ≤ x →
  |CA x - Real.log x + Real.eulerMascheroniConstant| ≤
    |Chebyshev.psi x-x|/x + J1 x + Real.log (2*Real.pi)/x
/-- Original published BFKNW Lemma21, (85)-(90), m=1. The full ordinate sum is
absolutely convergent and at most a1=.04620999. This is cited numerical-source evidence,
not a formal recomputation of its Platt/LMFDB database. -/
def SourceBFKNW21 : Prop :=
  Summable reciprocalWeight ∧ reciprocalMass ≤ 0.04620999

/-- RH is applied exactly as defined by pinned Mathlib; no additional location assertion. -/
theorem paperZero_re (hRH : RiemannHypothesis) (s : PaperZero) : s.val.re = 1/2 := by
  apply hRH s.val s.property.2.2.2
  · rintro ⟨n,hn⟩
    have hr := congrArg Complex.re hn
    norm_num at hr
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith [s.property.1]
  · intro hn
    have hr := congrArg Complex.re hn
    norm_num at hr
    linarith [s.property.2.1]

theorem J1_eq_mass_div_sqrt (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    J1 x = reciprocalMass / Real.sqrt x := by
  have he : x^((1:ℝ)/2-1) = (Real.sqrt x)⁻¹ := by
    rw [show (1:ℝ)/2-1=-(1/2) by norm_num,Real.rpow_neg hx.le,← Real.sqrt_eq_rpow]
  unfold J1 reciprocalMass
  calc (∑' s : PaperZero, (zeroMultiplicity s:ℝ)*x^(s.val.re-1)/s.val.im^2) =
      ∑' s : PaperZero, reciprocalWeight s * (Real.sqrt x)⁻¹ := by
        apply tsum_congr
        intro s
        rw [paperZero_re hRH s,he]
        unfold reciprocalWeight
        ring
    _ = (∑' s : PaperZero,reciprocalWeight s)*(Real.sqrt x)⁻¹ := tsum_mul_right
    _ = (∑' s : PaperZero,reciprocalWeight s)/Real.sqrt x := by ring

theorem log_two_pi_lt_two : Real.log (2*Real.pi) < 2 := by
  apply (Real.log_lt_iff_lt_exp (by positivity)).mpr
  have he : (Real.exp 1)^2 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hpow : (2.7:ℝ)^2 < (Real.exp 1)^2 := by
    gcongr
    linarith [Real.exp_one_gt_d9]
  rw [he] at hpow
  nlinarith [Real.pi_lt_d2]

/-- The summability guard in the published source remains effective for the actual J1 sum. -/
theorem J1_summable_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hs : Summable reciprocalWeight) :
    Summable (fun s : PaperZero => (zeroMultiplicity s:ℝ)*x^(s.val.re-1)/s.val.im^2) := by
  have he : x^((1:ℝ)/2-1) = (Real.sqrt x)⁻¹ := by
    rw [show (1:ℝ)/2-1=-(1/2) by norm_num,Real.rpow_neg hx.le,← Real.sqrt_eq_rpow]
  apply (hs.mul_right ((Real.sqrt x)⁻¹)).congr
  intro s
  rw [paperZero_re hRH s,he]
  unfold reciprocalWeight
  ring

/-- Generic exact source transport. Root can also instantiate this with an independently
proved xi-based mass bound, without requiring any numerical zero-spacing assumption. -/
theorem CA_corollary_from_mass_bound (h154 : SourceBFKNW154)
    (_hSum : Summable reciprocalWeight) (hMass : reciprocalMass ≤ 0.0476) : PublishedBFKNW_CA_RH := by
  intro hRH x hx
  have hx0 : 0 < x := by linarith
  have hy : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have h := h154 x hx
  rw [J1_eq_mass_div_sqrt hRH hx0] at h
  have hJ : reciprocalMass / Real.sqrt x ≤ 0.0476 / Real.sqrt x :=
    div_le_div_of_nonneg_right hMass hy.le
  have hc : Real.log (2*Real.pi)/x ≤ 2/x :=
    div_le_div_of_nonneg_right log_two_pi_lt_two.le hx0.le
  linarith

/-- Derived corollary from separately visible original BFKNW154 and BFKNW21 inputs. -/
theorem CA_corollary_from_sources (h154 : SourceBFKNW154) (h21 : SourceBFKNW21) :
    PublishedBFKNW_CA_RH :=
  CA_corollary_from_mass_bound h154 h21.1 (by linarith [h21.2])

/-- Final kernel-checked conditional consumer. Remaining premises are only the literal
BFKNW154 and BFKNW21 source claims, Büthe's three finite source statements, and RH. -/
theorem first_mertens_positive_from_original_sources
    (h154 : SourceBFKNW154) (h21 : SourceBFKNW21)
    (hPsi : PublishedButhePsi) (hThetaL : PublishedButheThetaLower)
    (hThetaU : PublishedButheThetaUpper) (hRH : RiemannHypothesis)
    {x : ℝ} (hx : Real.exp 24 ≤ x) (hxM : x ≤ (10:ℝ)^19) :
    0.006 / Real.sqrt x < A x - Real.log x - E :=
  first_mertens_positive (CA_corollary_from_sources h154 h21)
    hPsi hThetaL hThetaU hRH hx hxM

#print axioms first_mertens_positive_from_original_sources
end MertensPositive
