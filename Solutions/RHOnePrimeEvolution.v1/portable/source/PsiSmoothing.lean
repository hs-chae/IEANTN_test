/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.Zeta
import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Actual-psi smoothing consumers with explicit analytic obligations.
The remaining contracts concern an exact averaged explicit formula, the actual
zero sum with multiplicity, its density/moment estimate, and elementary averaged
main/trivial terms. None assumes the target psi bound. The two Fourier-moment
numerical predicates are not asserted as axioms or proved by native execution.
-/
namespace PsiSmoothing
open Real MeasureTheory Set

noncomputable def parabola (u : ℝ) : ℝ := (3 / 4 : ℝ) * (1 - u ^ 2)
noncomputable def box (_u : ℝ) : ℝ := 1 / 2
noncomputable def v (L : ℝ) : ℝ := L / 2 - Real.log L
noncomputable def delta (L : ℝ) : ℝ := L / (2 * Real.pi * Real.sqrt (Real.exp L))
noncomputable def average (k : ℝ → ℝ) (s L : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, k u * Chebyshev.psi
    (Real.exp L * Real.exp ((s + u) * delta L))
noncomputable def mainAverage (k : ℝ → ℝ) (s L : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, k u *
    (Real.exp L * Real.exp ((s + u) * delta L))
noncomputable def trivial (t : ℝ) : ℝ := -(Real.log (1 - t ^ (-2 : ℤ))) / 2
noncomputable def trivialAverage (k : ℝ → ℝ) (s L : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, k u * trivial
    (Real.exp L * Real.exp ((s + u) * delta L))
noncomputable def fourier (k : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, k u * Real.cos (y * u)
noncomputable def J (k : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ),
    (|fourier k y| - if y ≤ 1 then 1 else 0) * (Real.log y) ^ j / y
abbrev Zero := IEANTN.zetaZeroesIn (Set.Ioo 0 1) Set.univ
noncomputable def zeroPacket (k : ℝ → ℝ) (s L : ℝ) (ρ : Zero) : ℂ :=
  (Real.exp L : ℂ) ^ (ρ : ℂ) / (ρ : ℂ) *
    (∫ u in (-1 : ℝ)..1, (k u : ℂ) *
      Complex.exp ((ρ : ℂ) * (((s + u) * delta L : ℝ) : ℂ))) *
    (IEANTN.zetaOrder ρ : ℂ)
noncomputable def zeroAverage (k : ℝ → ℝ) (s L : ℝ) : ℂ :=
  ∑' ρ : Zero, zeroPacket k s L ρ
noncomputable def envelope (j0 j1 L : ℝ) : ℝ :=
  (v L ^ 2 + 2 * j0 * v L + 2 * j1 + L) / (2 * Real.pi) + 14 / 100

/-- A precise, unformalized analytic identity from the integrated explicit formula.
Summability is required, so no totalized-tsum success is possible. -/
def AveragedExplicitFormula (k : ℝ → ℝ) : Prop :=
  ∀ L : ℝ, 35 ≤ L → ∀ s : ℝ, s = -1 ∨ s = 1 →
    Summable (zeroPacket k s L) ∧
    average k s L = mainAverage k s L - (zeroAverage k s L).re -
      Real.log (2 * Real.pi) + trivialAverage k s L

/-- Exact zero observable; this remaining analytic lemma is derived in the written
proof from the zero-count formula, regularized absolute moments, and the imaginary
shift. It is not a psi-error premise. -/
def ZeroDensityMomentEstimate (k : ℝ → ℝ) : Prop :=
  RiemannHypothesis → ∀ L : ℝ, 35 ≤ L → ∀ s : ℝ, s = -1 ∨ s = 1 →
    ‖zeroAverage k s L‖ ≤ Real.sqrt (Real.exp L) *
      ((v L ^ 2 + 2 * J k 0 * v L + 2 * J k 1) / (2 * Real.pi) + 131 / 1000)

/-- Actual main integral, not a bound on psi. -/
def MainTermEstimate (k : ℝ → ℝ) : Prop :=
  ∀ L : ℝ, 35 ≤ L → ∀ s : ℝ, s = -1 ∨ s = 1 →
    |mainAverage k s L - Real.exp L| ≤
      Real.sqrt (Real.exp L) * (L / (2 * Real.pi) + 1 / 1000)

/-- Actual integrated trivial-zero contribution, including the constant log(2pi). -/
def TrivialTermEstimate (k : ℝ → ℝ) : Prop :=
  ∀ L : ℝ, 35 ≤ L → ∀ s : ℝ, s = -1 ∨ s = 1 →
    |trivialAverage k s L - Real.log (2 * Real.pi)| ≤
      Real.sqrt (Real.exp L) * (1 / 1000)

theorem v_nonneg {L : ℝ} (hL : 35 ≤ L) : 0 ≤ v L := by
  have hLp : 0 < L := by linarith
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < L / 2)
  rw [Real.log_div hLp.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  unfold v
  linarith

theorem delta_pos {L : ℝ} (hL : 35 ≤ L) : 0 < delta L := by
  unfold delta
  exact div_pos (by linarith) (by positivity)

theorem average_integrable (k : ℝ → ℝ) (hk : Continuous k) (s L : ℝ)
    (hL : 35 ≤ L) : IntervalIntegrable
      (fun u => k u * Chebyshev.psi (Real.exp L *
        Real.exp ((s + u) * delta L))) volume (-1) 1 := by
  have hd : 0 ≤ delta L := (delta_pos hL).le
  have hm : Monotone (fun u : ℝ =>
      Chebyshev.psi (Real.exp L * Real.exp ((s + u) * delta L))) := by
    intro a b hab
    apply Chebyshev.psi_mono
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos L).le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith : s + a ≤ s + b) hd
  have hi := hm.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := 1)
  exact hi.continuousOn_mul hk.continuousOn

theorem average_brackets (k : ℝ → ℝ) (hk : Continuous k)
    (hkn : ∀ u ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ k u)
    (hkm : (∫ u in (-1 : ℝ)..1, k u) = 1) {L : ℝ} (hL : 35 ≤ L) :
    average k (-1) L ≤ Chebyshev.psi (Real.exp L) ∧
      Chebyshev.psi (Real.exp L) ≤ average k 1 L := by
  have hi := average_integrable k hk (-1) L hL
  have hi' := average_integrable k hk 1 L hL
  have hc : IntervalIntegrable (fun u => k u * Chebyshev.psi (Real.exp L))
      volume (-1) 1 := (hk.intervalIntegrable (-1) 1).mul_const _
  have hconst : (∫ u in (-1 : ℝ)..1, k u * Chebyshev.psi (Real.exp L)) =
      Chebyshev.psi (Real.exp L) := by
    rw [intervalIntegral.integral_mul_const, hkm, one_mul]
  constructor
  · calc
      average k (-1) L ≤ ∫ u in (-1 : ℝ)..1, k u * Chebyshev.psi (Real.exp L) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hi hc
        intro u hu
        apply mul_le_mul_of_nonneg_left _ (hkn u hu)
        apply Chebyshev.psi_mono
        have he : Real.exp ((-1 + u) * delta L) ≤ 1 :=
          Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
            (by linarith [hu.2]) (delta_pos hL).le)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he (Real.exp_pos L).le
      _ = Chebyshev.psi (Real.exp L) := hconst
  · calc
      Chebyshev.psi (Real.exp L) =
          ∫ u in (-1 : ℝ)..1, k u * Chebyshev.psi (Real.exp L) := hconst.symm
      _ ≤ average k 1 L := by
        apply intervalIntegral.integral_mono_on (by norm_num) hc hi'
        intro u hu
        apply mul_le_mul_of_nonneg_left _ (hkn u hu)
        apply Chebyshev.psi_mono
        have he : 1 ≤ Real.exp ((1 + u) * delta L) :=
          Real.one_le_exp_iff.mpr (mul_nonneg (by linarith [hu.1]) (delta_pos hL).le)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he (Real.exp_pos L).le

/-- Whole-real-ray actual psi consumer. All remaining source contracts are printed
in its type; none is the desired pointwise psi inequality. -/
theorem psi_from_smoothing (k : ℝ → ℝ) (hk : Continuous k)
    (hkn : ∀ u ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ k u)
    (hkm : (∫ u in (-1 : ℝ)..1, k u) = 1)
    (rh : RiemannHypothesis) (hef : AveragedExplicitFormula k)
    (hzero : ZeroDensityMomentEstimate k) (hmain : MainTermEstimate k)
    (htriv : TrivialTermEstimate k) {j0 j1 : ℝ}
    (hJ0 : J k 0 ≤ j0) (hJ1 : J k 1 ≤ j1) :
    ∀ L : ℝ, 35 ≤ L → |Chebyshev.psi (Real.exp L) - Real.exp L| ≤
      Real.sqrt (Real.exp L) * envelope j0 j1 L := by
  intro L hL
  have hs : 0 ≤ Real.sqrt (Real.exp L) := Real.sqrt_nonneg _
  have hp : 0 < 2 * Real.pi := by positivity
  have hv : 0 ≤ v L := v_nonneg hL
  have hzm : (v L ^ 2 + 2 * J k 0 * v L + 2 * J k 1) / (2 * Real.pi) ≤
      (v L ^ 2 + 2 * j0 * v L + 2 * j1) / (2 * Real.pi) := by
    apply div_le_div_of_nonneg_right _ hp.le
    nlinarith
  have havg : ∀ s : ℝ, s = -1 ∨ s = 1 →
      |average k s L - Real.exp L| ≤
        Real.sqrt (Real.exp L) * envelope j0 j1 L := by
    intro s hs'
    have heq := (hef L hL s hs').2
    have hz := (Complex.abs_re_le_norm (zeroAverage k s L)).trans (hzero rh L hL s hs')
    have hm := hmain L hL s hs'
    have ht := htriv L hL s hs'
    have htri : |average k s L - Real.exp L| ≤
        |mainAverage k s L - Real.exp L| + |(zeroAverage k s L).re| +
          |trivialAverage k s L - Real.log (2 * Real.pi)| := by
      have h' := abs_sub_le (mainAverage k s L - Real.exp L) 0 (zeroAverage k s L).re
      simp only [sub_zero, zero_sub, abs_neg] at h'
      calc
        |average k s L - Real.exp L| =
            |(mainAverage k s L - Real.exp L) - (zeroAverage k s L).re +
              (trivialAverage k s L - Real.log (2 * Real.pi))| := by
          congr 1
          rw [heq]
          ring
        _ ≤ |(mainAverage k s L - Real.exp L) - (zeroAverage k s L).re| +
            |trivialAverage k s L - Real.log (2 * Real.pi)| := abs_add_le _ _
        _ ≤ _ := add_le_add h' le_rfl
    have hmz := mul_le_mul_of_nonneg_left hzm hs
    unfold envelope
    have hcollect :
        Real.sqrt (Real.exp L) * (L / (2 * Real.pi) + 1 / 1000) +
        Real.sqrt (Real.exp L) *
          ((v L ^ 2 + 2 * j0 * v L + 2 * j1) / (2 * Real.pi) + 131 / 1000) +
        Real.sqrt (Real.exp L) * (1 / 1000) ≤
        Real.sqrt (Real.exp L) *
          ((v L ^ 2 + 2 * j0 * v L + 2 * j1 + L) / (2 * Real.pi) + 14 / 100) := by
      ring_nf
      nlinarith
    apply (htri.trans (add_le_add (add_le_add hm (hz.trans
      (mul_le_mul_of_nonneg_left (add_le_add hzm le_rfl) hs))) ht)).trans hcollect
  have hb := average_brackets k hk hkn hkm hL
  have hm := abs_le.mp (havg (-1) (Or.inl rfl))
  have hp' := abs_le.mp (havg 1 (Or.inr rfl))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem parabola_continuous : Continuous parabola := by unfold parabola; fun_prop

theorem parabola_nonneg : ∀ u ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ parabola u := by
  intro u hu
  have h := mul_nonpos_of_nonneg_of_nonpos (by linarith [hu.1] : 0 ≤ u + 1)
    (by linarith [hu.2] : u - 1 ≤ 0)
  unfold parabola
  nlinarith

theorem parabola_mass : (∫ u in (-1 : ℝ)..1, parabola u) = 1 := by
  unfold parabola
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub]
  · rw [integral_pow]
    norm_num
  · exact intervalIntegrable_const
  · exact (continuous_id.pow 2).intervalIntegrable (-1) 1

theorem box_continuous : Continuous box := continuous_const

theorem box_nonneg : ∀ u ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ box u := by
  intro u hu
  norm_num [box]

theorem box_mass : (∫ u in (-1 : ℝ)..1, box u) = 1 := by
  norm_num [box, intervalIntegral.integral_const]

/-- The frozen NL B5 formula, now consumed on the actual psi whole ray.
The four exact analytic contracts and both actual integral moment bounds remain
visible; this is conditional closure, not complete analytic formalization. -/
theorem psi_B5 (rh : RiemannHypothesis)
    (hef : AveragedExplicitFormula parabola) (hz : ZeroDensityMomentEstimate parabola)
    (hm : MainTermEstimate parabola) (ht : TrivialTermEstimate parabola)
    (h0 : J parabola 0 ≤ 831 / 1000) (h1 : J parabola 1 ≤ 287 / 500) :
    ∀ L : ℝ, 35 ≤ L → |Chebyshev.psi (Real.exp L) - Real.exp L| ≤
      Real.sqrt (Real.exp L) * envelope (831 / 1000) (287 / 500) L :=
  psi_from_smoothing parabola parabola_continuous parabola_nonneg parabola_mass
    rh hef hz hm ht h0 h1

/-- A stronger one-box candidate with accepted rational moment enclosures;
formal analytic density/moment and explicit-formula inputs remain explicit. -/
theorem psi_box (rh : RiemannHypothesis)
    (hef : AveragedExplicitFormula box) (hz : ZeroDensityMomentEstimate box)
    (hm : MainTermEstimate box) (ht : TrivialTermEstimate box)
    (h0 : J box 0 ≤ 701 / 1000) (h1 : J box 1 ≤ 3 / 4) :
    ∀ L : ℝ, 35 ≤ L → |Chebyshev.psi (Real.exp L) - Real.exp L| ≤
      Real.sqrt (Real.exp L) * envelope (701 / 1000) (3 / 4) L :=
  psi_from_smoothing box box_continuous box_nonneg box_mass rh hef hz hm ht h0 h1

theorem psi_box_actual_x (rh : RiemannHypothesis)
    (hef : AveragedExplicitFormula box) (hz : ZeroDensityMomentEstimate box)
    (hm : MainTermEstimate box) (ht : TrivialTermEstimate box)
    (h0 : J box 0 ≤ 701 / 1000) (h1 : J box 1 ≤ 3 / 4) :
    ∀ x : ℝ, Real.exp 35 ≤ x → |Chebyshev.psi x - x| ≤
      Real.sqrt x * envelope (701 / 1000) (3 / 4) (Real.log x) := by
  intro x hx
  have hx0 : 0 < x := (Real.exp_pos 35).trans_le hx
  have hlog : 35 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 35) hx
    simpa only [Real.log_exp] using h
  have h := psi_box rh hef hz hm ht h0 h1 (Real.log x) hlog
  simpa only [Real.exp_log hx0] using h

theorem box_fourier {y : ℝ} (hy : y ≠ 0) : fourier box y = Real.sin y / y := by
  unfold fourier box
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left _ hy, integral_cos]
  simp only [mul_neg, mul_one, Real.sin_neg, smul_eq_mul]
  field_simp
  <;> ring

theorem v_gt_135 {L : ℝ} (hL : 35 ≤ L) : 27 / 2 < v L := by
  have he : (5 / 2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he2 : (25 / 4 : ℝ) < Real.exp 1 ^ 2 := by
    nlinarith [Real.exp_pos 1]
  have he4 : (625 / 16 : ℝ) < Real.exp 1 ^ 4 := by
    nlinarith [sq_nonneg (Real.exp 1 ^ 2 - 25 / 4)]
  have heq : Real.exp (4 : ℝ) = Real.exp 1 ^ 4 := by
    simpa using Real.exp_nat_mul 1 4
  have he35 : (35 : ℝ) < Real.exp 4 := by rw [heq]; linarith
  have hl35 : Real.log (35 : ℝ) < 4 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).mpr he35
  have hLp : 0 < L := by linarith
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < L / 35)
  rw [Real.log_div hLp.ne' (by norm_num : (35 : ℝ) ≠ 0)] at h
  unfold v
  linarith

/-- Genuine strict improvement of the full new envelope on the entire ray. -/
theorem box_improves_B5 {L : ℝ} (hL : 35 ≤ L) :
    1 / 2 < envelope (831 / 1000) (287 / 500) L -
      envelope (701 / 1000) (3 / 4) L := by
  have heq : envelope (831 / 1000) (287 / 500) L -
      envelope (701 / 1000) (3 / 4) L =
      ((13 / 50 : ℝ) * v L - 44 / 125) / (2 * Real.pi) := by
    unfold envelope
    ring
  rw [heq]
  apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  have hv := v_gt_135 hL
  linarith [Real.pi_lt_d2]

#print axioms psi_B5
#print axioms psi_box_actual_x
#print axioms box_improves_B5

#print axioms psi_from_smoothing
end PsiSmoothing
