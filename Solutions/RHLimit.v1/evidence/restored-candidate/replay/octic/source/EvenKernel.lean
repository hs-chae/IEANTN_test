/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import QuarticWindow
import PsiSmoothing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! One reusable even-polynomial-window consumer for the whole count/width
frontier. The actual analytic and scalar obligations are explicit parameters.
This unifies quartic, sextic and octic applications; it does not assert their
remaining analytic contracts as axioms. -/
namespace EvenKernel
open Real MeasureTheory Set Finset
noncomputable def kernel (n : ℕ) (u : ℝ) : ℝ := max 0 (1 - u ^ (2 * n))
noncomputable def mass (n : ℕ) : ℝ := 4 * (n : ℝ) / (2 * (n : ℝ) + 1)
noncomputable def D (C L : ℝ) : ℝ := C / 2 * L - 1
noncomputable def δ (C L : ℝ) : ℝ := D C L * Real.exp (-L / 2)
noncomputable def a (C L : ℝ) : ℝ := Real.exp (L - δ C L)
noncomputable def b (C L : ℝ) : ℝ := Real.exp (L + δ C L)
noncomputable def population (n : ℕ) (C L : ℝ) : ℝ :=
  ∑ p ∈ QuarticWindow.primesBetween (a C L) (b C L),
    kernel n ((Real.log p - L) / δ C L) * (Real.log p / Real.sqrt p)
noncomputable def mangoldtPopulation (n : ℕ) (C L : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (⌊b C L⌋₊ + 1)).filter
      (fun k : ℕ => a C L < (k : ℝ) ∧ (k : ℝ) < b C L),
    kernel n ((Real.log (k : ℝ) - L) / δ C L) *
      ((ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt (k : ℝ))
noncomputable def transform (n : ℕ) (y : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, kernel n u * Real.cos (y * u)
noncomputable def zeroPacket (n : ℕ) (C L : ℝ) (ρ : PsiSmoothing.Zero) : ℂ :=
  Complex.exp (Complex.I * ((ρ : ℂ).im * L : ℝ)) *
    (δ C L * transform n (δ C L * (ρ : ℂ).im) : ℝ) *
    (IEANTN.zetaOrder ρ : ℂ)
noncomputable def zeroTerm (n : ℕ) (C L : ℝ) : ℂ :=
  ∑' ρ : PsiSmoothing.Zero, zeroPacket n C L ρ
noncomputable def mainTerm (n : ℕ) (C L : ℝ) : ℝ :=
  D C L * ∫ u in (-1 : ℝ)..1, kernel n u * Real.cosh (δ C L * u / 2)
noncomputable def trivialCost (n : ℕ) (C L : ℝ) : ℝ :=
  ∫ t in a C L..b C L, kernel n ((Real.log t - L) / δ C L) /
    (Real.sqrt t * t * (t ^ 2 - 1))
noncomputable def countCoefficient (n : ℕ) (A C : ℝ) : ℝ := mass n * C / 2 - A / 2

def ExplicitFormula (n : ℕ) (C : ℝ) : Prop := RiemannHypothesis →
  ∀ L : ℝ, 24 ≤ L → Summable (zeroPacket n C L) ∧
    mangoldtPopulation n C L = mainTerm n C L - (zeroTerm n C L).re - trivialCost n C L

def ZeroEstimate (n : ℕ) (C A B R : ℝ) : Prop := RiemannHypothesis →
  ∀ L : ℝ, 24 ≤ L → ‖zeroTerm n C L‖ ≤
    A * (L / 2 - Real.log (2 * Real.pi * D C L)) + B + R

def PrimePowerCost (n : ℕ) (C P : ℝ) : Prop :=
  ∀ L : ℝ, 24 ≤ L → mangoldtPopulation n C L - population n C L ≤ P

def TrivialCost (n : ℕ) (C T : ℝ) : Prop :=
  ∀ L : ℝ, 24 ≤ L → trivialCost n C L ≤ T

/-- Exact scalar geometry and logarithmic margin; contains no prime-count goal. -/
def ScalarGeometry (n : ℕ) (C A B R P T η : ℝ) : Prop :=
  ∀ L : ℝ, 24 ≤ L → 0 < a C L ∧ 2 ≤ Real.log (a C L) ∧
    a C L ≤ b C L ∧ L - δ C L = Real.log (a C L) ∧ 0 ≤ δ C L ∧
    0 ≤ D C L ∧ 0 ≤ countCoefficient n A C ∧ 0 < η ∧
    η < A * Real.log (2 * Real.pi * D C L) - mass n - B - R - P - T

def ForwardCoverage (C : ℝ) : Prop := ∀ u : ℝ, Real.exp 24 ≤ u →
  ∃ L : ℝ, 24 ≤ L ∧ a C L = u ∧
    b C L ≤ u + C * Real.sqrt u * Real.log u

theorem kernel_continuous (n : ℕ) : Continuous (kernel n) := by
  unfold kernel
  fun_prop

theorem kernel_nonneg (n : ℕ) (u : ℝ) : 0 ≤ kernel n u := le_max_left _ _

theorem kernel_le_one (n : ℕ) (u : ℝ) : kernel n u ≤ 1 := by
  have hpow : 0 ≤ u ^ (2 * n) := by rw [Nat.mul_comm, pow_mul]; positivity
  unfold kernel
  exact max_le (by norm_num) (by linarith)

theorem kernel_eq_raw (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    kernel n u = 1 - u ^ (2 * n) := by
  have hp : |u| ^ (2 * n) ≤ 1 := pow_le_one₀ (abs_nonneg u) (abs_le.mpr hu)
  have hule : u ^ (2 * n) ≤ 1 :=
    (le_abs_self _).trans (by simpa only [abs_pow] using hp)
  unfold kernel
  exact max_eq_right (by linarith)

theorem kernel_mass (n : ℕ) : (∫ u in (-1 : ℝ)..1, kernel n u) = mass n := by
  have heq : (∫ u in (-1 : ℝ)..1, kernel n u) =
      ∫ u in (-1 : ℝ)..1, 1 - u ^ (2 * n) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
    exact kernel_eq_raw n hu
  rw [heq, intervalIntegral.integral_sub]
  · rw [integral_pow]
    unfold mass
    simp only [one_pow, pow_add, pow_mul, neg_one_sq, one_mul, one_pow,
      pow_one, mul_neg, mul_one]
    norm_num
    push_cast
    field_simp
    ring
  · exact intervalIntegrable_const
  · exact (continuous_id.pow (2 * n)).intervalIntegrable (-1) 1

theorem mainTerm_lower (n : ℕ) {C L : ℝ} (hd : 0 ≤ D C L) :
    mass n * D C L ≤ mainTerm n C L := by
  have hc : Continuous (fun u : ℝ => kernel n u * Real.cosh (δ C L * u / 2)) := by
    exact (kernel_continuous n).mul (Real.continuous_cosh.comp (by fun_prop))
  have hi : (∫ u in (-1 : ℝ)..1, kernel n u) ≤
      ∫ u in (-1 : ℝ)..1, kernel n u * Real.cosh (δ C L * u / 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((kernel_continuous n).intervalIntegrable (-1) 1) (hc.intervalIntegrable (-1) 1)
    intro u hu
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.one_le_cosh _) (kernel_nonneg n u)
  rw [kernel_mass] at hi
  unfold mainTerm
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi hd

theorem population_le_count (n : ℕ) {C L : ℝ} (ha : 0 < a C L)
    (hla : 2 ≤ Real.log (a C L)) : population n C L ≤
      ((QuarticWindow.primesBetween (a C L) (b C L)).card : ℝ) *
        (Real.log (a C L) / Real.sqrt (a C L)) := by
  unfold population
  calc
    ∑ p ∈ QuarticWindow.primesBetween (a C L) (b C L),
        kernel n ((Real.log p - L) / δ C L) * (Real.log p / Real.sqrt p) ≤
        ∑ _p ∈ QuarticWindow.primesBetween (a C L) (b C L),
          Real.log (a C L) / Real.sqrt (a C L) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpa := (Finset.mem_filter.mp hp).2.1
      have hlogp : 0 ≤ Real.log p := (by linarith : 0 ≤ Real.log (a C L)).trans
        (Real.log_le_log ha hpa.le)
      calc
        kernel n ((Real.log p - L) / δ C L) * (Real.log p / Real.sqrt p) ≤
            Real.log p / Real.sqrt p := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (kernel_le_one n _)
            (div_nonneg hlogp (Real.sqrt_nonneg _))
        _ ≤ _ := QuarticWindow.log_div_sqrt_antitone ha hpa.le hla
    _ = _ := by simp

/-- Whole real-ray actual prime-count frontier, from decomposed analytic contracts.
For n=4,A=1.822 it has coefficient (8/9)C-.911. -/
theorem prime_count_from_kernel (n : ℕ) (C A B R P T η : ℝ)
    (rh : RiemannHypothesis) (hef : ExplicitFormula n C)
    (hz : ZeroEstimate n C A B R) (hpp : PrimePowerCost n C P)
    (ht : TrivialCost n C T) (hg : ScalarGeometry n C A B R P T η)
    (hc : ForwardCoverage C) :
    ∀ u : ℝ, Real.exp 24 ≤ u →
      (countCoefficient n A C + η / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + C * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u := by
  intro u hu
  obtain ⟨L,hL,hcenter,hwidth⟩ := hc u hu
  obtain ⟨ha,hla,hab,hlog,hδ,hd,hlam,hη,hmargin⟩ := hg L hL
  have heq := (hef rh L hL).2
  have hz' := (le_abs_self (zeroTerm n C L).re).trans
    ((Complex.abs_re_le_norm _).trans (hz rh L hL))
  have hm := mainTerm_lower n hd
  have hp := hpp L hL
  have ht' := ht L hL
  have hpop : countCoefficient n A C * L + η < population n C L := by
    unfold D at hm
    unfold countCoefficient
    nlinarith
  have hbound := population_le_count n ha hla
  have hloga : 0 < Real.log (a C L) := by linarith
  have hsa : 0 < Real.sqrt (a C L) := Real.sqrt_pos.mpr ha
  have hstrict : countCoefficient n A C * Real.log (a C L) + η <
      ((QuarticWindow.primesBetween (a C L) (b C L)).card : ℝ) *
        (Real.log (a C L) / Real.sqrt (a C L)) := by
    have hh : countCoefficient n A C * Real.log (a C L) ≤
        countCoefficient n A C * L := mul_le_mul_of_nonneg_left (by linarith) hlam
    linarith
  have hdiv := (div_lt_iff₀ (div_pos hloga hsa)).mpr hstrict
  have hfield : (countCoefficient n A C * Real.log (a C L) + η) /
      (Real.log (a C L) / Real.sqrt (a C L)) =
      (countCoefficient n A C + η / Real.log (a C L)) * Real.sqrt (a C L) := by
    field_simp
    <;> ring
  rw [hfield] at hdiv
  have hcard := QuarticWindow.count_le_primeCounting_difference ha.le hab
  have hmono : QuarticWindow.primeCounting (b C L) ≤
      QuarticWindow.primeCounting (u + C * Real.sqrt u * Real.log u) := by
    unfold QuarticWindow.primeCounting
    exact_mod_cast Nat.monotone_primeCounting (Nat.floor_le_floor hwidth)
  rw [hcenter] at hcard hdiv
  linarith

#print axioms prime_count_from_kernel
end EvenKernel
