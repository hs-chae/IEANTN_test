/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CLogNativeRows
import PsiClosedElementary
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.PSeries
import EulerLower

/-! Source-first C logarithms genuinely consumed by the new absolute box moment
and the actual Chebyshev.psi theorem. The finite numerical aggregation is a
kernel proof. Analytic Mellin/constant identities remain explicit, decomposed
premises; neither the actual moment bound nor the desired PNT bound is assumed.
-/
namespace CLogMoment
open Real Finset PsiSmoothing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

def upper (n : ℕ) : ℚ := (CLogNativeRows.words[n]?.getD 0 : ℚ) / 2 ^ 40
def lower (n : ℕ) : ℚ := upper n - 1 / 2 ^ 30
def samples : Finset ℕ := Icc 2 128
def sLower : ℚ := (∑ n ∈ samples, lower n / n) - upper 128 ^ 2 / 2
def qLower : ℚ := ∑ n ∈ samples, lower n / ((n : ℚ) * (4 * n ^ 2 - 1))
def gammaLower : ℚ := harmonic 1024 - 10 * upper 2 - 1 / 2048
def aUpper : ℚ := 1 - gammaLower - lower 2
def finalUpper : ℚ := -sLower + upper 128 / 256 - qLower +
  aUpper * lower 2 - aUpper ^ 2 / 2 + 1 / 2 + (31416 / 10000) ^ 2 / 24

noncomputable def stieltjesSeq (n : ℕ) : ℝ :=
  (∑ k ∈ Icc 2 n, Real.log k / k) - (Real.log n) ^ 2 / 2
noncomputable def gamma1 : ℝ := Filter.limUnder Filter.atTop stieltjesSeq
noncomputable def qTerm (n : ℕ) : ℝ :=
  if n < 2 then 0 else Real.log n / ((n : ℝ) * (4 * n ^ 2 - 1))
noncomputable def q : ℝ := ∑' n : ℕ, qTerm n
noncomputable def a : ℝ := 1 - Real.eulerMascheroniConstant - Real.log 2

/-- Elementary accelerated harmonic bound, from the trapezoid comparison for1/t.
Its written derivation and the exact Mellin/constant limits are in BOX_MELLIN_EXACT.md. -/
def EulerHarmonicLower : Prop :=
  (harmonic 1024 : ℝ) - 10 * Real.log 2 - 1 / 2048 ≤ Real.eulerMascheroniConstant
/-- Convex trapezoid bound for log(t)/t on t≥128; gamma1 is the actual limit,
not an independent numeric parameter. -/
def StieltjesTrapezoidLower : Prop :=
  stieltjesSeq 128 - Real.log 128 / 256 ≤ gamma1
/-- Exact coefficient extraction from the regularized absolute Mellin transform. -/
def MellinMomentIdentity : Prop :=
  J box 1 = -gamma1 - q + a * Real.log 2 - a ^ 2 / 2 + 1 / 2 + Real.pi ^ 2 / 24

/-- These enclosures consume full execution proofs for the actual C source. -/
theorem sample_interval {n : ℕ} (hn : 2 ≤ n) (hN : n ≤ 128) :
    (lower n : ℝ) ≤ Real.log n ∧ Real.log n ≤ (upper n : ℝ) := by
  have h := CLogNativeRows.source_execution_and_interval hn hN
  constructor
  · simpa only [lower, upper, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using h.2.1
  · simpa only [upper, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]
      using h.2.2

theorem exact_scalar_checks : finalUpper < 567 / 800 ∧ aUpper < 0 ∧ 0 ≤ lower 2 := by
  decide +kernel

theorem qTerm_nonneg (n : ℕ) : 0 ≤ qTerm n := by
  unfold qTerm
  split_ifs with hn
  · rfl
  · have hn2 : 2 ≤ n := by omega
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    apply div_nonneg (Real.log_nonneg (by linarith))
    have hh : 0 ≤ (n : ℝ) := by positivity
    nlinarith [sq_nonneg (n : ℝ)]

/-- The omitted logarithmic series is genuinely summable, by a p-series bound. -/
theorem qTerm_summable : Summable qTerm := by
  apply Summable.of_nonneg_of_le qTerm_nonneg
    (show ∀ n : ℕ, qTerm n ≤ 1 / (n : ℝ) ^ 2 from ?_)
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  intro n
  unfold qTerm
  split_ifs with hn
  · positivity
  · have hn2 : 2 ≤ n := by omega
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hn0 : (0 : ℝ) < n := by linarith
    have den : 0 < (n : ℝ) * (4 * n ^ 2 - 1) := by
      apply mul_pos hn0
      nlinarith [sq_nonneg (n : ℝ)]
    apply (div_le_div_iff₀ den (sq_pos_of_pos hn0)).mpr
    have hl := Real.log_le_sub_one_of_pos hn0
    have hmul := mul_le_mul_of_nonneg_right hl (sq_nonneg (n : ℝ))
    have hp : 0 ≤ (n : ℝ) * (3 * n ^ 2 + n - 1) := by
      apply mul_nonneg hn0.le
      nlinarith [sq_nonneg (n : ℝ)]
    nlinarith

theorem source_moment_bound (hg : EulerHarmonicLower)
    (hs : StieltjesTrapezoidLower) (hm : MellinMomentIdentity)
    (hq : Summable qTerm) : J box 1 < 567 / 800 := by
  have interval128 := sample_interval (n := 128) (by norm_num) (by norm_num)
  have interval2 := sample_interval (n := 2) (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at interval128 interval2
  have num := exact_scalar_checks
  have hsum : (∑ n ∈ samples, (lower n : ℝ) / n) ≤
      ∑ n ∈ samples, Real.log n / n := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact div_le_div_of_nonneg_right (sample_interval hn'.1 hn'.2).1 (by positivity)
  have sCast : (sLower : ℝ) = (∑ n ∈ samples, (lower n : ℝ) / n) -
      (upper 128 : ℝ) ^ 2 / 2 := by simp [sLower]
  have sn : (sLower : ℝ) ≤ stieltjesSeq 128 := by
    rw [sCast]
    unfold stieltjesSeq
    have lnonneg : 0 ≤ Real.log (128 : ℝ) := Real.log_nonneg (by norm_num)
    have usq : (Real.log (128 : ℝ)) ^ 2 ≤ (upper 128 : ℝ) ^ 2 := by
      nlinarith [interval128.2]
    change _ ≤ (∑ n ∈ samples, Real.log n / n) - Real.log 128 ^ 2 / 2
    linarith
  have st : (sLower : ℝ) - (upper 128 : ℝ) / 256 ≤ gamma1 := by
    unfold StieltjesTrapezoidLower at hs
    linarith [interval128.2]
  have qsum : (qLower : ℝ) ≤ ∑ n ∈ samples, qTerm n := by
    simp only [qLower, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]
    apply Finset.sum_le_sum
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn'.1
    have hl := (sample_interval hn'.1 hn'.2).1
    have hh : ¬n < 2 := by omega
    simp only [qTerm, hh, ↓reduceIte]
    apply div_le_div_of_nonneg_right hl
    nlinarith [sq_nonneg (n : ℝ)]
  have qfull : (qLower : ℝ) ≤ q := by
    exact qsum.trans (hq.sum_le_tsum samples (fun n _ => qTerm_nonneg n))
  have g : (gammaLower : ℝ) ≤ Real.eulerMascheroniConstant := by
    unfold EulerHarmonicLower at hg
    have hgc : (gammaLower : ℝ) = (harmonic 1024 : ℝ) - 10 * (upper 2 : ℝ) -
        1 / 2048 := by simp [gammaLower]
    rw [hgc]
    linarith [interval2.2]
  have aBound : a ≤ (aUpper : ℝ) := by
    have ha : (aUpper : ℝ) = 1 - (gammaLower : ℝ) - (lower 2 : ℝ) := by simp [aUpper]
    rw [ha]
    unfold a
    linarith [interval2.1]
  have aneg : (aUpper : ℝ) < 0 := by exact_mod_cast num.2.1
  have lpos : (0 : ℝ) ≤ (lower 2 : ℝ) := by exact_mod_cast num.2.2
  have prod : a * Real.log 2 ≤ (aUpper : ℝ) * (lower 2 : ℝ) := by
    have x := mul_le_mul_of_nonpos_left interval2.1 (aBound.trans aneg.le)
    have y := mul_le_mul_of_nonneg_right aBound lpos
    linarith
  have asq : (aUpper : ℝ) ^ 2 ≤ a ^ 2 := by nlinarith
  have psq : Real.pi ^ 2 ≤ (31416 / 10000 : ℝ) ^ 2 := by
    have hpi := Real.pi_lt_d4
    have hp := Real.pi_pos
    nlinarith
  have hfc : (finalUpper : ℝ) = -(sLower : ℝ) + (upper 128 : ℝ) / 256 -
      (qLower : ℝ) + (aUpper : ℝ) * (lower 2 : ℝ) - (aUpper : ℝ) ^ 2 / 2 +
      1 / 2 + (31416 / 10000 : ℝ) ^ 2 / 24 := by simp [finalUpper]
  have hbound : J box 1 ≤ (finalUpper : ℝ) := by
    unfold MellinMomentIdentity at hm
    rw [hm, hfc]
    linarith
  have hf : (finalUpper : ℝ) < ((567 / 800 : ℚ) : ℝ) := Rat.cast_lt.mpr num.1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hf
  exact hbound.trans_lt hf

/-- Numerical source leaf, elementary Euler bound, and series summability are closed.
Only the two exact analytic Mellin/constant contracts are supplied here. -/
theorem source_moment_bound_closed (hs : StieltjesTrapezoidLower)
    (hm : MellinMomentIdentity) : J box 1 < 567 / 800 :=
  source_moment_bound EulerLower.harmonic1024_lower hs hm qTerm_summable

/-- Actual C source→proved executions and log enclosures→kernel aggregation→
Mellin moment→actual full-real-ray Chebyshev.psi, with remaining analytic inputs
fully visible. This does not assert that the analytic identities were formalized. -/
theorem psi_fast (rh : RiemannHypothesis)
    (hef : AveragedExplicitFormula box) (hz : ZeroDensityMomentEstimate box)
    (h0 : J box 0 = Real.log 2) (hg : EulerHarmonicLower)
    (hs : StieltjesTrapezoidLower) (hm : MellinMomentIdentity)
    (hq : Summable qTerm) :
    ∀ x : ℝ, Real.exp 35 ≤ x → |Chebyshev.psi x - x| ≤
      Real.sqrt x * envelope (Real.log 2) (567 / 800) (Real.log x) :=
  RHContinuation.Parabolic.psi_fast rh hef hz h0 (source_moment_bound hg hs hm hq).le

#print axioms source_moment_bound
#print axioms psi_fast
end CLogMoment
