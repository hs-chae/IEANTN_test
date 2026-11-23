/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib
import ZeroCountIntegral

/-! Source-correct interface to Brent--Platt--Trudgian, *The mean square of the
error term in the prime number theorem*, JNT 238 (2022), Corollary 1, p.743
(arXiv:2008.06140v1, PDF p.4). Its published input is NOT proved here: the
consequences below are ordinary conditional Lean mathematics. The local exact
predicate retains the source threshold T >= 2 pi and the closed counting convention;
it does not silently reuse HasRvMBound's different threshold/count definition. -/
namespace RHLimit.BPTZeroCount
open Real Set MeasureTheory
set_option maxHeartbeats 0

/-- Published BPT Corollary 1, explicitly retained as a literature input. -/
def PublishedBound : Prop :=
  ∀ T : ℝ, 2 * Real.pi ≤ T →
    |ZeroCount.v1.zetaNClosed T - ZeroCount.v1.rvmMain T| ≤ (7 / 25) * Real.log T

/-- The actual closed count is a nonnegative integer; no numerical zero table is used. -/
theorem count_eq_nat {T : ℝ} (_hT : 0 ≤ T) :
    ∃ n : ℕ, ZeroCount.v1.zetaNClosed T = (n : ℝ) := by
  classical
  let S := (CH2Section7Z.finite_zeros_Ioc (a := 0) (b := T) le_rfl).toFinset
  let k : ℤ := ∑ ρ ∈ S, IEANTN.zetaOrder ρ
  have hk : 0 ≤ k := by
    apply Finset.sum_nonneg
    intro ρ hρ
    exact_mod_cast CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self
      ((Set.Finite.mem_toFinset _).mp hρ)
  have he : ZeroCount.v1.zetaNClosed T = (k : ℝ) := by
    rw [ZeroCount.v1.zetaNClosed, CH2Section7Z.zetaZeroesSum_eq_sum
      (CH2Section7Z.finite_zeros_Ioc (a := 0) (b := T) le_rfl)]
    simp only [one_mul, k, Int.cast_sum, S]
  refine ⟨k.toNat, ?_⟩
  rw [he]
  exact_mod_cast (Int.toNat_of_nonneg hk).symm

lemma log_twelve_lt : Real.log 12 < (5 : ℝ) / 2 := by
  have h2 : Real.log 2 < (7 : ℝ) / 10 := by linarith [Real.log_two_lt_d9]
  have h3 : Real.log 3 < (11 : ℝ) / 10 := by linarith [Real.log_three_lt_d9]
  have he : Real.log 12 = Real.log 3 + 2 * Real.log 2 := by
    calc Real.log 12 = Real.log ((3 : ℝ) * 2 ^ 2) := by norm_num
         _ = Real.log 3 + 2 * Real.log 2 := by
           rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ)^2 ≠ 0),
             Real.log_pow]
           norm_num
  linarith

/-- BPT's precise constant proves the cutoff12 used by the written zero estimates.
The weaker canonical CH/Rosser error bound alone is not substituted for this input. -/
theorem count_twelve_zero (h : PublishedBound) : ZeroCount.v1.zetaNClosed 12 = 0 := by
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hp4 : Real.pi < 63 / 20 := by linarith [Real.pi_lt_d2]
  have hdom : 2 * Real.pi ≤ 12 := by linarith
  have hb := (le_abs_self _).trans (h 12 hdom)
  let r : ℝ := 12 / (2 * Real.pi)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrlo : (19 : ℝ) / 10 ≤ r := by
    dsimp [r]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith
  have hrhi : r ≤ 2 := by
    dsimp [r]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    linarith
  have hlog : Real.log r ≤ (347 : ℝ) / 500 := by
    exact (Real.log_le_log (by linarith) hrhi).trans (by linarith [Real.log_two_lt_d9])
  have hm : ZeroCount.v1.rvmMain 12 ≤ (367 : ℝ) / 1250 := by
    change r * Real.log r - r + 7 / 8 ≤ _
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hlog)]
  have hn : ZeroCount.v1.zetaNClosed 12 < 1 := by
    nlinarith [log_twelve_lt]
  obtain ⟨n, he⟩ := count_eq_nat (T := 12) (by norm_num)
  have hn0 : n = 0 := by
    rw [he] at hn
    have : n < 1 := by exact_mod_cast hn
    omega
  simpa [hn0] using he

noncomputable def remainder (T : ℝ) : ℝ :=
  ZeroCount.v1.zetaNClosed T - ZeroCount.v1.rvmMain T

noncomputable def density (T : ℝ) : ℝ := Real.log (T / (2 * Real.pi)) / (2 * Real.pi)

lemma main_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt ZeroCount.v1.rvmMain (density t) t := by
  unfold ZeroCount.v1.rvmMain
  have h2 := (hasDerivAt_id t).div_const (2 * Real.pi)
  have hlog := (Real.hasDerivAt_log
    (by positivity : t / (2 * Real.pi) ≠ 0)).comp t h2
  apply (((h2.mul hlog).sub h2).add_const (7 / 8 : ℝ)).congr_deriv
  dsimp [density]
  field_simp
  ring

/-- Exact finite weighted RvM remainder, before any absolute values or tail limits. -/
theorem finite_remainder {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {φ φ' : ℝ → ℝ} (hd : ∀ t ∈ uIcc a b, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (uIcc a b)) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ φ ρ.im) -
      (∫ t in a..b, φ t * density t) =
      φ b * remainder b - φ a * remainder a - ∫ t in a..b, φ' t * remainder t := by
  have hp (t : ℝ) (ht : t ∈ uIcc a b) : 0 < t := by
    rw [uIcc_of_le hab] at ht
    linarith [ht.1]
  have hm : ContinuousOn ZeroCount.v1.rvmMain (uIcc a b) :=
    fun t ht => (main_hasDerivAt (hp t ht)).continuousAt.continuousWithinAt
  have hdc : ContinuousOn density (uIcc a b) := by
    intro t ht
    have ht0 := hp t ht
    have hne : t / (2 * Real.pi) ≠ 0 := by positivity
    have hr : ContinuousAt (fun x : ℝ => x / (2 * Real.pi)) t :=
      continuousAt_id.div_const (2 * Real.pi)
    have hl : ContinuousAt (fun x : ℝ => Real.log (x / (2 * Real.pi))) t :=
      hr.log hne
    exact (hl.div_const (2 * Real.pi)).continuousWithinAt
  have hn := RHContinuation.ZeroCountIntegral.count_integrable (by linarith : 0 ≤ a) hab
  have hir : IntervalIntegrable (fun t => φ' t * remainder t) volume a b :=
    (hn.sub hm.intervalIntegrable).continuousOn_mul hc
  have him : IntervalIntegrable
      (fun t => (ZeroCount.v1.rvmMain t - ZeroCount.v1.zetaNClosed a) * φ' t) volume a b :=
    ((hm.sub continuousOn_const).mul hc).intervalIntegrable
  have hs : (∫ t in a..b, φ' t *
      (ZeroCount.v1.zetaNClosed t - ZeroCount.v1.zetaNClosed a)) =
      (∫ t in a..b, φ' t * remainder t) +
      (∫ t in a..b, (ZeroCount.v1.rvmMain t - ZeroCount.v1.zetaNClosed a) * φ' t) := by
    rw [← intervalIntegral.integral_add hir him]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [remainder]
    ring
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => (main_hasDerivAt (hp t ht)).sub_const (ZeroCount.v1.zetaNClosed a))
    hd hdc.intervalIntegrable hc.intervalIntegrable
  have hswap : (∫ t in a..b, density t * φ t) = ∫ t in a..b, φ t * density t := by
    simp only [mul_comm]
  rw [RHContinuation.ZeroAbel.exact_finite ha hab hd hc, hs, hibp, hswap]
  dsimp [remainder]
  ring

/-- A source-correct finite BPT bound for every C1 real test function.
The absolute Fourier function still requires a smooth-approximation/limit bridge;
this theorem does not assert that missing bridge or any numerical moment cap. -/
theorem finite_remainder_bound (h : PublishedBound) {a b : ℝ}
    (ha : 2 * Real.pi ≤ a) (hab : a ≤ b) {φ φ' : ℝ → ℝ}
    (hd : ∀ t ∈ uIcc a b, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (uIcc a b)) :
    |IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ φ ρ.im) -
      (∫ t in a..b, φ t * density t)| ≤
      (7 / 25) * (|φ b| * Real.log b + |φ a| * Real.log a +
        ∫ t in a..b, |φ' t| * Real.log t) := by
  have ha1 : 1 ≤ a := by linarith [Real.pi_gt_three]
  have hp (t : ℝ) (ht : t ∈ uIcc a b) : 0 < t := by
    rw [uIcc_of_le hab] at ht
    linarith [ht.1]
  have hlog : ContinuousOn Real.log (uIcc a b) :=
    fun t ht => (Real.continuousAt_log (hp t ht).ne').continuousWithinAt
  have hm : ContinuousOn ZeroCount.v1.rvmMain (uIcc a b) :=
    fun t ht => (main_hasDerivAt (hp t ht)).continuousAt.continuousWithinAt
  have hn := RHContinuation.ZeroCountIntegral.count_integrable (by linarith : 0 ≤ a) hab
  have hir : IntervalIntegrable (fun t => φ' t * remainder t) volume a b :=
    (hn.sub hm.intervalIntegrable).continuousOn_mul hc
  have hj : IntervalIntegrable (fun t => (7 / 25) * (|φ' t| * Real.log t)) volume a b :=
    ((hc.abs.mul hlog).const_mul _).intervalIntegrable
  have hI : |∫ t in a..b, φ' t * remainder t| ≤
      (7 / 25) * ∫ t in a..b, |φ' t| * Real.log t := by
    calc _ ≤ ∫ t in a..b, |φ' t * remainder t| :=
           intervalIntegral.abs_integral_le_integral_abs hab
         _ ≤ ∫ t in a..b, (7 / 25) * (|φ' t| * Real.log t) := by
           apply intervalIntegral.integral_mono_on hab hir.abs hj
           intro t ht
           have hbound := h t (ha.trans ht.1)
           change |remainder t| ≤ _ at hbound
           rw [abs_mul]
           nlinarith [mul_le_mul_of_nonneg_left hbound (abs_nonneg (φ' t))]
         _ = _ := intervalIntegral.integral_const_mul _ _
  rw [finite_remainder ha1 hab hd hc]
  calc _ ≤ |φ b| * |remainder b| + |φ a| * |remainder a| +
      |∫ t in a..b, φ' t * remainder t| := by
        calc _ ≤ |φ b * remainder b - φ a * remainder a| +
            |∫ t in a..b, φ' t * remainder t| := abs_sub _ _
             _ ≤ (|φ b * remainder b| + |φ a * remainder a|) +
                 |∫ t in a..b, φ' t * remainder t| := by gcongr; exact abs_sub _ _
             _ = _ := by rw [abs_mul, abs_mul]
       _ ≤ |φ b| * ((7 / 25) * Real.log b) + |φ a| * ((7 / 25) * Real.log a) +
           (7 / 25) * (∫ t in a..b, |φ' t| * Real.log t) := by
             apply add_le_add _ hI
             exact add_le_add (mul_le_mul_of_nonneg_left (h b (ha.trans hab)) (abs_nonneg _))
               (mul_le_mul_of_nonneg_left (h a ha) (abs_nonneg _))
       _ = _ := by ring

#print axioms count_eq_nat
#print axioms count_twelve_zero
#print axioms finite_remainder
#print axioms finite_remainder_bound
end RHLimit.BPTZeroCount
