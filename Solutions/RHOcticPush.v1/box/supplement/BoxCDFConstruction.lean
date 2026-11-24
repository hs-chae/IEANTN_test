/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import BoxImproved
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
namespace RHOcticPush.BoxCDF
open Real Set Finset MeasureTheory IEANTN
set_option maxHeartbeats 0

noncomputable def endpoint (s L u : ℝ) : ℝ :=
  Real.exp L*Real.exp ((s+u)*IEANTN.RHSmoothing.delta L)
noncomputable def cutoff (s L t : ℝ) : ℝ :=
  (1/2:ℝ)*∫ u in (-1:ℝ)..1, if t≤endpoint s L u then (1:ℝ) else 0

lemma cutoff_zero (s L : ℝ) : cutoff s L 0=1 := by
  have h : (fun u : ℝ => if (0:ℝ)≤endpoint s L u then (1:ℝ)else 0)=fun _=>1 := by
    funext u
    rw [if_pos (by unfold endpoint; positivity)]
  rw [cutoff,h]
  norm_num

/-- The actual cumulative box weight is outside Green's support fragment.
This is a domain obstruction for a direct source application, not a claim that
an admissible cutoff/mollifier construction is mathematically impossible. -/
theorem raw_cdf_not_Green_supported (s L X : ℝ) :
    ¬Function.support (fun t : ℝ => cutoff s L (X*t)) ⊆ Ici 1 := by
  intro h
  have hz : (0:ℝ)∈Function.support (fun t : ℝ => cutoff s L (X*t)) := by
    simp only [Function.mem_support,mul_zero,cutoff_zero,ne_eq,one_ne_zero,not_false_eq_true]
  have := h hz
  norm_num at this

lemma psi_finite_cutoff {x B : ℝ} (hx : 0≤x) (hB : x≤B) :
    Chebyshev.psi x=∑ n ∈ Finset.Icc 0 ⌊B⌋₊,
      (ArithmeticFunction.vonMangoldt n:ℝ)*(if (n:ℝ)≤x then 1 else 0) := by
  have hf : (Finset.Icc 0 ⌊B⌋₊).filter (fun n : ℕ => (n:ℝ)≤x)=Finset.Icc 0 ⌊x⌋₊ := by
    ext n
    simp only [mem_filter,Finset.mem_Icc,Nat.zero_le,true_and]
    constructor
    · intro hn
      exact (Nat.le_floor_iff hx).mpr hn.2
    · intro hn
      exact ⟨hn.trans (Nat.floor_mono hB),(Nat.le_floor_iff hx).mp hn⟩
  rw [Chebyshev.psi_eq_sum_Icc,←hf,sum_filter]
  apply sum_congr rfl
  intro n hn
  split_ifs <;> simp

lemma endpoint_monotone {L : ℝ} (hL : 0≤L) (s : ℝ) : Monotone (endpoint s L) := by
  have hd : 0≤IEANTN.RHSmoothing.delta L := by unfold IEANTN.RHSmoothing.delta; positivity
  intro u v huv
  apply mul_le_mul_of_nonneg_left _ (exp_pos L).le
  exact exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hd)

lemma cutoff_below {L : ℝ} (hL : 0≤L) (s : ℝ) {t : ℝ}
    (ht : t≤endpoint s L (-1)) : cutoff s L t=1 := by
  have he : (∫ u in (-1:ℝ)..1, if t≤endpoint s L u then (1:ℝ) else 0)=
      ∫ _u in (-1:ℝ)..1, (1:ℝ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (-1:ℝ)≤1)] at hu
    exact if_pos (ht.trans (endpoint_monotone hL s hu.1))
  rw [cutoff,he]
  norm_num

/-- The support obstruction occurs at a genuinely POSITIVE argument below1;
it is not an artifact of a totalized value or a convention at the origin. -/
theorem raw_cdf_positive_support_obstruction {L X : ℝ} (hL : 0≤L) (hX : 0<X)
    (s : ℝ) : ∃ t : ℝ, 0<t ∧ t<1 ∧ cutoff s L (X*t)=1 := by
  let t := min (1/2:ℝ) (endpoint s L (-1)/(2*X))
  have ha : 0<endpoint s L (-1) := by unfold endpoint; positivity
  have ht0 : 0<t := lt_min (by norm_num) (div_pos ha (by positivity))
  have ht1 : t<1 := (min_le_left _ _).trans_lt (by norm_num)
  have htm := (le_div_iff₀ (by positivity : (0:ℝ)<2*X)).mp
    (min_le_right (1/2:ℝ) (endpoint s L (-1)/(2*X)))
  refine ⟨t,ht0,ht1,cutoff_below hL s ?_⟩
  dsimp [t] at *
  nlinarith

lemma indicator_integrable {L : ℝ} (hL : 0≤L) (s t : ℝ) :
    IntervalIntegrable (fun u : ℝ => if t≤endpoint s L u then (1:ℝ) else 0)
      volume (-1) 1 := by
  apply Monotone.intervalIntegrable
  intro u v huv
  dsimp only
  by_cases hu : t≤endpoint s L u
  · rw [if_pos hu,if_pos (hu.trans (endpoint_monotone hL s huv))]
  · rw [if_neg hu]
    split_ifs <;> norm_num

/-- Exact finite Mangoldt population of the ACTUAL averaged psi observable.
No analytic explicit formula, RH, or newly assumed source predicate is used. -/
theorem actual_box_population {L : ℝ} (hL : 35≤L) (s : ℝ) :
    IEANTN.RHSmoothing.average IEANTN.RHSmoothing.box s L =
      ∑ n ∈ Finset.Icc 0 ⌊endpoint s L 1⌋₊,
        (ArithmeticFunction.vonMangoldt n:ℝ)*cutoff s L n := by
  have hL0 : 0≤L := by linarith
  have hi (n : ℕ) : IntervalIntegrable
      (fun u : ℝ => (ArithmeticFunction.vonMangoldt n:ℝ)*
        (if (n:ℝ)≤endpoint s L u then 1 else 0)) volume (-1) 1 :=
    (indicator_integrable hL0 s n).const_mul _
  unfold IEANTN.RHSmoothing.average IEANTN.RHSmoothing.box
  rw [intervalIntegral.integral_const_mul]
  have he : (∫ u in (-1:ℝ)..1, Chebyshev.psi (endpoint s L u))=
      ∫ u in (-1:ℝ)..1, ∑ n ∈ Finset.Icc 0 ⌊endpoint s L 1⌋₊,
        (ArithmeticFunction.vonMangoldt n:ℝ)*(if (n:ℝ)≤endpoint s L u then 1 else 0) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (-1:ℝ)≤1)] at hu
    exact psi_finite_cutoff (by unfold endpoint; positivity)
      (endpoint_monotone hL0 s hu.2)
  change (1/2:ℝ)*(∫ u in (-1:ℝ)..1,Chebyshev.psi (endpoint s L u))=_
  rw [he,intervalIntegral.integral_finset_sum]
  · rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_const_mul,cutoff]
    ring
  · intro n hn
    exact hi n

open Complex

/-- The normalization constant is already an unconditional Mathlib result,
adapted from CH2Section9Limit.logDeriv_zeta_zero; it is not a new source premise. -/
lemma box_log_constant : deriv riemannZeta 0/riemannZeta 0=
    ((Real.log (2*Real.pi):ℝ):ℂ) := by
  rw [deriv_riemannZeta_zero,riemannZeta_zero,
    show ((2:ℂ)*(Real.pi:ℂ))=((2*Real.pi:ℝ):ℂ) by push_cast; ring,
    ←Complex.ofReal_log (by positivity)]
  push_cast
  field_simp

lemma averaged_log_constant : (∫ u in (-1:ℝ)..1,
    IEANTN.RHSmoothing.box u*Real.log (2*Real.pi))=Real.log (2*Real.pi) := by
  norm_num [IEANTN.RHSmoothing.box]
  ring

#print axioms raw_cdf_positive_support_obstruction
#print axioms box_log_constant
#print axioms raw_cdf_not_Green_supported
#print axioms actual_box_population
end RHOcticPush.BoxCDF
