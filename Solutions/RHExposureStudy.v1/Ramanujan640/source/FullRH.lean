import SharedRH
import IEANTN.Bridges.RH.LogicalAdapters
import IEANTN.Nodes.Buthe2016.v1.Conclusions
import IEANTN.Nodes.CH2.v5.Conclusions
import IEANTN.Nodes.CH2.v1.Conclusions
import Mathlib.Analysis.Complex.ExponentialBounds
import IEANTN.Nodes.LowZeroes.v1.Conclusions
import IEANTN.Nodes.ZetaHadamard.v1.Conclusions

open IEANTN Real
namespace FullRH

theorem strip_zero_re (hRH : SharedRH.hypothesis)
    (r : zetaZeroesIn (Set.Ioo (0:ℝ) 1) Set.univ) : (r : ℂ).re = 1/2 := by
  have hr := r.property
  exact hRH r hr.2.2 (RH.LogicalAdapters.nontrivial_of_pos_re hr.1.1) (by
    intro h
    have hh := hr.1.2
    rw [h] at hh
    norm_num at hh)

theorem right_density_zero (hRH : SharedRH.hypothesis) (σ T : ℝ)
    (hσ : 1/2 ≤ σ) : zetaN' σ T = 0 := by
  have : IsEmpty (zetaZeroesIn (Set.Ioo σ 1) (Set.Ioo 0 T)) := ⟨fun ⟨r, hr⟩ => by
    have hs := strip_zero_re hRH ⟨r, ⟨⟨by linarith [hr.1.1], hr.1.2⟩, trivial, hr.2.2⟩⟩
    change r.re = 1/2 at hs
    linarith [hr.1.1]⟩
  unfold zetaN' zetaZeroesSum
  exact tsum_empty

theorem classical_of_low (hRH : SharedRH.hypothesis) {R t0 H : ℝ}
    (ht0 : 0 < t0) (hHpos : 0 < H) (hR : 0 < R) (hH : 2 < R * log H)
    (hlow : zetaZeroesIn Set.univ (Set.Ioo 0 H) = ∅) :
    ClassicalZeroFreeRegion R t0 := by
  intro σ t ht hσ hz
  have htpos := ht0.trans_le ht
  by_cases h : t < H
  · have hh : (σ + t * Complex.I : ℂ) ∈ zetaZeroesIn Set.univ (Set.Ioo 0 H) := by
      refine ⟨trivial, ?_, hz⟩
      simpa using (show t ∈ Set.Ioo 0 H from ⟨htpos, h⟩)
    rw [hlow] at hh
    exact hh
  · have hlogH : 0 < log H := by
      by_contra! hn
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hR.le hn]
    have hd : 2 < R * log t := hH.trans_le
      (mul_le_mul_of_nonneg_left (Real.log_le_log hHpos (le_of_not_gt h)) hR.le)
    have he : 1 / (R * log t) < (1/2 : ℝ) := by
      apply (div_lt_iff₀ (show 0 < R * log t by linarith)).2
      linarith
    have hs : 1/2 < σ := by linarith
    refine RH.LogicalAdapters.half_plane hRH (le_refl (1/2 : ℝ)) (σ + t * Complex.I) ?_ ?_ hz
    · simpa using hs
    · intro hh
      have hi := congrArg Complex.im hh
      simp at hi
      linarith

theorem sqrt_log_fallback (hRH : SharedRH.hypothesis)
    (hc : CH2.v5.psi_bound_of_fixed_strip) {x : ℝ} (hx : exp 32 ≤ x) :
    Eψ x ≤ (1/2 : ℝ) * log x ^ 2 * x ^ (-(1/2 : ℝ)) := by
  have hh := hc (1/2) (by norm_num) (by norm_num)
    (RH.LogicalAdapters.half_plane hRH (le_refl _)) x
  norm_num at hh
  exact hh hx

theorem buthe_all_pi (hRH : SharedRH.hypothesis)
    (hb : Buthe2016.v1.theorem_2_li_minus_pi) {x : ℝ} (hx : 2657 < x) :
    |primeCounting x - li x| ≤ sqrt x * log x / (8 * π) :=
  hb _ (RH.LogicalAdapters.finite_height hRH _) x hx (le_refl _)

theorem buthe_all_psi (hRH : SharedRH.hypothesis)
    (hb : Buthe2016.v1.theorem_2_psi) {x : ℝ} (hx : 59 < x) :
    |Chebyshev.psi x - x| ≤ sqrt x * log x ^ 2 / (8 * π) :=
  hb _ (RH.LogicalAdapters.finite_height hRH _) x hx (le_refl _)

theorem buthe_all_theta (hRH : SharedRH.hypothesis)
    (hb : Buthe2016.v1.theorem_2_theta) {x : ℝ} (hx : 599 < x) :
    |Chebyshev.theta x - x| ≤ sqrt x * log x ^ 2 / (8 * π) :=
  hb _ (RH.LogicalAdapters.finite_height hRH _) x hx (le_refl _)


theorem classical_one (hRH : SharedRH.hypothesis)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate) :
    ClassicalZeroFreeRegion 1 2 := by
  have hh : zetaZeroesIn Set.univ (Set.Ioo 0 (14.134725 : ℝ)) = ∅ := by
    simpa [LowZeroes.v1.no_zeroes_below_first_ordinate, margin] using hlow
  refine classical_of_low hRH (by norm_num) (by norm_num) (by norm_num) ?_ hh
  rw [one_mul, Real.lt_log_iff_exp_lt (by norm_num)]
  rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

theorem adaptive_ch2 (hRH : SharedRH.hypothesis) (hc : CH2.v1.corollary_1_2_psi)
    {T x : ℝ} (hT : (10:ℝ)^7 ≤ T) (hx : max T ((10:ℝ)^9) < x) :
    |Chebyshev.psi x - x * CH2.v1.mainFactor T| ≤ π / (T-1) * x + CH2.v1.CT T * sqrt x :=
  hc T x hT (RH.LogicalAdapters.finite_height hRH T) hx

theorem adaptive_lambda (hRH : SharedRH.hypothesis) (hc : CH2.v1.corollary_1_2_lambda_sum)
    {T x : ℝ} (hT : (10:ℝ)^7 ≤ T) (hx : max T ((10:ℝ)^9) < x) :
    |CH2.v1.lambdaSum x - (log x - eulerMascheroniConstant)| ≤ π / (T-1) + CH2.v1.CT T / sqrt x :=
  hc T x hT (RH.LogicalAdapters.finite_height hRH T) hx

#print axioms right_density_zero
#print axioms classical_of_low
#print axioms classical_one
#print axioms adaptive_ch2
#print axioms adaptive_lambda
#print axioms sqrt_log_fallback
#print axioms buthe_all_pi
end FullRH
