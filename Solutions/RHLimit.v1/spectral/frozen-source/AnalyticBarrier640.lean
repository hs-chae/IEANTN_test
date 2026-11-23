import RamanujanPV.AnalyticTransition

/-! Post-lock verification work. Frozen 155-term Ei evaluator and genuine
linear-ODE comparison; no numerical-success or desired-gap premise. -/
namespace Ramanujan640.AnalyticBarrier
open Real Set Finset RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable def eiPartial155 (z : ℝ) : ℝ :=
  ∑ n ∈ range 155, eiTerm z n

lemma eiTerm_ratio155 {z : ℝ} (hz : 0 ≤ z) {n : ℕ} (hn : 155 ≤ n) :
    eiTerm z (n+1) ≤ (z/156)*eiTerm z n := by
  rw [eiTerm_succ]
  have ht := eiTerm_nonneg hz n
  have hn' : (155:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < (n+2)^2 := by positivity
  apply (div_le_iff₀ hden).mpr
  have hp : (156:ℝ)*(n+1) ≤ (n+2)^2 := by
    nlinarith [sq_nonneg (n-155:ℝ)]
  have hq : z*(n+1) ≤ (z/156)*(n+2)^2 := by
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hp)]
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hq)]

/-- Exact source remainder: t155*z / (156*(156-z)), where
t155=z^155/155!. No change to the frozen 155-term numerical method. -/
theorem ei_series_remainder155 {z : ℝ} (hz : 0 ≤ z) (hz44 : z ≤ 44) :
    0 ≤ (∑' n, eiTerm z n) - eiPartial155 z ∧
    (∑' n, eiTerm z n) - eiPartial155 z ≤
      (z^155 / (Nat.factorial 155 : ℝ))*z/(156*(156-z)) := by
  have hs := summable_eiTerm hz
  have he := hs.sum_add_tsum_nat_add 155
  have hr0 : 0 ≤ z/156 := by positivity
  have hr1 : z/156 < 1 := by linarith
  have ht := geometric_tail 155 (eiTerm_nonneg hz) hr0 hr1
    (fun k => eiTerm_ratio155 hz (by omega : 155 ≤ 155+k))
  have he' : (∑' n, eiTerm z n) - eiPartial155 z =
      ∑' k, eiTerm z (155+k) := by
    have he2 : eiPartial155 z + (∑' k, eiTerm z (155+k)) = ∑' n, eiTerm z n := by
      simpa only [eiPartial155, Nat.add_comm] using he
    linarith
  rw [he']
  constructor
  · exact tsum_nonneg (fun k => eiTerm_nonneg hz _)
  · have hEq : eiTerm z 155 / (1-z/156) =
        (z^155 / (Nat.factorial 155 : ℝ))*z/(156*(156-z)) := by
      unfold eiTerm
      have hzden : (156:ℝ)-z ≠ 0 := by linarith
      norm_num [Nat.factorial]
      rw [show z^156 = z^155*z by ring]
      field_simp [hzden]
      <;> ring
    exact ht.2.trans_eq hEq

/-- Integrating-factor comparison for an actual differentiable real function. -/
theorem ode_nonneg {f f' : ℝ → ℝ} {a x : ℝ} (hax : a ≤ x)
    (hd : ∀ t ∈ Ici a, HasDerivAt f (f' t) t)
    (hforcing : ∀ t ∈ Ici a, 0 ≤ f' t + f t) (ha : 0 ≤ f a) :
    0 ≤ f x := by
  let g : ℝ → ℝ := fun t => Real.exp t * f t
  have hg : ∀ t ∈ Ici a, HasDerivAt g (Real.exp t*(f t+f' t)) t := by
    intro t ht
    convert (Real.hasDerivAt_exp t).mul (hd t ht) using 1 <;> first | rfl | ring
  have hm : MonotoneOn g (Ici a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro t ht
      exact (hg t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hg t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hg t (interior_subset ht)).deriv]
      exact mul_nonneg (Real.exp_pos t).le (by linarith [hforcing t (interior_subset ht)])
  have hga : 0 ≤ g a := mul_nonneg (Real.exp_pos a).le ha
  have hmono := hm (show a ∈ Ici a by simp) hax hax
  have hgx : 0 ≤ Real.exp x * f x := hga.trans hmono
  exact nonneg_of_mul_nonneg_right hgx (Real.exp_pos x)

/-- A supersolution may be supplied through its derivative, not through the
desired conclusion. This is the generic analytic mechanism of both barriers. -/
theorem ode_compare {f f' g g' : ℝ → ℝ} {a x : ℝ} (hax : a ≤ x)
    (hf : ∀ t ∈ Ici a, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Ici a, HasDerivAt g (g' t) t)
    (hforcing : ∀ t ∈ Ici a, f' t + f t ≤ g' t + g t)
    (ha : f a ≤ g a) : f x ≤ g x := by
  have h := ode_nonneg hax (f:=fun t => g t-f t) (f':=fun t => g' t-f' t)
    (fun t ht => (hg t ht).sub (hf t ht))
    (by intro t ht; linarith [hforcing t ht]) (sub_nonneg.mpr ha)
  exact sub_nonneg.mp h

#print axioms ei_series_remainder155
#print axioms ode_nonneg
#print axioms ode_compare
end Ramanujan640.AnalyticBarrier
