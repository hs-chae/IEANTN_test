/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Applications
import FKS2Scalar.ExpCertificate

namespace FKS2Table4
open Real IEANTN MeasureTheory Set intervalIntegral

noncomputable def Q (L : ℝ) : ℝ := L^2/283*exp (-L/8)
noncomputable def kernel (t : ℝ) : ℝ := 1/(log t)^2
noncomputable def err (t : ℝ) : ℝ := (Chebyshev.theta t-t)/(t*(log t)^2)
noncomputable def W (b : ℝ) : ℝ :=
  Li (exp (b+1))-Li (exp b)+exp b/b-exp (b+1)/(b+1)
noncomputable def cell (b : ℝ) : ℝ :=
  330*exp (-330)*Q b*((exp (b+1)-exp b)/b^2)
noncomputable def anchor : ℝ := (330/300)*exp (-30)*(1.6997e-12+Q 300)
noncomputable def cells : ℝ := ∑ j ∈ Finset.range 30, cell (300+j)
/-- A deliberately coarser, proved whole-ray tail than FKS2 equation(12). -/
noncomputable def allowance : ℝ := anchor+cells+Q 330+Q 330/328

theorem Q_nonneg (L : ℝ) : 0 ≤ Q L := by unfold Q; positivity

theorem Q_antitone {a b : ℝ} (ha : 300 ≤ a) (hab : a ≤ b) : Q b ≤ Q a := by
  have h := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 2
    (L0 := a) (c := (1/8:ℝ)) (by linarith)
    ((div_le_iff₀ (by linarith : 0<a)).mpr (by linarith)) hab
  unfold Q
  have he : ∀ t : ℝ, -(1/8:ℝ)*t = -t/8 := by intro t;ring
  simp only [he] at h
  nlinarith

theorem theta_input (hpsi : QRHCH2.v5.psi_refined_bound) :
    ∀ L ≥ 300, Eθ (exp L) ≤ Q L := by
  intro L hL
  have h := QRHPropagation.theta_exp_bound hpsi hL
  change |Chebyshev.theta (exp L)-exp L| ≤ _ at h
  unfold Eθ Q
  apply (div_le_iff₀ (exp_pos L)).mpr
  have he : exp (7*L/8) = exp (-L/8)*exp L := by rw [← exp_add];congr 1;ring
  rw [he] at h
  nlinarith

theorem theta_on_ray (hθ : ∀ L ≥ 300, Eθ (exp L) ≤ Q L)
    {b t : ℝ} (hb : 300 ≤ b) (ht : exp b ≤ t) : Eθ t ≤ Q b := by
  have ht0 : 0<t := (exp_pos b).trans_le ht
  have hl : b ≤ log t := by simpa using log_le_log (exp_pos b) ht
  rw [← exp_log ht0]
  exact (hθ (log t) (hb.trans hl)).trans (Q_antitone hb hl)

theorem kernel_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable kernel volume a b := by
  exact ((FKS2Sol.continuousOn_inv_log (ha.trans hab) 2).intervalIntegrable (μ := volume)).mono_set
    (by rw [uIcc_of_le hab,uIcc_of_le (ha.trans hab)];intro t ht;exact ⟨ha.trans ht.1,ht.2⟩)

theorem weight_identity {b : ℝ} (hb : 300 ≤ b) :
    W b = ∫ t in exp b..exp (b+1), kernel t := by
  have h0 : 2 ≤ exp b := by linarith [add_one_le_exp b]
  have h1 : 2 ≤ exp (b+1) := by linarith [add_one_le_exp (b+1)]
  have h := integral_interval_sub_left
    ((FKS2Sol.continuousOn_inv_log h1 2).intervalIntegrable (μ := volume))
    ((FKS2Sol.continuousOn_inv_log h0 2).intervalIntegrable (μ := volume))
  have hL0 := FKS2Sol.Li_eq h0
  have hL1 := FKS2Sol.Li_eq h1
  unfold W kernel
  rw [log_exp] at hL0 hL1
  linarith

theorem weight_bounds {b : ℝ} (hb : 300 ≤ b) :
    0 ≤ W b ∧ W b ≤ (exp (b+1)-exp b)/b^2 := by
  rw [weight_identity hb]
  have hab : exp b ≤ exp (b+1) := exp_le_exp.mpr (by linarith)
  constructor
  · apply integral_nonneg hab
    intro t ht
    exact one_div_nonneg.mpr (sq_nonneg _)
  · have hi := kernel_integrable (by linarith [add_one_le_exp b]) hab
    have hc : IntervalIntegrable (fun _ : ℝ => 1/b^2) volume (exp b) (exp (b+1)) :=
      intervalIntegrable_const
    have hm := integral_mono_on hab hi hc (fun t ht => by
      have hl : b ≤ log t := by simpa using log_le_log (exp_pos b) ht.1
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by linarith) hl 2))
    simpa [intervalIntegral.integral_const,div_eq_mul_inv,mul_comm] using hm

theorem cell_absolute_integral_bound (hθ : ∀ L ≥ 300, Eθ (exp L) ≤ Q L)
    {b : ℝ} (hb : 300 ≤ b) :
    (∫ t in exp b..exp (b+1), |err t|) ≤ Q b*W b := by
  have hab : exp b ≤ exp (b+1) := exp_le_exp.mpr (by linarith)
  have hi : IntervalIntegrable err volume (exp b) (exp (b+1)) :=
    FKS2Sol.intervalIntegrable_sub_div (by linarith [add_one_le_exp b]) hab
  have hk := kernel_integrable (by linarith [add_one_le_exp b]) hab
  rw [weight_identity hb]
  calc
    _ ≤ ∫ t in exp b..exp (b+1), Q b*kernel t := by
      apply integral_mono_on hab hi.abs (hk.const_mul _)
      intro t ht
      have ht0 : 0<t := (exp_pos b).trans_le ht.1
      have hlog : 0<log t := by
        have hl : b ≤ log t := by simpa using log_le_log (exp_pos b) ht.1
        linarith
      have he : |err t| = Eθ t * kernel t := by
        unfold err Eθ kernel
        rw [abs_div,abs_of_pos (by positivity : 0<t*(log t)^2)]
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (theta_on_ray hθ hb ht.1) (by unfold kernel;positivity)
    _ = _ := integral_const_mul _ _

theorem cell_error_bound (hθ : ∀ L ≥ 300, Eθ (exp L) ≤ Q L)
    {b : ℝ} (hb : 300 ≤ b) :
    |∫ t in exp b..exp (b+1), err t| ≤ Q b*W b :=
  (abs_integral_le_integral_abs (exp_le_exp.mpr (by linarith))).trans
    (cell_absolute_integral_bound hθ hb)

theorem cell_normalization {b : ℝ} (hb : 300 ≤ b) :
    cell b = (330*(exp 1-1)/283)*exp (7*b/8-330) := by
  have he : exp (b+1)-exp b = exp b*(exp 1-1) := by rw [exp_add];ring
  have hs : exp (-330)*exp (-b/8)*exp b = exp (7*b/8-330) := by
    rw [← exp_add,← exp_add];congr 1;ring
  unfold cell Q
  rw [he]
  calc
    _ = (330*(exp 1-1)/283)*(exp (-330)*exp (-b/8)*exp b) := by
      field_simp
      <;> ring
    _ = _ := by rw [hs]

end FKS2Table4
