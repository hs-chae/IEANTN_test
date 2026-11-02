/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Table4.Math

namespace FKS2Table4
open Real IEANTN MeasureTheory Set intervalIntegral

theorem uniform_integral_error {a b eps : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hE : ∀ t ∈ Icc a b, Eθ t ≤ eps) :
    |∫ t in a..b, err t| ≤ eps*(∫ t in a..b, kernel t) := by
  have hi : IntervalIntegrable err volume a b := FKS2Sol.intervalIntegrable_sub_div
    (by linarith) hab
  have hk := kernel_integrable ha hab
  calc
    _ ≤ ∫ t in a..b, |err t| := abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, eps*kernel t := by
      apply integral_mono_on hab hi.abs (hk.const_mul _)
      intro t ht
      have ht0 : 0<t := by linarith [ht.1]
      have hl : 0<log t := log_pos (by linarith [ht.1])
      have he : |err t| = Eθ t*kernel t := by
        unfold err Eθ kernel
        rw [abs_div,abs_of_pos (by positivity : 0<t*(log t)^2)]
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (hE t ht) (by unfold kernel;positivity)
    _ = _ := integral_const_mul _ _

/-- Elementary whole-ray replacement for the sharper maximum argument in FKS2(12). -/
theorem normalized_kernel_tail {x : ℝ} (hx : exp 330 ≤ x) :
    log x/x*(∫ t in exp 330..x, kernel t) ≤ (1:ℝ)/328 := by
  have hx0 : 0<x := (exp_pos _).trans_le hx
  have hlog : 330 ≤ log x := by simpa using log_le_log (exp_pos (330:ℝ)) hx
  let G : ℝ → ℝ := fun t => (330/328)*t/(log t)^2
  let D : ℝ → ℝ := fun t => (330/328)*(log t-2)/(log t)^3
  have hD : ∀ t ∈ uIcc (exp 330) x, HasDerivAt G (D t) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : 0<t := (exp_pos _).trans_le ht.1
    have hl : 0<log t := by
      have he : 330 ≤ log t := by simpa using log_le_log (exp_pos (330:ℝ)) ht.1
      linarith
    have hh := ((hasDerivAt_const t (330/328:ℝ)).mul (hasDerivAt_id t)).div
      ((hasDerivAt_log ht0.ne').pow 2) (pow_ne_zero 2 hl.ne')
    apply hh.congr_deriv
    dsimp [D]
    field_simp
    <;> ring
  have hcont : ContinuousOn D (uIcc (exp 330) x) := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : 0<t := (exp_pos _).trans_le ht.1
    have hl : 0<log t := by
      have he : 330 ≤ log t := by simpa using log_le_log (exp_pos (330:ℝ)) ht.1
      linarith
    exact (((continuousAt_const.mul ((continuousAt_log ht0.ne').sub continuousAt_const)).div
      ((continuousAt_log ht0.ne').pow 3) (pow_ne_zero 3 hl.ne'))).continuousWithinAt
  have hiD := hcont.intervalIntegrable (μ := volume)
  have hk := kernel_integrable (by linarith [add_one_le_exp (330:ℝ)]) hx
  have hcomp : (∫ t in exp 330..x, kernel t) ≤ G x-G (exp 330) := by
    rw [← integral_eq_sub_of_hasDerivAt hD hiD]
    apply integral_mono_on hx hk hiD
    intro t ht
    have ht0 : 0<t := (exp_pos _).trans_le ht.1
    have hl : 330 ≤ log t := by simpa using log_le_log (exp_pos (330:ℝ)) ht.1
    unfold kernel
    dsimp [D]
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<(log t)^2)
      (by positivity : (0:ℝ)<(log t)^3)).mpr
    nlinarith [mul_nonneg (sq_nonneg (log t)) (show 0 ≤ log t-330 by linarith)]
  have hG : 0 ≤ G (exp 330) := by dsimp [G];positivity
  have hm := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ log x/x by positivity)
  have hn : log x/x*G x = (330/328)/(log x) := by dsimp [G];field_simp
  have hf : (330/328:ℝ)/log x ≤ 1/328 := by
    apply (div_le_iff₀ (by linarith : 0<log x)).mpr
    linarith
  nlinarith [mul_nonneg (show 0 ≤ log x/x by positivity) hG]

theorem log_div_antitone {a x : ℝ} (ha : 1 ≤ a) (hx : exp a ≤ x) :
    log x/x ≤ a*exp (-a) := by
  have hx0 : 0<x := (exp_pos _).trans_le hx
  have hlog : a ≤ log x := by simpa using log_le_log (exp_pos a) hx
  have h := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 1
    (L0 := a) (c := 1) (by linarith) (by rw [div_le_one (by linarith : 0<a)];simpa using ha) hlog
  simpa [pow_one,exp_neg,exp_log hx0,div_eq_mul_inv] using h

theorem finite_integral_bound (hθ : ∀ L ≥ 300, Eθ (exp L) ≤ Q L) :
    330*exp (-330)*|∫ t in exp 300..exp 330, err t| ≤ cells := by
  have hs := sum_integral_adjacent_intervals (a := fun n : ℕ => exp (300+(n:ℝ)))
    (f := err) (μ := volume) (n := 30) (fun k hk =>
      FKS2Sol.intervalIntegrable_sub_div (by linarith [add_one_le_exp (300+(k:ℝ))])
        (exp_le_exp.mpr (by push_cast;linarith)))
  norm_num only [Nat.cast_zero,add_zero,Nat.cast_ofNat] at hs
  rw [← hs]
  have habs : |∑ j ∈ Finset.range 30, ∫ t in exp (300+(j:ℝ))..exp (300+((j+1:ℕ):ℝ)),err t| ≤
      ∑ j ∈ Finset.range 30, |∫ t in exp (300+(j:ℝ))..exp (300+((j+1:ℕ):ℝ)),err t| :=
    Finset.abs_sum_le_sum_abs _ _
  unfold cells
  calc
    _ ≤ 330*exp (-330)*(∑ j ∈ Finset.range 30,
      |∫ t in exp (300+(j:ℝ))..exp (300+((j+1:ℕ):ℝ)),err t|) := by gcongr
    _ = ∑ j ∈ Finset.range 30,330*exp (-330)*
      |∫ t in exp (300+(j:ℝ))..exp (300+((j+1:ℕ):ℝ)),err t| := by rw [Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      have hb : (300:ℝ) ≤ 300+j := by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
      have hc := cell_error_bound hθ hb
      have hw := weight_bounds hb
      have he : 300+((j+1:ℕ):ℝ) = (300+(j:ℝ))+1 := by push_cast;ring
      rw [he]
      change 330*exp (-330)*|∫ t in exp (300+(j:ℝ))..exp ((300+(j:ℝ))+1),err t| ≤ _
      calc
        _ ≤ (330*exp (-330))*(Q (300+(j:ℝ))*
            ((exp ((300+(j:ℝ))+1)-exp (300+(j:ℝ)))/(300+(j:ℝ))^2)) :=
          mul_le_mul_of_nonneg_left (hc.trans
            (mul_le_mul_of_nonneg_left hw.2 (Q_nonneg _))) (by positivity)
        _ = _ := by unfold cell;ring

theorem normalized_anchor (hθ : Eθ (exp 300) ≤ Q 300)
    (hOld : Eπ (exp 300) ≤ 1.6997e-12) :
    |(primeCounting (exp 300)-Li (exp 300))/(exp 300/300)-
      (Chebyshev.theta (exp 300)-exp 300)/exp 300| ≤ 1.6997e-12+Q 300 := by
  have hp : |(primeCounting (exp 300)-Li (exp 300))/(exp 300/300)| ≤ 1.6997e-12 := by
    rw [abs_div,abs_of_pos (by positivity : (0:ℝ)<exp 300/300)]
    simpa only [Eπ,log_exp] using hOld
  have ht : |(Chebyshev.theta (exp 300)-exp 300)/exp 300| ≤ Q 300 := by
    rw [abs_div,abs_of_pos (exp_pos _)]
    exact hθ
  exact (abs_sub _ _).trans (add_le_add hp ht)

theorem bounded_anchor (hθ : Eθ (exp 300) ≤ Q 300)
    (hOld : Eπ (exp 300) ≤ 1.6997e-12) :
    |primeCounting (exp 300)-Li (exp 300)-
      (Chebyshev.theta (exp 300)-exp 300)/300| ≤
      exp 300/300*(1.6997e-12+Q 300) := by
  have hQ := Q_nonneg 300
  have hp := (div_le_iff₀ (by positivity : (0:ℝ)< exp 300/300)).mp
    (show |primeCounting (exp 300)-Li (exp 300)|/(exp 300/300) ≤ 1.6997e-12 by
      simpa only [Eπ,log_exp] using hOld)
  have ht := (div_le_iff₀ (exp_pos (300:ℝ))).mp hθ
  change |Chebyshev.theta (exp 300)-exp 300| ≤ _ at ht
  have hd : |(Chebyshev.theta (exp 300)-exp 300)/300| ≤ exp 300/300*Q 300 := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<300)]
    nlinarith
  exact (abs_sub _ _).trans (by nlinarith [hp,hd])

theorem whole_ray_transport (hθ : ∀ L ≥ 300, Eθ (exp L) ≤ Q L)
    (hOld : Eπ (exp 300) ≤ 1.6997e-12) :
    ∀ x ≥ exp 330, Eπ x ≤ allowance := by
  intro x hx
  have hx0 : 0<x := (exp_pos _).trans_le hx
  have h330 : 2 ≤ exp (330:ℝ) := by linarith [add_one_le_exp (330:ℝ)]
  have h300 : 2 ≤ exp (300:ℝ) := by linarith [add_one_le_exp (300:ℝ)]
  have hab : exp (300:ℝ) ≤ exp 330 := exp_le_exp.mpr (by norm_num)
  have hm : 0 ≤ log x/x := by have := log_le_log (exp_pos (330:ℝ)) hx; rw [log_exp] at this;positivity
  have hp := FKS2Sol.Epi_le h300 (hab.trans hx)
  have hsplit := integral_add_adjacent_intervals
    (FKS2Sol.intervalIntegrable_sub_div (by linarith) hab)
    (FKS2Sol.intervalIntegrable_sub_div (by linarith) hx)
  have htri : |∫ t in exp 300..x,err t| ≤
      |∫ t in exp 300..exp 330,err t|+|∫ t in exp 330..x,err t| := by
    change |∫ t in exp 300..x,(Chebyshev.theta t-t)/(t*(log t)^2)| ≤ _
    rw [← hsplit]
    exact abs_add_le _ _
  have hA := bounded_anchor (hθ 300 le_rfl) hOld
  have hmono := log_div_antitone (by norm_num : (1:ℝ)≤330) hx
  have hanchor : log x/x*|primeCounting (exp 300)-Li (exp 300)-
      (Chebyshev.theta (exp 300)-exp 300)/log (exp 300)| ≤ anchor := by
    rw [log_exp]
    calc
      _ ≤ (330*exp (-330))*(exp 300/300*(1.6997e-12+Q 300)) :=
        mul_le_mul hmono hA (abs_nonneg _) (by positivity)
      _ = _ := by
        unfold anchor
        have he : exp (-330)*exp 300 = exp (-30:ℝ) := by rw [← exp_add];norm_num
        calc
          _ = (330/300)*(exp (-330)*exp 300)*(1.6997e-12+Q 300) := by ring
          _ = _ := by rw [he]
  have hfinite := (mul_le_mul_of_nonneg_right hmono (abs_nonneg
    (∫ t in exp 300..exp 330,err t))).trans (finite_integral_bound hθ)
  have ht := uniform_integral_error h330 hx
    (fun t ht => theta_on_ray hθ (b := 330) (by norm_num) ht.1)
  have htail : log x/x*|∫ t in exp 330..x,err t| ≤ Q 330/328 := by
    have h := mul_le_mul_of_nonneg_left ht hm
    have hnorm := mul_le_mul_of_nonneg_left (normalized_kernel_tail hx) (Q_nonneg 330)
    nlinarith [h,hnorm]
  have hpoint := theta_on_ray hθ (by norm_num : (300:ℝ)≤330) hx
  change Eπ x ≤ log x/x*|primeCounting (exp 300)-Li (exp 300)-
      (Chebyshev.theta (exp 300)-exp 300)/log (exp 300)|+Eθ x+
      log x/x*|∫ t in exp 300..x,err t| at hp
  have hmul := mul_le_mul_of_nonneg_left htri hm
  unfold allowance
  linarith

end FKS2Table4
