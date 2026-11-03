/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Table4.Transport

namespace FKS2Pair
open Real IEANTN MeasureTheory Set intervalIntegral FKS2Table4

/-- Only the31 entries indexed0 through30 are used. Each is a whole-tail allowance. -/
def ValidProfile (U : ℕ → ℝ) : Prop :=
  (∀ j : ℕ, j ≤ 30 → 0 ≤ U j) ∧
  ∀ j : ℕ, j ≤ 30 → ∀ t ≥ exp (300+(j:ℝ)), Eθ t ≤ U j

noncomputable def cellU (u b : ℝ) : ℝ :=
  (330*u/b^2)*(exp 1-1)*exp (b-330)
noncomputable def cells (U : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 30, cellU (U j) (300+j)
noncomputable def anchor (U : ℕ → ℝ) : ℝ :=
  (330/300)*exp (-30)*(1.6997e-12+U 0)
noncomputable def Bsafe (U : ℕ → ℝ) : ℝ :=
  anchor U+cells U+U 30+U 30/328

theorem cell_normalization (u b : ℝ) :
    330*exp (-330)*u*((exp (b+1)-exp b)/b^2) = cellU u b := by
  have he : exp (b+1)-exp b = exp b*(exp 1-1) := by rw [exp_add];ring
  have hs : exp (-330)*exp b=exp (b-330) := by rw [← exp_add];congr 1;ring
  unfold cellU
  rw [he]
  calc
    _ = (330*u/b^2)*(exp 1-1)*(exp (-330)*exp b) := by ring
    _ = _ := by rw [hs]

theorem finite_integral_bound {U : ℕ → ℝ} (hU : ValidProfile U) :
    330*exp (-330)*|∫ t in exp 300..exp 330, err t| ≤ cells U := by
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
      have hj30 : j ≤ 30 := by have := Finset.mem_range.mp hj;omega
      have hb : (300:ℝ) ≤ 300+j := by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
      have hc : |∫ t in exp (300+(j:ℝ))..exp ((300+(j:ℝ))+1),err t| ≤ U j*W (300+j) := by
        rw [weight_identity hb]
        exact uniform_integral_error (by linarith [add_one_le_exp (300+(j:ℝ))])
          (exp_le_exp.mpr (by linarith)) (fun t ht => hU.2 j hj30 t ht.1)
      have hw := weight_bounds hb
      have he : 300+((j+1:ℕ):ℝ) = (300+(j:ℝ))+1 := by push_cast;ring
      rw [he]
      calc
        _ ≤ (330*exp (-330))*(U j*
            ((exp ((300+(j:ℝ))+1)-exp (300+(j:ℝ)))/(300+(j:ℝ))^2)) :=
          mul_le_mul_of_nonneg_left (hc.trans
            (mul_le_mul_of_nonneg_left hw.2 (hU.1 j hj30))) (by positivity)
        _ = _ := by simpa only [mul_assoc] using cell_normalization (U j) (300+j)

theorem normalized_anchor {u : ℝ} (hθ : Eθ (exp 300) ≤ u)
    (hOld : Eπ (exp 300) ≤ 1.6997e-12) :
    |(primeCounting (exp 300)-Li (exp 300))/(exp 300/300)-
      (Chebyshev.theta (exp 300)-exp 300)/exp 300| ≤ 1.6997e-12+u := by
  have hp : |(primeCounting (exp 300)-Li (exp 300))/(exp 300/300)| ≤ 1.6997e-12 := by
    rw [abs_div,abs_of_pos (by positivity : (0:ℝ)<exp 300/300)]
    simpa only [Eπ,log_exp] using hOld
  have ht : |(Chebyshev.theta (exp 300)-exp 300)/exp 300| ≤ u := by
    rw [abs_div,abs_of_pos (exp_pos _)]
    exact hθ
  exact (abs_sub _ _).trans (add_le_add hp ht)

theorem bounded_anchor {u : ℝ} (hθ : Eθ (exp 300) ≤ u)
    (hOld : Eπ (exp 300) ≤ 1.6997e-12) :
    |primeCounting (exp 300)-Li (exp 300)-
      (Chebyshev.theta (exp 300)-exp 300)/300| ≤ exp 300/300*(1.6997e-12+u) := by
  have hp := (div_le_iff₀ (by positivity : (0:ℝ)<exp 300/300)).mp
    (show |primeCounting (exp 300)-Li (exp 300)|/(exp 300/300) ≤ 1.6997e-12 by
      simpa only [Eπ,log_exp] using hOld)
  have ht := (div_le_iff₀ (exp_pos (300:ℝ))).mp hθ
  change |Chebyshev.theta (exp 300)-exp 300| ≤ _ at ht
  have hd : |(Chebyshev.theta (exp 300)-exp 300)/300| ≤ exp 300/300*u := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<300)]
    nlinarith
  exact (abs_sub _ _).trans (by nlinarith [hp,hd])

/-- Same31 allowances, same historical anchor and same entire ray for both configurations. -/
theorem whole_ray_transport {U : ℕ → ℝ} (hU : ValidProfile U)
    (hOld : Eπ (exp 300) ≤ 1.6997e-12) :
    ∀ x ≥ exp 330, Eπ x ≤ Bsafe U := by
  intro x hx
  have hx0 : 0<x := (exp_pos _).trans_le hx
  have h330 : 2 ≤ exp (330:ℝ) := by linarith [add_one_le_exp (330:ℝ)]
  have h300 : 2 ≤ exp (300:ℝ) := by linarith [add_one_le_exp (300:ℝ)]
  have hab : exp (300:ℝ) ≤ exp 330 := exp_le_exp.mpr (by norm_num)
  have hθ0 : Eθ (exp 300) ≤ U 0 := by
    simpa using hU.2 0 (by norm_num) (exp 300) (by simp)
  have hθ30 : ∀ t ≥ exp 330,Eθ t ≤ U 30 := by
    intro t ht
    have h := hU.2 30 le_rfl t
    norm_num at h
    exact h ht
  have hm : 0 ≤ log x/x := by have := log_le_log (exp_pos (330:ℝ)) hx;rw [log_exp] at this;positivity
  have hp := FKS2Sol.Epi_le h300 (hab.trans hx)
  have hsplit := integral_add_adjacent_intervals
    (FKS2Sol.intervalIntegrable_sub_div (by linarith) hab)
    (FKS2Sol.intervalIntegrable_sub_div (by linarith) hx)
  have htri : |∫ t in exp 300..x,err t| ≤
      |∫ t in exp 300..exp 330,err t|+|∫ t in exp 330..x,err t| := by
    change |∫ t in exp 300..x,(Chebyshev.theta t-t)/(t*(log t)^2)| ≤ _
    rw [← hsplit]
    exact abs_add_le _ _
  have hA := bounded_anchor hθ0 hOld
  have hmono := log_div_antitone (by norm_num : (1:ℝ)≤330) hx
  have hu0 := hU.1 0 (by norm_num)
  have hanchor : log x/x*|primeCounting (exp 300)-Li (exp 300)-
      (Chebyshev.theta (exp 300)-exp 300)/log (exp 300)| ≤ anchor U := by
    rw [log_exp]
    calc
      _ ≤ (330*exp (-330))*(exp 300/300*(1.6997e-12+U 0)) :=
        mul_le_mul hmono hA (abs_nonneg _) (by positivity)
      _ = _ := by
        unfold anchor
        have he : exp (-330)*exp 300=exp (-30:ℝ) := by rw [← exp_add];norm_num
        calc
          _ = (330/300)*(exp (-330)*exp 300)*(1.6997e-12+U 0) := by ring
          _ = _ := by rw [he]
  have hfinite := (mul_le_mul_of_nonneg_right hmono (abs_nonneg
    (∫ t in exp 300..exp 330,err t))).trans (finite_integral_bound hU)
  have ht := uniform_integral_error h330 hx (fun t ht => hθ30 t ht.1)
  have htail : log x/x*|∫ t in exp 330..x,err t| ≤ U 30/328 := by
    have h := mul_le_mul_of_nonneg_left ht hm
    have hnorm := mul_le_mul_of_nonneg_left (normalized_kernel_tail hx) (hU.1 30 le_rfl)
    nlinarith [h,hnorm]
  have hpoint := hθ30 x hx
  change Eπ x ≤ log x/x*|primeCounting (exp 300)-Li (exp 300)-
      (Chebyshev.theta (exp 300)-exp 300)/log (exp 300)|+Eθ x+
      log x/x*|∫ t in exp 300..x,err t| at hp
  have hmul := mul_le_mul_of_nonneg_left htri hm
  unfold Bsafe
  linarith
end FKS2Pair
