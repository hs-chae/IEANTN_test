/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.DirectKernelNorm
namespace WinnerDirectKernel
open Complex

noncomputable def highFactor (a H v L : ℝ) : ℝ :=
  1 + 1/(H*L) + Real.exp (-a*(L-v))*L/(H*v^2) + 2*L/(H*a*v^3)

/-- A common factor for every high-ordinate zero, retaining reciprocal ordinate in the main sum. -/
theorem norm_piKernel_high {z : ℂ} {a H v L : ℝ}
    (ha : 0 < a) (hH : 0 < H) (hv : 0 < v) (hL : v ≤ L)
    (hb : a ≤ z.re) (hg : H ≤ |z.im|) :
    ‖piKernel z v L‖ ≤
      (Real.exp (z.re*L)/(|z.im| * L)) * highFactor a H v L := by
  let n := ‖z‖
  let g := |z.im|
  have hLp : 0 < L := hv.trans_le hL
  have hgp : 0 < g := hH.trans_le hg
  have hgn : g ≤ n := Complex.abs_im_le_norm z
  have hnp : 0 < n := hgp.trans_le hgn
  have hz : z ≠ 0 := norm_pos_iff.mp hnp
  have hbp : 0 < z.re := ha.trans_le hb
  have hn2 : g*H ≤ n^2 := by
    calc g*H ≤ n*n := mul_le_mul hgn (hg.trans hgn) hH.le hnp.le
         _ = n^2 := by ring
  have hn2b : g*H*a ≤ n^2*z.re := by
    calc g*H*a ≤ n^2*a := mul_le_mul_of_nonneg_right hn2 ha.le
         _ ≤ n^2*z.re := mul_le_mul_of_nonneg_left hb (sq_nonneg n)
  have he : Real.exp (z.re*v) ≤ Real.exp (z.re*L)*Real.exp (-a*(L-v)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hL)]
  have t1 : Real.exp (z.re*L)/(n*L) ≤ Real.exp (z.re*L)/(g*L) := by
    apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
    exact mul_le_mul_of_nonneg_right hgn hLp.le
  have t2 : Real.exp (z.re*L)/(n^2*L^2) ≤
      (Real.exp (z.re*L)/(g*L))*(1/(H*L)) := by
    calc _ ≤ Real.exp (z.re*L)/(g*H*L^2) := by
           apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
           exact mul_le_mul_of_nonneg_right hn2 (sq_nonneg L)
         _ = _ := by field_simp
  have t3 : Real.exp (z.re*v)/(n^2*v^2) ≤
      (Real.exp (z.re*L)/(g*L))*(Real.exp (-a*(L-v))*L/(H*v^2)) := by
    calc _ ≤ (Real.exp (z.re*L)*Real.exp (-a*(L-v)))/(n^2*v^2) := by gcongr
         _ ≤ (Real.exp (z.re*L)*Real.exp (-a*(L-v)))/(g*H*v^2) := by
           apply div_le_div_of_nonneg_left (by positivity) (by positivity)
           exact mul_le_mul_of_nonneg_right hn2 (sq_nonneg v)
         _ = _ := by field_simp
  have t4 : 2*Real.exp (z.re*L)/(n^2*z.re*v^3) ≤
      (Real.exp (z.re*L)/(g*L))*(2*L/(H*a*v^3)) := by
    calc _ ≤ 2*Real.exp (z.re*L)/(g*H*a*v^3) := by
           apply div_le_div_of_nonneg_left (by positivity) (by positivity)
           exact mul_le_mul_of_nonneg_right hn2b (pow_nonneg hv.le 3)
         _ = _ := by field_simp
  have hnorm := norm_piKernel hz hv hL hbp
  change ‖piKernel z v L‖ ≤ (Real.exp (z.re*L)/(g*L))*highFactor a H v L
  dsimp only [highFactor]
  dsimp only [n] at t1 t2 t3 t4
  dsimp only [g] at t1 t2 t3 t4 ⊢
  nlinarith

#print axioms norm_piKernel_high
end WinnerDirectKernel
