/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OcticGeometry
import OcticConsumer

namespace RHLimit.OcticGeometry
open Real Set
set_option maxHeartbeats 2000000

theorem a_ge_twenty_four {C L : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hL : 24 ≤ L) : (24 : ℝ) ≤ EvenKernel.a C L := by
  have hs := delta_small hC hL
  have he := Real.add_one_le_exp (L - EvenKernel.δ C L)
  unfold EvenKernel.a
  linarith

theorem b_le_three_a {C L : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hL : 24 ≤ L) : EvenKernel.b C L ≤ 3 * EvenKernel.a C L := by
  have hs := delta_small hC hL
  have he : exp (2 * EvenKernel.δ C L) ≤ 3 :=
    (Real.exp_le_exp.mpr (by linarith : 2 * EvenKernel.δ C L ≤ 1)).trans
      Real.exp_one_lt_three.le
  have heq : EvenKernel.b C L = EvenKernel.a C L * exp (2 * EvenKernel.δ C L) := by
    unfold EvenKernel.a EvenKernel.b
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ EvenKernel.a C L by
    unfold EvenKernel.a; positivity)
  nlinarith

theorem window_width {C L : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hL : 24 ≤ L) :
    EvenKernel.b C L - EvenKernel.a C L ≤
      C * sqrt (EvenKernel.a C L) * log (EvenKernel.a C L) := by
  let d := EvenKernel.δ C L
  let s := exp ((L - d) / 2)
  have hd0 : 0 ≤ d := delta_nonneg hC.1 hL
  have hds : d ≤ 3 / 2500 := delta_small hC hL
  have ha0 : 0 < EvenKernel.a C L := exp_pos _
  have hs0 : 0 < s := exp_pos _
  have hsmall : |2 * d| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have he := Real.abs_exp_sub_one_sub_id_le hsmall
  have he' : exp (2 * d) - 1 ≤ 2 * d + 4 * d ^ 2 := by
    have hh := (le_abs_self (exp (2 * d) - 1 - 2 * d)).trans he
    nlinarith
  have hD : exp (L / 2) * (2 * d) = C * L - 2 := by
    dsimp [d]
    rw [delta_eq_div]
    field_simp
    unfold EvenKernel.D
    ring
  have hsqrt : s = sqrt (EvenKernel.a C L) := by
    dsimp [s, d, EvenKernel.a]
    exact Real.exp_half _
  have hrepr : EvenKernel.a C L = s * (exp (L / 2) * exp (-d / 2)) := by
    dsimp [s, d, EvenKernel.a]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hpoly : EvenKernel.a C L * (2 * d + 4 * d ^ 2) =
      s * ((C * L - 2) * exp (-d / 2) * (1 + 2 * d)) := by
    rw [hrepr]
    calc
      _ = s * ((exp (L / 2) * (2 * d)) * exp (-d / 2) * (1 + 2 * d)) := by ring
      _ = _ := by rw [hD]
  have hCL : 0 ≤ C * L - 2 := by
    have hh := D_nonneg hC.1 hL
    unfold EvenKernel.D at hh
    nlinarith
  have hneg : exp (-d / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hdrop : (C * L - 2) * exp (-d / 2) * (1 + 2 * d) ≤
      (C * L - 2) * (1 + 2 * d) := by
    have hm := mul_le_mul_of_nonneg_left hneg hCL
    exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hm)
      (by linarith : 0 ≤ 1 + 2 * d)
  have hb : 4 * C * L * d ≤ 1152 / 625 := width_budget hC hL
  have hCp : 0 ≤ C := by linarith [hC.1]
  have hCto : C ≤ 2 * C * L := by
    have hm := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * L by linarith) hCp
    nlinarith
  have hm := mul_le_mul_of_nonneg_left
    (show 2 * C * L + C - 4 ≤ 4 * C * L by linarith) hd0
  have hscalar : (C * L - 2) * (1 + 2 * d) ≤ C * (L - d) := by nlinarith
  have hwindow : EvenKernel.b C L - EvenKernel.a C L =
      EvenKernel.a C L * (exp (2 * d) - 1) := by
    have heq : EvenKernel.b C L = EvenKernel.a C L * exp (2 * d) := by
      dsimp [d]
      unfold EvenKernel.a EvenKernel.b
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    ring
  calc
    EvenKernel.b C L - EvenKernel.a C L = EvenKernel.a C L * (exp (2 * d) - 1) := hwindow
    _ ≤ EvenKernel.a C L * (2 * d + 4 * d ^ 2) :=
      mul_le_mul_of_nonneg_left he' ha0.le
    _ = s * ((C * L - 2) * exp (-d / 2) * (1 + 2 * d)) := hpoly
    _ ≤ s * ((C * L - 2) * (1 + 2 * d)) := mul_le_mul_of_nonneg_left hdrop hs0.le
    _ ≤ s * (C * (L - d)) := mul_le_mul_of_nonneg_left hscalar hs0.le
    _ = C * sqrt (EvenKernel.a C L) * log (EvenKernel.a C L) := by
      rw [hsqrt]
      unfold EvenKernel.a
      rw [Real.log_exp]
      dsimp [d]
      ring

/-- A bounded IVT construction covers every endpoint; no global inverse is used. -/
theorem forward_coverage_family {C : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16) :
    EvenKernel.ForwardCoverage C := by
  intro u hu
  have hu0 : 0 < u := (exp_pos 24).trans_le hu
  have hlogu : 24 ≤ log u := by
    have hh := Real.log_le_log (exp_pos 24) hu
    simpa only [Real.log_exp] using hh
  let f : ℝ → ℝ := fun L => L - EvenKernel.δ C L
  have hf : Continuous f := by dsimp [f, EvenKernel.δ, EvenKernel.D]; fun_prop
  have hlo : f (log u) ≤ log u := by
    have hd := delta_nonneg hC.1 hlogu
    dsimp [f]
    linarith
  have hhi : log u ≤ f (log u + 1) := by
    have hs := delta_small hC (show 24 ≤ log u + 1 by linarith)
    dsimp [f]
    linarith
  obtain ⟨L, hLi, hEq⟩ := (intermediate_value_Icc (a := log u) (b := log u + 1)
    (by linarith) hf.continuousOn) (show log u ∈ Icc (f (log u)) (f (log u + 1))
      from ⟨hlo, hhi⟩)
  have hL : 24 ≤ L := hlogu.trans hLi.1
  have hcenter : EvenKernel.a C L = u := by
    change exp (f L) = u
    rw [hEq, Real.exp_log hu0]
  refine ⟨L, hL, hcenter, ?_⟩
  have hw := window_width hC hL
  rw [hcenter] at hw
  linarith

theorem forward_coverage_215 : EvenKernel.ForwardCoverage (43 / 20) :=
  forward_coverage_family (by norm_num)

/-- Actual all-real count with both geometric contracts now proved. -/
theorem prime_count_215_reduced (rh : RiemannHypothesis)
    (hef : EvenKernel.ExplicitFormula 4 (43 / 20))
    (hz : EvenKernel.ZeroEstimate 4 (43 / 20) (911 / 500) (3 / 2) (3 / 125))
    (hpp : EvenKernel.PrimePowerCost 4 (43 / 20) (31 / 2000))
    (ht : EvenKernel.TrivialCost 4 (43 / 20) (1 / 1000)) :
    ∀ u : ℝ, Real.exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + 43 / 20 * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u :=
  OcticConsumer.prime_count_215 rh hef hz hpp ht scalar_geometry_215 forward_coverage_215

#print axioms window_width
#print axioms forward_coverage_family
#print axioms prime_count_215_reduced
end RHLimit.OcticGeometry
