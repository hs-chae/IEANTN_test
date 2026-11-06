/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.PrimeConsumer
import IEANTN.Nodes.KadiriLumley.v1.Conclusions

/-!
Strict comparison of interval-length allowance functions. These are comparisons
with the explicitly listed numerical prime-gap providers. They do not claim a
complete census of all implicit theta-derived routes or effective external
literature, and do not infer mathematical quality from evidence designation.
-/

namespace DirectIntervalA
open Real Set MeasureTheory Complex
set_option maxHeartbeats 0

theorem exp_fifth_gt_max_denominator {L : ℝ} (hL : 330 ≤ L) :
    (60000000000000:ℝ) < Real.exp (L/5) := by
  have he := Real.pow_div_factorial_le_exp (66:ℝ) (by norm_num) 13
  norm_num at he
  have hm : Real.exp 66 ≤ Real.exp (L/5) := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Covers each registered fixed relative width, including backward intervals
after the exact denominator Delta-1 conversion. -/
theorem gap_lt_fixed_relative {L D : ℝ} (hL : 330 ≤ L)
    (hD : 0 < D) (hDmax : D ≤ 60000000000000) :
    Real.exp (4*L/5) < Real.exp L/D := by
  have hd : D < Real.exp (L/5) := hDmax.trans_lt (exp_fifth_gt_max_denominator hL)
  have hh := mul_lt_mul_of_pos_right hd (Real.exp_pos (4*L/5))
  have he : Real.exp (L/5)*Real.exp (4*L/5)=Real.exp L := by
    rw [←Real.exp_add];congr 1;ring
  rw [he] at hh
  exact (lt_div_iff₀ hD).mpr (by nlinarith only [hh])

/-- Covers the constant-coefficient exponent-7/8 interval providers. -/
theorem gap_lt_density_relative {L C : ℝ} (hL : 330 ≤ L)
    (hC : (264/10000:ℝ) ≤ C) :
    Real.exp (4*L/5) < C*Real.exp (7*L/8) := by
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 3*L/40 by linarith)
  have hs : (99/4:ℝ)^2 ≤ (3*L/40)^2 := by nlinarith
  have he40 : (40:ℝ) < Real.exp (3*L/40) := by nlinarith
  have hc := mul_le_mul_of_nonneg_right hC (Real.exp_pos (3*L/40)).le
  have hbig : (1:ℝ) < C*Real.exp (3*L/40) := by nlinarith
  have hm := mul_lt_mul_of_pos_right hbig (Real.exp_pos (4*L/5))
  have hid : C*Real.exp (3*L/40)*Real.exp (4*L/5)=C*Real.exp (7*L/8) := by
    rw [mul_assoc,←Real.exp_add]
    congr 1
    congr 1
    ring
  rw [one_mul,hid] at hm
  exact hm

/-- The earlier logarithm-squared QRH interval is also strictly wider. -/
theorem gap_lt_log_squared_relative {L : ℝ} (hL : 330 ≤ L) :
    Real.exp (4*L/5) < (4/283:ℝ)*L^2*Real.exp (7*L/8) := by
  apply gap_lt_density_relative hL
  have hs : (330:ℝ)^2 ≤ L^2 := by nlinarith
  nlinarith

/-- Dusart's x/log^3(x) interval compared on the requested closed log window. -/
theorem gap_lt_log_cubed_relative {L : ℝ} (hL : 330 ≤ L) (hL' : L ≤ 331) :
    Real.exp (4*L/5) < Real.exp L/L^3 := by
  apply gap_lt_fixed_relative hL (by positivity)
  have hc : L^3 ≤ (331:ℝ)^3 := by gcongr
  norm_num at hc
  linarith

/-- All Table2 denominator constraints are proved from the actual registered
table values by ordinary finite kernel arithmetic. -/
theorem table2_delta_bounds {n D : ℕ} (h : (n,D) ∈ KadiriLumley.v1.table2ExpRows) :
    1 < D ∧ D ≤ 60000000000000 := by
  have ha : KadiriLumley.v1.table2ExpRows.all
      (fun q => decide (1 < q.2 ∧ q.2 ≤ 60000000000000)) = true := by decide
  exact of_decide_eq_true ((List.all_eq_true.mp ha) (n,D) h)

theorem gap_lt_table2_forward {n D : ℕ} (h : (n,D) ∈ KadiriLumley.v1.table2ExpRows)
    {L : ℝ} (hL : 330 ≤ L) :
    Real.exp (4*L/5) < Real.exp L/((D:ℝ)-1) := by
  have hb := table2_delta_bounds h
  apply gap_lt_fixed_relative hL
  · have hD : (1:ℝ) < D := by exact_mod_cast hb.1
    linarith
  · have hD : (D:ℝ) ≤ 60000000000000 := by exact_mod_cast hb.2
    linarith

/-- Every remaining fixed forward denominator, including the first Table2 row
and the separately named backward rows after Delta-1 conversion. -/
def registeredFixedDenominators : List ℕ :=
  [16,10000000000000,30000000000000,40000000000000,60000000000000,
    28313999,1946282820,1966196910,36082897]

theorem gap_lt_registered_fixed {D : ℕ} (hD : D ∈ registeredFixedDenominators)
    {L : ℝ} (hL : 330 ≤ L) :
    Real.exp (4*L/5) < Real.exp L/(D:ℝ) := by
  have ha : registeredFixedDenominators.all
      (fun q => decide (0 < q ∧ q ≤ 60000000000000)) = true := by decide
  have hb : 0 < D ∧ D ≤ 60000000000000 :=
    of_decide_eq_true ((List.all_eq_true.mp ha) D hD)
  exact gap_lt_fixed_relative hL (by exact_mod_cast hb.1) (by exact_mod_cast hb.2)

theorem gap_lt_registered_density {L : ℝ} (hL : 330 ≤ L) :
    Real.exp (4*L/5) < (264/10000:ℝ)*Real.exp (7*L/8) ∧
    Real.exp (4*L/5) < (345/10000:ℝ)*Real.exp (7*L/8) ∧
    Real.exp (4*L/5) < (2/25:ℝ)*Real.exp (7*L/8) := by
  exact ⟨gap_lt_density_relative hL (by norm_num),
    gap_lt_density_relative hL (by norm_num),gap_lt_density_relative hL (by norm_num)⟩
/-- Backward-to-forward transport keeps the source endpoint convention explicit. -/
theorem backward_interval_implies_forward
    {x0 x D : ℝ} (hx : 0 ≤ x) (hD : 1 < D) (hxx0 : x0 ≤ x)
    (hsource : ∀ y : ℝ, x0 ≤ y →
      IEANTN.HasPrimeInInterval (y*(1-1/D)) (y/D)) :
    IEANTN.HasPrimeInInterval x (x/(D-1)) := by
  have hD0 : D ≠ 0 := by linarith
  have hD1 : D-1 ≠ 0 := by linarith
  let y := x+x/(D-1)
  have hyx : x ≤ y := by
    have hd : 0 ≤ x/(D-1) := div_nonneg hx (by linarith)
    dsimp [y]
    linarith
  have hh := hsource y (hxx0.trans hyx)
  have ha : y*(1-1/D)=x := by dsimp [y];field_simp [hD0,hD1];ring
  have hb : y/D=x/(D-1) := by dsimp [y];field_simp [hD0,hD1];ring
  rw [ha,hb] at hh
  exact hh

theorem table2_exponent_bounds {n D : ℕ} (h : (n,D) ∈ KadiriLumley.v1.table2ExpRows) :
    n ≤ 330 := by
  have ha : KadiriLumley.v1.table2ExpRows.all
      (fun q => decide (q.1 ≤ 330)) = true := by decide
  exact of_decide_eq_true ((List.all_eq_true.mp ha) (n,D) h)

theorem exp_ray_ge_four_e18 {L : ℝ} (hL : 330 ≤ L) :
    (4*(10:ℝ)^18) ≤ Real.exp L := by
  have hh := exp_fifth_gt_max_denominator hL
  have hs : (Real.exp (L/5))^2 = Real.exp (2*L/5) := by
    rw [pow_two,←Real.exp_add];congr 1;ring
  have hm : Real.exp (2*L/5) ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
  rw [←hs] at hm
  norm_num
  nlinarith

#print axioms gap_lt_fixed_relative
#print axioms gap_lt_density_relative
#print axioms gap_lt_log_cubed_relative
#print axioms gap_lt_table2_forward
#print axioms gap_lt_registered_fixed
end DirectIntervalA
