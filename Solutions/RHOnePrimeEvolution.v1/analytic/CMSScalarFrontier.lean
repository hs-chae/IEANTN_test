/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import Mathlib

/-! Scalar consequences of a CMS-style obstruction inequality. These theorems
prove no prime-existence statement by themselves. Source inequality (6.16), its
actual kernel constant and interval geometry must be attached separately.
The variable `m` denotes sqrt(a)*(2*pi*Delta), and `z` denotes
log(1/(2*pi*Delta)). No numerical evaluation axiom is used here. -/
namespace RHOnePrime.CMSScalar
open Real
set_option maxHeartbeats 0

/-- A direct proof of the monotonicity used to extend endpoint certificates to
an entire real interval. No sample grid is promoted to continuum coverage. -/
theorem log_sub_linear_antitone {a d L B : ℝ}
    (ha : 0 < a) (hL : 0 < L) (hLB : L ≤ B) (hd : 1 ≤ d * L) :
    log (a * B) - d * B ≤ log (a * L) - d * L := by
  have hB : 0 < B := hL.trans_le hLB
  have hj := Real.log_le_sub_one_of_pos (div_pos hB hL)
  have hr : (B / L - 1) ≤ d * (B - L) := by
    calc
      B / L - 1 = (B - L) * (1 / L) := by field_simp
      _ ≤ (B - L) * d := mul_le_mul_of_nonneg_left
        ((div_le_iff₀ hL).mpr (by simpa [mul_comm] using hd))
        (sub_nonneg.mpr hLB)
      _ = d * (B - L) := mul_comm _ _
  have he : log (a * B) - log (a * L) = log (B / L) := by
    rw [Real.log_mul ha.ne' hB.ne', Real.log_mul ha.ne' hL.ne',
      Real.log_div hB.ne' hL.ne']
    ring
  linarith

noncomputable def jFloor : ℝ := 2281 / 2000
noncomputable def effectiveCost (c : ℝ) : ℝ := (1 - jFloor * c) / 2
noncomputable def margin (c L : ℝ) : ℝ :=
  log ((4 / 15 : ℝ) * L) - effectiveCost c * L - 117 / 100

/-- Conditional solely on the three explicit scalar bounds, the CMS obstruction
cannot hold whenever the displayed margin is positive. This is not labelled a
source theorem or an RH theorem. The 1.17 budget exceeds 1.16+0.001*jFloor. -/
theorem obstruction_impossible {c L J m z : ℝ}
    (hJ : jFloor ≤ J) (hm0 : 0 ≤ m)
    (hm : c * L / 2 - 1 / 1000 ≤ m)
    (hz : z ≤ L / 2 - log ((4 / 15 : ℝ) * L))
    (hmargin : 0 < margin c L) : ¬ (J * m ≤ z + 29 / 25) := by
  intro hob
  have hj0 : 0 ≤ jFloor := by norm_num [jFloor]
  have h1 := mul_le_mul_of_nonneg_right hJ hm0
  have h2 := mul_le_mul_of_nonneg_left hm hj0
  unfold margin effectiveCost at hmargin
  norm_num [jFloor] at *
  nlinarith

/-- One exact endpoint bound proves positivity on the whole real slab. -/
theorem margin_positive_on_slab {c A B L : ℝ}
    (hA : 0 < A) (hAL : A ≤ L) (hLB : L ≤ B)
    (hd : 1 ≤ effectiveCost c * A)
    (hB : 0 < margin c B) : 0 < margin c L := by
  have hL : 0 < L := hA.trans_le hAL
  have hd0 : 0 ≤ effectiveCost c := by nlinarith
  have hdL : 1 ≤ effectiveCost c * L := by nlinarith
  have hmono := log_sub_linear_antitone (a := (4/15 : ℝ))
    (d := effectiveCost c) (by norm_num) hL hLB hdL
  unfold margin at *
  linarith

/-- Tail fallback: using only log(4L/15)>1.17, c=.877 already defeats
an obstruction with jFloor=1.1405. Endpoint logarithm is left explicit here. -/
theorem tail_margin_positive {L : ℝ} (hL : 0 ≤ L)
    (hlog : (117 / 100 : ℝ) < log ((4 / 15 : ℝ) * L)) :
    0 < margin (877 / 1000) L := by
  unfold margin effectiveCost jFloor
  norm_num
  nlinarith

/-- A symbolic endpoint certificate reduces all logarithms at power-of-two
endpoints to Mathlib's independently proved lower bound for log(2). -/
theorem power_two_endpoint {c B : ℝ} (n : ℕ)
    (hn : 0 < n) (hB : (4 / 15 : ℝ) * B = (2 : ℝ) ^ n)
    (hnum : effectiveCost c * B + 117 / 100 < (n : ℝ) * (6931471803 / 10000000000)) :
    0 < margin c B := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : (n : ℝ) * (6931471803 / 10000000000) <
      log ((2 : ℝ) ^ n) := by
    rw [Real.log_pow]
    have hb : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    exact mul_lt_mul_of_pos_left hb hp
  unfold margin
  rw [hB]
  linarith

theorem slab_083 {L : ℝ} (hlo : 44 ≤ L) (hhi : L ≤ 60) :
    0 < margin (83 / 100) L := by
  apply margin_positive_on_slab (A := 44) (B := 60) (by norm_num) hlo hhi
  · norm_num [effectiveCost, jFloor]
  · apply power_two_endpoint 4 (by norm_num) (by norm_num)
    norm_num [effectiveCost, jFloor]

theorem slab_0844 {L : ℝ} (hlo : 60 ≤ L) (hhi : L ≤ 120) :
    0 < margin (211 / 250) L := by
  apply margin_positive_on_slab (A := 60) (B := 120) (by norm_num) hlo hhi
  · norm_num [effectiveCost, jFloor]
  · apply power_two_endpoint 5 (by norm_num) (by norm_num)
    norm_num [effectiveCost, jFloor]

theorem slab_0856 {L : ℝ} (hlo : 120 ≤ L) (hhi : L ≤ 240) :
    0 < margin (107 / 125) L := by
  apply margin_positive_on_slab (A := 120) (B := 240) (by norm_num) hlo hhi
  · norm_num [effectiveCost, jFloor]
  · apply power_two_endpoint 6 (by norm_num) (by norm_num)
    norm_num [effectiveCost, jFloor]

theorem slab_0864 {L : ℝ} (hlo : 240 ≤ L) (hhi : L ≤ 480) :
    0 < margin (108 / 125) L := by
  apply margin_positive_on_slab (A := 240) (B := 480) (by norm_num) hlo hhi
  · norm_num [effectiveCost, jFloor]
  · apply power_two_endpoint 7 (by norm_num) (by norm_num)
    norm_num [effectiveCost, jFloor]

theorem slab_087 {L : ℝ} (hlo : 480 ≤ L) (hhi : L ≤ 960) :
    0 < margin (87 / 100) L := by
  apply margin_positive_on_slab (A := 480) (B := 960) (by norm_num) hlo hhi
  · norm_num [effectiveCost, jFloor]
  · apply power_two_endpoint 8 (by norm_num) (by norm_num)
    norm_num [effectiveCost, jFloor]

theorem slab_0873 {L : ℝ} (hlo : 960 ≤ L) (hhi : L ≤ 1920) :
    0 < margin (873 / 1000) L := by
  apply margin_positive_on_slab (A := 960) (B := 1920) (by norm_num) hlo hhi
  · norm_num [effectiveCost, jFloor]
  · apply power_two_endpoint 9 (by norm_num) (by norm_num)
    norm_num [effectiveCost, jFloor]

theorem slab_0875 {L : ℝ} (hlo : 1920 ≤ L) (hhi : L ≤ 3840) :
    0 < margin (7 / 8) L := by
  apply margin_positive_on_slab (A := 1920) (B := 3840) (by norm_num) hlo hhi
  · norm_num [effectiveCost, jFloor]
  · apply power_two_endpoint 10 (by norm_num) (by norm_num)
    norm_num [effectiveCost, jFloor]

theorem slab_0876 {L : ℝ} (hlo : 3840 ≤ L) (hhi : L ≤ 7680) :
    0 < margin (219 / 250) L := by
  apply margin_positive_on_slab (A := 3840) (B := 7680) (by norm_num) hlo hhi
  · norm_num [effectiveCost, jFloor]
  · apply power_two_endpoint 11 (by norm_num) (by norm_num)
    norm_num [effectiveCost, jFloor]

theorem slab_08765 {L : ℝ} (hlo : 7680 ≤ L) (hhi : L ≤ 15360) :
    0 < margin (1753 / 2000) L := by
  apply margin_positive_on_slab (A := 7680) (B := 15360) (by norm_num) hlo hhi
  · norm_num [effectiveCost, jFloor]
  · apply power_two_endpoint 12 (by norm_num) (by norm_num)
    norm_num [effectiveCost, jFloor]

theorem tail_0877 {L : ℝ} (hL : 44 ≤ L) :
    0 < margin (877 / 1000) L := by
  apply tail_margin_positive (by linarith)
  have harg : (8 : ℝ) ≤ (4 / 15 : ℝ) * L := by linarith
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 8) harg
  have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [he] at hmono
  linarith [Real.log_two_gt_d9]

#print axioms log_sub_linear_antitone
#print axioms obstruction_impossible
#print axioms margin_positive_on_slab
#print axioms tail_margin_positive
#print axioms slab_083
#print axioms slab_0844
#print axioms slab_0856
#print axioms slab_0864
#print axioms slab_087
#print axioms slab_0873
#print axioms slab_0875
#print axioms slab_0876
#print axioms slab_08765
#print axioms tail_0877
end RHOnePrime.CMSScalar
