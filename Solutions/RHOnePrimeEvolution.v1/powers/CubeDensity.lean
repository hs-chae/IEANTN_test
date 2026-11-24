/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PowerPartition
namespace RHOnePrime.PowerPopulation
open Real Set
set_option maxHeartbeats 0

lemma log_sqrt_partition_budget {x : ℝ} (hx : exp 16 ≤ x) :
    180 * log x < sqrt x := by
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have hL : 16 ≤ log x := by simpa using log_le_log (exp_pos 16) hx
  let v := log x - 16
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have he4 : (217 / 4 : ℝ) ≤ exp 4 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 12
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have he8 : (47089 / 16 : ℝ) ≤ exp 8 := by
    rw [show (8 : ℝ) = 4 + 4 by norm_num, exp_add]
    nlinarith [exp_pos 4]
  have hev : 1 + v / 2 ≤ exp (v / 2) := by linarith [add_one_le_exp (v / 2)]
  have he : exp (log x / 2) = exp 8 * exp (v / 2) := by
    rw [← exp_add]
    dsimp [v]
    congr 1
    ring
  have hs : sqrt x = exp (log x / 2) := by
    rw [sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  rw [hs, he]
  have hprod := mul_le_mul he8 hev (by linarith : 0 ≤ 1 + v / 2) (exp_nonneg 8)
  dsimp [v] at hprod
  linarith

/-- One common cell length bounds every C=16 short window inside the cube. -/
lemma cube_common_cell {n u : ℝ} (hn : exp 16 ≤ n)
    (hu : n ^ 3 ≤ u) (hub : u ≤ (n + 1) ^ 3) :
    16 * sqrt u * log u ≤ 64 * n * sqrt n * log n := by
  have hn0 : 0 < n := (exp_pos _).trans_le hn
  have hn16 : 16 ≤ n := by linarith [add_one_le_exp (16 : ℝ)]
  have hL : 16 ≤ log n := by simpa using log_le_log (exp_pos 16) hn
  have hu0 : 0 < u := (pow_pos hn0 3).trans_le hu
  have hstep : n + 1 ≤ (17 / 16 : ℝ) * n := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ n + 1) hstep 3
  have hpow : (n + 1) ^ 3 ≤ (81 / 64 : ℝ) * n ^ 3 := by nlinarith [pow_pos hn0 3]
  have hs : sqrt u ≤ (9 / 8 : ℝ) * n * sqrt n := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    calc
      u ≤ (81 / 64 : ℝ) * n ^ 3 := hub.trans hpow
      _ = ((9 / 8 : ℝ) * n * sqrt n) ^ 2 := by
        calc
          _ = (81 / 64 : ℝ) * n ^ 2 * n := by ring
          _ = (81 / 64 : ℝ) * n ^ 2 * (sqrt n) ^ 2 := by rw [sq_sqrt hn0.le]
          _ = _ := by ring
  have htwo : n + 1 ≤ 2 * n := by linarith
  have hlogstep := log_le_log (by positivity : 0 < n + 1) htwo
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne'] at hlogstep
  have hlogtwo : log (2 : ℝ) ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlu := log_le_log hu0 hub
  rw [log_pow] at hlu
  have hl : log u ≤ (32 / 9 : ℝ) * log n := by norm_num at hlu; linarith
  have hnon : 0 ≤ log u := by
    have hn1 : 1 ≤ n := by linarith
    have h1 : 1 ≤ u := (show (1 : ℝ) ≤ n ^ 3 by nlinarith [sq_nonneg (n-1)]).trans hu
    exact log_nonneg h1
  have hm := mul_le_mul hs hl hnon (by positivity : 0 ≤ (9 / 8 : ℝ) * n * sqrt n)
  nlinarith

/-- Disjoint-window amplification gives the natural n²/log(n) scale,
with a conservative explicit coefficient and a whole-real-ray onset. -/
theorem cube_density_half (hf : OcticFamily) {n : ℝ} (hn : exp 16 ≤ n) :
    n ^ 2 / (2 * log n) <
      ((QuarticWindow.primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ) := by
  have hn0 : 0 < n := (exp_pos _).trans_le hn
  have hL : 16 ≤ log n := by simpa using log_le_log (exp_pos 16) hn
  have hl0 : 0 < log n := by linarith
  have hs0 : 0 < sqrt n := sqrt_pos.mpr hn0
  have hs2 := sq_sqrt hn0.le
  have h8 : exp 8 ≤ n := (exp_le_exp.mpr (by norm_num : (8 : ℝ) ≤ 16)).trans hn
  have ha : exp 24 ≤ n ^ 3 := by
    have h := pow_le_pow_left₀ (exp_nonneg 8) h8 3
    simpa only [← exp_nat_mul, show (3 : ℕ) * (8 : ℝ) = 24 by norm_num] using h
  let H := 64 * n * sqrt n * log n
  let t := 3 * n ^ 2 / H
  let k : ℕ := ⌊t⌋₊
  have hH : 0 < H := by dsimp [H]; positivity
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht8 : 8 ≤ t := by
    apply (le_div_iff₀ hH).mpr
    have hbudget := log_sqrt_partition_budget hn
    have hm := mul_lt_mul_of_pos_left hbudget (by positivity : 0 < 3 * n * sqrt n)
    dsimp [H]
    nlinarith [mul_pos hn0 hs0, mul_pos (mul_pos hn0 hs0) hl0]
  have hklo : (7 / 8 : ℝ) * t ≤ (k : ℝ) := by
    have h := Nat.sub_one_lt_floor t
    dsimp [k]
    linarith
  have hkhi : (k : ℝ) * H ≤ 3 * n ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (Nat.floor_le ht0) hH.le
    dsimp [k, t] at *
    exact h.trans_eq (div_mul_cancel₀ _ hH.ne')
  have hend : n ^ 3 + (k : ℝ) * H ≤ (n + 1) ^ 3 := by nlinarith [sq_nonneg n]
  have hc : ∀ i < k, 13 * n * sqrt n <
      ((QuarticWindow.primesBetween (n ^ 3 + i * H) (n ^ 3 + (i + 1) * H)).card : ℝ) := by
    intro i hi
    have hik : (i + 1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hi
    have hstart : n ^ 3 ≤ n ^ 3 + (i : ℝ) * H :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hH.le)
    have hcellend : n ^ 3 + (i + 1 : ℝ) * H ≤ (n + 1) ^ 3 := by nlinarith
    have hstartend : n ^ 3 + (i : ℝ) * H ≤ (n + 1) ^ 3 := by nlinarith
    have hb := cube_common_cell hn hstart hstartend
    have hfamily := family_sixteen hf (ha.trans hstart)
    have hs : n * sqrt n ≤ sqrt (n ^ 3 + (i : ℝ) * H) := by
      have h := sqrt_le_sqrt hstart
      rw [show n ^ 3 = n ^ 2 * n by ring, sqrt_mul (sq_nonneg _), sqrt_sq hn0.le] at h
      exact h
    have hsub := open_count_mono (a := n ^ 3 + (i : ℝ) * H)
      (b := n ^ 3 + (i : ℝ) * H + 16 * sqrt (n ^ 3 + (i : ℝ) * H) * log (n ^ 3 + (i : ℝ) * H))
      (c := n ^ 3 + (i : ℝ) * H) (d := n ^ 3 + (i + 1 : ℝ) * H)
      le_rfl (by dsimp [H] at *; linarith)
    have hsub' : ((QuarticWindow.primesBetween (n ^ 3 + (i : ℝ) * H)
      (n ^ 3 + (i : ℝ) * H + 16 * sqrt (n ^ 3 + (i : ℝ) * H) * log (n ^ 3 + (i : ℝ) * H))).card : ℝ) ≤
      ((QuarticWindow.primesBetween (n ^ 3 + (i : ℝ) * H) (n ^ 3 + (i + 1 : ℝ) * H)).card : ℝ) := by exact_mod_cast hsub
    exact (by nlinarith : 13 * n * sqrt n ≤ 13 * sqrt (n ^ 3 + (i : ℝ) * H)).trans_lt (hfamily.trans_le hsub')
  have htile := tiled_count hH.le k hc
  have hmono : ((QuarticWindow.primesBetween (n ^ 3) (n ^ 3 + (k : ℝ) * H)).card : ℝ) ≤
      ((QuarticWindow.primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ) := by
    exact_mod_cast open_count_mono le_rfl hend
  have hcoeff := mul_le_mul_of_nonneg_right hklo (by positivity : 0 ≤ 13 * n * sqrt n)
  have heq : ((7 / 8 : ℝ) * t) * (13 * n * sqrt n) =
      (273 / 512 : ℝ) * n ^ 2 / log n := by
    dsimp [t, H]
    field_simp
    ring
  rw [heq] at hcoeff
  have hstrict : n ^ 2 / (2 * log n) < (273 / 512 : ℝ) * n ^ 2 / log n := by
    have hp : 0 < n ^ 2 / log n := div_pos (sq_pos_of_pos hn0) hl0
    calc
      n ^ 2 / (2 * log n) = (1 / 2 : ℝ) * (n ^ 2 / log n) := by ring
      _ < (273 / 512 : ℝ) * (n ^ 2 / log n) := mul_lt_mul_of_pos_right (by norm_num) hp
      _ = _ := by ring
  exact hstrict.trans_le (hcoeff.trans (htile.trans hmono))

theorem cube_density_half_from_sources
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {n : ℝ} (hn : exp 16 ≤ n) :
    n ^ 2 / (2 * log n) <
      ((QuarticWindow.primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ) :=
  cube_density_half (RHOcticPush.OptimizedFinal.strict_count_family hGreen hN hB rh) hn

#print axioms cube_common_cell
#print axioms cube_density_half
#print axioms cube_density_half_from_sources
end RHOnePrime.PowerPopulation
