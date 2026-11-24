/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CubeDensityUniform
namespace RHOnePrime.PowerPopulation
open Real Set
set_option maxHeartbeats 0

/-- A variable admissible kernel width fills every cell. Unlike floor tiling,
there is no discarded large final fraction of the cube window. -/
theorem cube_density_070 (hf : OcticFamily) {n : ℝ} (hn : exp 8 ≤ n) :
    (7 / 10 : ℝ) * n ^ 2 / log n <
      ((QuarticWindow.primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ) := by
  have hn0 : 0 < n := (exp_pos _).trans_le hn
  have hL : 8 ≤ log n := by simpa using log_le_log (exp_pos 8) hn
  have hl0 : 0 < log n := by linarith
  have hs0 : 0 < sqrt n := sqrt_pos.mpr hn0
  have hs2 := sq_sqrt hn0.le
  have ha : exp 24 ≤ n ^ 3 := by
    have h := pow_le_pow_left₀ (exp_nonneg 8) hn 3
    simpa only [← exp_nat_mul, show (3 : ℕ) * (8 : ℝ) = 24 by norm_num] using h
  let s := sqrt n / log n
  let k : ℕ := ⌈s / 17⌉₊
  let C := 16 * s / (17 * (k : ℝ))
  let B := (51 / 16 : ℝ) * n * sqrt n * log n
  let H := 3 * n ^ 2 / (k : ℝ)
  have hs : (27 / 4 : ℝ) < s := (lt_div_iff₀ hl0).mpr (log_sqrt_cube_budget hn)
  have hspos : 0 < s := by linarith
  have hklo : s / 17 ≤ (k : ℝ) := Nat.le_ceil _
  have hkhi : (k : ℝ) < s / 17 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hkpos : 0 < (k : ℝ) := (by positivity : 0 < s / 17).trans_le hklo
  have hC : C ∈ Icc (103 / 100 : ℝ) 16 := by
    constructor
    · apply (le_div_iff₀ (by positivity : 0 < 17 * (k : ℝ))).mpr
      nlinarith
    · apply (div_le_iff₀ (by positivity : 0 < 17 * (k : ℝ))).mpr
      linarith
  have hg : 0 ≤ (8 / 9 : ℝ) * C - 18203 / 20000 := by linarith [hC.1]
  have hH : 0 < H := by dsimp [H]; positivity
  have heKC : (k : ℝ) * C = (16 / 17 : ℝ) * s := by
    dsimp [C]
    field_simp
  have heCB : C * B = H := by
    dsimp [C, B, H, s]
    field_simp
    ring_nf
    rw [hs2]
  have heKH : (k : ℝ) * H = 3 * n ^ 2 := by
    dsimp [H]
    field_simp
  have hend : n ^ 3 + (k : ℝ) * H ≤ (n + 1) ^ 3 := by rw [heKH]; nlinarith [sq_nonneg n]
  have hc : ∀ i < k, (((8 / 9 : ℝ) * C - 18203 / 20000) * n * sqrt n) <
      ((QuarticWindow.primesBetween (n ^ 3 + i * H) (n ^ 3 + (i + 1) * H)).card : ℝ) := by
    intro i hi
    have hik : (i + 1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hi
    have hstart : n ^ 3 ≤ n ^ 3 + (i : ℝ) * H :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hH.le)
    have hcellend : n ^ 3 + (i + 1 : ℝ) * H ≤ (n + 1) ^ 3 := by nlinarith
    have hstartend : n ^ 3 + (i : ℝ) * H ≤ (n + 1) ^ 3 := by nlinarith
    have hb := cube_common_cell_uniform hn hstart hstartend
    have hwidth : C * sqrt (n ^ 3 + (i : ℝ) * H) * log (n ^ 3 + (i : ℝ) * H) ≤ H := by
      have hb' : sqrt (n ^ 3 + (i : ℝ) * H) * log (n ^ 3 + (i : ℝ) * H) ≤ B := by dsimp [B]; linarith
      have hm := mul_le_mul_of_nonneg_left hb' (by linarith [hC.1] : 0 ≤ C)
      rw [heCB] at hm
      nlinarith
    have hfamily := hf C hC _ (ha.trans hstart)
    have hLu : 24 ≤ log (n ^ 3 + (i : ℝ) * H) := by
      simpa using log_le_log (exp_pos 24) (ha.trans hstart)
    have hd : 0 ≤ (21 / 5 : ℝ) / log (n ^ 3 + (i : ℝ) * H) := div_nonneg (by norm_num) (by linarith)
    have hsu : n * sqrt n ≤ sqrt (n ^ 3 + (i : ℝ) * H) := by
      have h := sqrt_le_sqrt hstart
      rw [show n ^ 3 = n ^ 2 * n by ring, sqrt_mul (sq_nonneg _), sqrt_sq hn0.le] at h
      exact h
    have hlower : (((8 / 9 : ℝ) * C - 18203 / 20000) * n * sqrt n) ≤
      ((8 / 9 : ℝ) * C - 18203 / 20000 + (21 / 5) / log (n ^ 3 + (i : ℝ) * H)) * sqrt (n ^ 3 + (i : ℝ) * H) := by
      have hm := mul_le_mul_of_nonneg_left hsu hg
      have hd' := mul_nonneg hd (sqrt_nonneg (n ^ 3 + (i : ℝ) * H))
      nlinarith
    have hsub := open_count_mono (a := n ^ 3 + (i : ℝ) * H)
      (b := n ^ 3 + (i : ℝ) * H + C * sqrt (n ^ 3 + (i : ℝ) * H) * log (n ^ 3 + (i : ℝ) * H))
      (c := n ^ 3 + (i : ℝ) * H) (d := n ^ 3 + (i + 1 : ℝ) * H)
      le_rfl (by linarith)
    have hsub' : ((QuarticWindow.primesBetween (n ^ 3 + (i : ℝ) * H)
      (n ^ 3 + (i : ℝ) * H + C * sqrt (n ^ 3 + (i : ℝ) * H) * log (n ^ 3 + (i : ℝ) * H))).card : ℝ) ≤
      ((QuarticWindow.primesBetween (n ^ 3 + (i : ℝ) * H) (n ^ 3 + (i + 1 : ℝ) * H)).card : ℝ) := by exact_mod_cast hsub
    exact hlower.trans_lt (hfamily.trans_le hsub')
  have htile := tiled_count hH.le k hc
  have hmono : ((QuarticWindow.primesBetween (n ^ 3) (n ^ 3 + (k : ℝ) * H)).card : ℝ) ≤
      ((QuarticWindow.primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ) := by exact_mod_cast open_count_mono le_rfl hend
  have hcoeff : (7 / 10 : ℝ) * s < (k : ℝ) * ((8 / 9 : ℝ) * C - 18203 / 20000) := by
    by_cases hs17 : s ≤ 17
    · have hkone : k = 1 := by
        have hk_le : k ≤ 1 := (Nat.ceil_le).mpr (by linarith)
        have hk_nat : 0 < k := by exact_mod_cast hkpos
        omega
      have hkcast : (k : ℝ) = 1 := by simp [hkone]
      rw [hkcast] at heKC ⊢
      nlinarith
    · have hs17' : 17 < s := lt_of_not_ge hs17
      have hkbound : (k : ℝ) < (2 / 17 : ℝ) * s := by linarith
      nlinarith
  have hprod := mul_lt_mul_of_pos_right hcoeff (mul_pos hn0 hs0)
  have he : (7 / 10 : ℝ) * s * (n * sqrt n) = (7 / 10 : ℝ) * n ^ 2 / log n := by
    dsimp [s]
    field_simp
    nlinarith [hs2]
  rw [he] at hprod
  have hprod' : (7 / 10 : ℝ) * n ^ 2 / log n <
      (k : ℝ) * (((8 / 9 : ℝ) * C - 18203 / 20000) * n * sqrt n) := by nlinarith
  exact hprod'.trans_le (htile.trans hmono)

theorem cube_density_070_from_sources
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {n : ℝ} (hn : exp 8 ≤ n) :
    (7 / 10 : ℝ) * n ^ 2 / log n <
      ((QuarticWindow.primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ) :=
  cube_density_070 (RHOcticPush.OptimizedFinal.strict_count_family hGreen hN hB rh) hn

theorem density_070_improves_648 {n : ℝ} (hn : exp 8 ≤ n) :
    (81 / 125 : ℝ) * n ^ 2 / log n < (7 / 10 : ℝ) * n ^ 2 / log n := by
  have hn0 : 0 < n := (exp_pos _).trans_le hn
  have hL : 8 ≤ log n := by simpa using log_le_log (exp_pos 8) hn
  have hp : 0 < n ^ 2 / log n := div_pos (sq_pos_of_pos hn0) (by linarith)
  calc
    _ = (81 / 125 : ℝ) * (n ^ 2 / log n) := by ring
    _ < (7 / 10 : ℝ) * (n ^ 2 / log n) := mul_lt_mul_of_pos_right (by norm_num) hp
    _ = _ := by ring

theorem cube_population_frontier_070 (hf : OcticFamily) {n : ℝ} (hn : exp 8 ≤ n) :
    max ((((101797 / 20000 : ℝ) + (7 / 5) / log n) * n * sqrt n))
      ((7 / 10 : ℝ) * n ^ 2 / log n) <
      ((QuarticWindow.primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ) := by
  exact max_lt (cube_population hf hn) (cube_density_070 hf hn)

theorem cube_population_frontier_070_from_sources
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {n : ℝ} (hn : exp 8 ≤ n) :
    max ((((101797 / 20000 : ℝ) + (7 / 5) / log n) * n * sqrt n))
      ((7 / 10 : ℝ) * n ^ 2 / log n) <
      ((QuarticWindow.primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ) :=
  cube_population_frontier_070 (RHOcticPush.OptimizedFinal.strict_count_family hGreen hN hB rh) hn

#print axioms cube_density_070
#print axioms cube_density_070_from_sources
end RHOnePrime.PowerPopulation
