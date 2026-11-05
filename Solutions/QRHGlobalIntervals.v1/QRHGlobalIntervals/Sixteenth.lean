/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import QRHGlobalIntervals.Global
import QRHGlobalIntervals.KadiriLumley

/-!
# Under QRH, every interval `(x, x + x^{7/8}/16]` with `x ≥ 1361` contains a prime

The constant of `global_interval` divided by 16, from `x = 1361` on. Five ranges:

| range | input | check |
|---|---|---|
| `1361 ≤ x < 90289` | a 230-rung prime ladder | `(p' - p)^8·16^8 ≤ p^7`, kernel-decided; `norm_num` primality |
| `90289 ≤ x ≤ e^{44}` | `Dusart2018.v1.proposition_5_4` | `e^4 ≤ 11³/16`, `e^6 ≤ 32³/16` |
| `e^{44} ≤ x ≤ e^{64}` | Kadiri–Lumley row `x ≥ 4·10^18`, `Δ = 36082898` | `e^8 ≤ (Δ-1)/16` |
| `e^{64} ≤ x ≤ e^{128}` | Kadiri–Lumley row `x ≥ e^60`, `Δ = 1966196911` | `e^{16} ≤ (Δ-1)/16` |
| `x ≥ e^{128}` | `QRHPropagation.v2.theta_frontier`, row `(128, 0.03013)` | `0.03014·(2 + e^{-16}/16) < 1/16` |

Below 1361 the constant `1/16` fails: the gap `1327 → 1361` is `34 > 1327^{7/8}/16 ≈ 33.7`.
-/

namespace QRHGlobal

open Real IEANTN

set_option maxRecDepth 100000

/-- The ladder for `c = 1/16`, from `1361` past Dusart's `89693`. -/
def ladder16 : List ℕ := [
    1361, 1381, 1409, 1439, 1471, 1499, 1531, 1567, 1601, 1637, 1669, 1709,
    1747, 1789, 1831, 1873, 1913, 1951, 1997, 2039, 2087, 2137, 2179, 2221,
    2273, 2311, 2357, 2411, 2467, 2521, 2579, 2633, 2693, 2753, 2803, 2861,
    2927, 2971, 3037, 3089, 3137, 3203, 3271, 3343, 3413, 3469, 3547, 3623,
    3701, 3779, 3863, 3947, 4027, 4111, 4201, 4289, 4373, 4463, 4549, 4643,
    4733, 4831, 4933, 5039, 5147, 5237, 5347, 5449, 5563, 5669, 5783, 5903,
    6011, 6133, 6257, 6379, 6491, 6619, 6737, 6871, 7013, 7151, 7297, 7433,
    7583, 7727, 7883, 8039, 8191, 8353, 8521, 8689, 8863, 9029, 9209, 9391,
    9551, 9739, 9931, 10111, 10303, 10501, 10691, 10891, 11093, 11299, 11503, 11719,
    11941, 12163, 12391, 12619, 12853, 13099, 13339, 13591, 13841, 14087, 14347, 14593,
    14867, 15139, 15413, 15683, 15973, 16267, 16567, 16871, 17183, 17497, 17807, 18133,
    18461, 18797, 19139, 19483, 19819, 20177, 20533, 20903, 21277, 21649, 22037, 22409,
    22807, 23209, 23609, 24023, 24443, 24859, 25261, 25703, 26153, 26597, 27061, 27529,
    28001, 28477, 28961, 29453, 29959, 30469, 30983, 31513, 32051, 32587, 33119, 33679,
    34231, 34807, 35393, 35983, 36587, 37201, 37813, 38431, 39047, 39679, 40289, 40949,
    41627, 42307, 43003, 43711, 44417, 45139, 45869, 46601, 47353, 48121, 48889, 49681,
    50461, 51263, 52081, 52903, 53731, 54583, 55441, 56311, 57203, 58111, 59029, 59957,
    60901, 61861, 62827, 63809, 64793, 65789, 66809, 67843, 68897, 69959, 71039, 72109,
    73189, 74311, 75437, 76579, 77747, 78929, 80111, 81331, 82567, 83813, 85081, 86357,
    87649, 88969, 90289]

theorem ladder16_ok : ladderOK 1 16 ladder16 = true := by decide

theorem ladder16_prime : ∀ q ∈ ladder16.tail, q.Prime := by
  simp only [ladder16, List.tail_cons, List.forall_mem_cons]
  norm_num

theorem exp_nat_ge (n : ℕ) : (2.7182818283 : ℝ) ^ n ≤ exp (n : ℝ) := by
  have h := Real.exp_one_gt_d9
  rw [show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) h.le n

theorem sixteenth_interval (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hKL : KadiriLumley.v1.table_2)
    (hcrit : PrimeInterval.v1.eTheta_criterion) :
    ∀ x : ℝ, 1361 ≤ x → HasPrimeInInterval x ((1 / 16 : ℝ) * x ^ ((7 : ℝ) / 8)) := by
  intro x hx
  have hx0 : 0 < x := by linarith
  have hc : (0 : ℝ) < 1 / 16 := by norm_num
  -- the ladder
  by_cases hl : x < 90289
  · have hlast : (1361 :: ladder16.tail).getLast (List.cons_ne_nil _ _) = 90289 := by decide
    have := ladder_sound 1 16 (by norm_num) 1361 ladder16.tail ladder16_prime ladder16_ok x
      (by exact_mod_cast hx) (by rw [hlast]; exact_mod_cast hl)
    norm_num at this ⊢
    exact this
  replace hl := not_lt.mp hl
  have h11 : 11 ≤ log x := eleven_le_log (by linarith)
  -- Dusart, log x ≤ 44
  by_cases h44 : log x ≤ 44
  · by_cases h32 : log x ≤ 32
    · refine dusart_piece hD (a := 11) (b := 32) (by norm_num) ?_ x (by linarith) h11 h32
      calc exp ((32 : ℝ) / 8) = exp ((4 : ℕ) : ℝ) := by norm_num
        _ ≤ 2.7182818286 ^ 4 := (exp_nat_lt 4 (by norm_num)).le
        _ ≤ 1 / 16 * 11 ^ 3 := by norm_num
    · replace h32 := (not_le.mp h32).le
      refine dusart_piece hD (a := 32) (b := 48) (by norm_num) ?_ x (by linarith) h32 (by linarith)
      calc exp ((48 : ℝ) / 8) = exp ((6 : ℕ) : ℝ) := by norm_num
        _ ≤ 2.7182818286 ^ 6 := (exp_nat_lt 6 (by norm_num)).le
        _ ≤ 1 / 16 * 32 ^ 3 := by norm_num
  replace h44 := (not_le.mp h44).le
  have hroot : x ^ ((1 : ℝ) / 8) = exp (log x / 8) := by
    rw [rpow_def_of_pos hx0]; ring_nf
  -- Kadiri–Lumley, the 4·10^18 row, log x ≤ 64
  by_cases h64 : log x ≤ 64
  · have hrow := hKL.1
    refine kl_piece (X := 4 * 10 ^ 18) (Δ := 36082898) (fun y hy => hrow y hy) (by norm_num) hc x
      ?_ hx0 ?_
    · have h44e : (4 * 10 ^ 18 : ℝ) ≤ exp 44 := by
        calc (4 * 10 ^ 18 : ℝ) ≤ 2.7182818283 ^ 44 := by norm_num
          _ ≤ exp ((44 : ℕ) : ℝ) := exp_nat_ge 44
          _ = exp 44 := by norm_num
      have : exp 44 ≤ x := by rw [← exp_log hx0]; exact exp_le_exp.mpr h44
      linarith
    · rw [hroot]
      calc exp (log x / 8) ≤ exp ((8 : ℕ) : ℝ) := exp_le_exp.mpr (by push_cast; linarith)
        _ ≤ 2.7182818286 ^ 8 := (exp_nat_lt 8 (by norm_num)).le
        _ ≤ 1 / 16 * (36082898 - 1) := by norm_num
  replace h64 := (not_le.mp h64).le
  -- Kadiri–Lumley, the e^60 row, log x ≤ 128
  by_cases h128 : log x ≤ 128
  · have hrow : ∀ y : ℝ, exp 60 ≤ y →
        ∃ p : ℕ, Nat.Prime p ∧ y * (1 - 1 / ((1966196911 : ℕ) : ℝ)) < p ∧ (p : ℝ) < y := by
      intro y hy
      have hmem : (60, 1966196911) ∈ KadiriLumley.v1.table2ExpRows := by
        unfold KadiriLumley.v1.table2ExpRows
        repeat (first | exact List.mem_cons_self .. | apply List.mem_cons_of_mem)
      exact hKL.2 60 1966196911 hmem y (by simpa using hy)
    refine kl_piece (X := exp 60) (Δ := (1966196911 : ℕ)) hrow (by norm_num) hc x ?_ hx0 ?_
    · rw [← exp_log hx0]; exact exp_le_exp.mpr (by linarith)
    · rw [hroot]
      calc exp (log x / 8) ≤ exp ((16 : ℕ) : ℝ) := exp_le_exp.mpr (by push_cast; linarith)
        _ ≤ 2.7182818286 ^ 16 := (exp_nat_lt 16 (by norm_num)).le
        _ ≤ 1 / 16 * (((1966196911 : ℕ) : ℝ) - 1) := by norm_num
  replace h128 := (not_le.mp h128).le
  -- QRH, the frontier row (128, 0.03013)
  have hrowθ : ((128 : ℝ), (0.03013 : ℝ)) ∈ CH2.v6.densityFrontier := by
    norm_num [CH2.v6.densityFrontier]
  have hb := hθ 128 0.03013 hrowθ
  refine interval_of_theta_power hcrit hb (by norm_num) hc ?_ x ?_
  · have he : exp (-128 / 8 : ℝ) ≤ 1 / 10 ^ 6 := by
      have h16 := exp_nat_ge 16
      rw [show (-128 / 8 : ℝ) = -((16 : ℕ) : ℝ) by norm_num, exp_neg, inv_le_comm₀ (exp_pos _)
        (by norm_num)]
      calc ((1 / 10 ^ 6 : ℝ))⁻¹ ≤ 2.7182818283 ^ 16 := by norm_num
        _ ≤ _ := h16
    nlinarith
  · rw [← exp_log hx0]; exact exp_le_exp.mpr h128

/-- Prime gaps after `1361`: the next prime after `p` is at most `p + p^{7/8}/16`. -/
theorem prime_gap_sixteenth (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hKL : KadiriLumley.v1.table_2)
    (hcrit : PrimeInterval.v1.eTheta_criterion) {p : ℕ} (_hp : p.Prime) (h : 1361 ≤ p) :
    ∃ q : ℕ, q.Prime ∧ p < q ∧ (q : ℝ) ≤ p + (p : ℝ) ^ ((7 : ℝ) / 8) / 16 := by
  obtain ⟨q, hq, hpq, hle⟩ := sixteenth_interval hθ hD hKL hcrit p (by exact_mod_cast h)
  exact ⟨q, hq, by exact_mod_cast hpq, by linarith⟩

end QRHGlobal
