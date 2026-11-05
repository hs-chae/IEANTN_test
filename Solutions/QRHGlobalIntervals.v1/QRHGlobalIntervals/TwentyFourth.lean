/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import QRHGlobalIntervals.Sixteenth
import IEANTN.Nodes.BKLNW.v1.Conclusions

/-!
# Under QRH, every interval `(x, x + x^{7/8}/24]` with `x ≥ 1339` contains a prime

The constant `1/24` is the smallest of the form `1/n` that the network's tables reach: the QRH
frontier row `(160, 0.02069)` needs `c > 2·0.0207 = 0.0414`, and no Kadiri–Lumley row reaches past
`e^{148}` at this constant. The gap `[e^{128}, e^{160}]` is closed by BKLNW's Table 8 (`ψ` within
`2.45299·10⁻¹²·x` from `e^{100}`) and its Corollary 5.1 (`ψ − θ`), which together give
`Eθ ≤ 2.4530·10⁻¹²` on `[e^{100}, e^{25000}]` (`eTheta_le_bklnw`).

| range | input | check |
|---|---|---|
| `1339 ≤ x < 90583` | a 355-rung ladder | `(p' − p)^8·24^8 ≤ p^7`, kernel-decided; `norm_num` primality |
| `90583 ≤ x ≤ e^{44}` | `Dusart2018.v1.proposition_5_4` | `e^4 ≤ 11³/24`, `e^6 ≤ 32³/24` |
| `e^{44} ≤ x ≤ e^{64}` | Kadiri–Lumley row `x ≥ 4·10^18` | `e^8 ≤ (Δ − 1)/24` |
| `e^{64} ≤ x ≤ e^{128}` | Kadiri–Lumley row `x ≥ e^60` | `e^{16} ≤ (Δ − 1)/24` |
| `e^{128} ≤ x ≤ e^{160}` | BKLNW Table 8 row `(100, 2.45299e-12)`, Corollary 5.1 row `(50, ·)` | `2·2.4530e-12·e^{20} < (1 − 2.4530e-12)/24` |
| `x ≥ e^{160}` | `QRHPropagation.v2.theta_frontier`, row `(160, 0.02069)` | `0.0207·(2 + e^{-20}/24) < 1/24` |

The threshold is sharp among integers: there is no prime in `(1338, 1338 + 1338^{7/8}/24]`
(`not_twentyfourth_1338`), since `1338^{7/8}/24 < 22.67` and `1339, …, 1360` are composite.
The same check gives the sharp integer threshold `1328` for `1/16` (`sixteenth_interval_sharp`).
-/

namespace QRHGlobal

open Real IEANTN

set_option maxRecDepth 100000

/-- The ladder for `c = 1/24`, from `1339` (not a prime; only the later rungs must be) past
Dusart's `89693`. Greedy: each rung is the largest prime allowed by the step condition. -/
def ladder24 : List ℕ := [
    1339, 1361, 1381, 1399, 1409, 1429, 1453, 1471, 1493, 1511, 1531, 1553,
    1571, 1597, 1621, 1637, 1663, 1669, 1693, 1709, 1733, 1759, 1787, 1811,
    1831, 1847, 1877, 1907, 1933, 1951, 1979, 2003, 2029, 2053, 2083, 2113,
    2143, 2161, 2179, 2213, 2243, 2273, 2309, 2341, 2377, 2411, 2447, 2477,
    2503, 2539, 2557, 2593, 2633, 2671, 2711, 2753, 2791, 2833, 2861, 2903,
    2939, 2971, 3011, 3049, 3089, 3121, 3167, 3209, 3257, 3301, 3347, 3391,
    3433, 3469, 3517, 3559, 3607, 3659, 3709, 3761, 3803, 3853, 3907, 3947,
    4003, 4057, 4111, 4159, 4219, 4273, 4327, 4373, 4423, 4483, 4547, 4603,
    4663, 4729, 4793, 4861, 4931, 4999, 5059, 5119, 5189, 5261, 5333, 5407,
    5483, 5557, 5623, 5701, 5779, 5857, 5939, 6011, 6091, 6173, 6257, 6343,
    6427, 6491, 6581, 6661, 6737, 6829, 6917, 7001, 7079, 7159, 7253, 7351,
    7451, 7549, 7649, 7753, 7853, 7951, 8053, 8161, 8269, 8377, 8467, 8573,
    8681, 8783, 8893, 9011, 9127, 9241, 9349, 9473, 9587, 9697, 9817, 9941,
    10069, 10193, 10321, 10453, 10589, 10723, 10861, 10993, 11131, 11273, 11411, 11551,
    11699, 11839, 11987, 12119, 12269, 12421, 12577, 12721, 12853, 13009, 13171, 13337,
    13499, 13669, 13841, 14011, 14177, 14347, 14519, 14699, 14879, 15061, 15241, 15427,
    15619, 15809, 16001, 16193, 16381, 16573, 16763, 16963, 17167, 17377, 17581, 17791,
    17989, 18199, 18413, 18637, 18859, 19087, 19309, 19543, 19777, 20011, 20249, 20483,
    20719, 20963, 21211, 21433, 21683, 21937, 22193, 22453, 22717, 22973, 23227, 23497,
    23773, 24049, 24329, 24611, 24889, 25171, 25463, 25759, 26053, 26357, 26647, 26953,
    27259, 27551, 27851, 28163, 28477, 28793, 29123, 29453, 29789, 30119, 30449, 30781,
    31123, 31477, 31817, 32173, 32537, 32887, 33247, 33623, 33997, 34381, 34763, 35153,
    35543, 35933, 36319, 36721, 37123, 37537, 37951, 38371, 38791, 39217, 39631, 40063,
    40499, 40939, 41389, 41843, 42299, 42751, 43207, 43669, 44131, 44587, 45061, 45541,
    46027, 46523, 47017, 47527, 48029, 48541, 49057, 49559, 50093, 50627, 51169, 51713,
    52267, 52817, 53381, 53951, 54521, 55079, 55663, 56249, 56843, 57427, 58031, 58631,
    59243, 59863, 60493, 61129, 61757, 62401, 63031, 63689, 64333, 65003, 65677, 66359,
    67049, 67741, 68443, 69151, 69859, 70573, 71293, 72019, 72739, 73483, 74231, 74959,
    75721, 76493, 77269, 78049, 78839, 79633, 80429, 81239, 82051, 82847, 83663, 84503,
    85333, 86183, 87049, 87917, 88799, 89689, 90583]

theorem ladder24_ok : ladderOK 1 24 ladder24 = true := by decide

theorem ladder24_prime : ∀ q ∈ ladder24.tail, q.Prime := by
  simp only [ladder24, List.tail_cons, List.forall_mem_cons]
  norm_num

/-! ### `Eθ` on `[e^{100}, e^{25000}]` from BKLNW -/

/-- Each of the terms `x^{1/k − 1/3}`, `k ≥ 3`, of BKLNW's `f` is at most `1`, so `f(x)` is at
most the number of terms. -/
theorem bklnw_f_le {x : ℝ} {N : ℕ} (hx : 1 ≤ x) (hN : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    BKLNW.v1.f x ≤ N := by
  unfold BKLNW.v1.f
  calc ∑ k ∈ Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊, x ^ ((1 : ℝ) / (k : ℝ) - 1 / 3)
      ≤ ∑ _k ∈ Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        apply rpow_le_one_of_one_le_of_nonpos hx
        have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
        have : (1 : ℝ) / k ≤ 1 / 3 := by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
        linarith
    _ = ((Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).card : ℝ) := by simp
    _ ≤ N := by
        rw [Nat.card_Icc]
        exact_mod_cast (show ⌊Real.log x / Real.log 2⌋₊ + 1 - 3 ≤ N by omega)

/-- `a₂(100) ≤ 146`: both points at which `f` is evaluated have at most 145 terms. -/
theorem bklnw_a2_le : BKLNW.v1.a₂ 100 ≤ 146 := by
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hpos : 0 < Real.log 2 := by linarith
  have hn : ⌊(100 : ℝ) / Real.log 2⌋₊ ≤ 144 := by
    apply Nat.le_of_lt_succ
    rw [Nat.floor_lt (by positivity), div_lt_iff₀ hpos]
    norm_num
    nlinarith
  have h1 : BKLNW.v1.f (exp 100) ≤ 145 := by
    have := bklnw_f_le (x := exp 100) (N := 144) (one_le_exp (by norm_num))
      (by rw [log_exp]; exact hn)
    push_cast at this
    linarith
  have h2 : BKLNW.v1.f ((2 : ℝ) ^ (⌊(100 : ℝ) / Real.log 2⌋₊ + 1)) ≤ 145 := by
    have hx : (1 : ℝ) ≤ (2 : ℝ) ^ (⌊(100 : ℝ) / Real.log 2⌋₊ + 1) := one_le_pow₀ (by norm_num)
    have hfl : ⌊Real.log ((2 : ℝ) ^ (⌊(100 : ℝ) / Real.log 2⌋₊ + 1)) / Real.log 2⌋₊ ≤ 145 := by
      rw [Real.log_pow, mul_div_assoc, div_self hpos.ne', mul_one]
      rw [show ((⌊(100 : ℝ) / Real.log 2⌋₊ + 1 : ℕ) : ℝ) = ((⌊(100 : ℝ) / Real.log 2⌋₊ + 1 : ℕ) : ℝ)
        from rfl, Nat.floor_natCast]
      omega
    have := bklnw_f_le hx hfl
    push_cast at this
    linarith
  unfold BKLNW.v1.a₂
  have hmax : max (BKLNW.v1.f (exp 100)) (BKLNW.v1.f ((2 : ℝ) ^ (⌊(100 : ℝ) / Real.log 2⌋₊ + 1)))
      ≤ 145 := max_le h1 h2
  have hf0 : 0 ≤ max (BKLNW.v1.f (exp 100))
      (BKLNW.v1.f ((2 : ℝ) ^ (⌊(100 : ℝ) / Real.log 2⌋₊ + 1))) := by
    apply le_max_of_le_left
    unfold BKLNW.v1.f
    exact Finset.sum_nonneg (fun k _ => rpow_nonneg (exp_pos _).le _)
  nlinarith

/-- `38·log 10 < 100`, i.e. `10^38 < e^100`: BKLNW's high branch applies at `b = 100`. -/
theorem thirtyeight_log_ten : 38 * Real.log 10 < (2 : ℝ) * ((50 : ℕ) : ℝ) := by
  have h : (10 : ℝ) ^ 38 < exp 100 := by
    calc (10 : ℝ) ^ 38 < 2.7182818283 ^ 100 := by norm_num
      _ ≤ exp ((100 : ℕ) : ℝ) := exp_nat_ge 100
      _ = exp 100 := by norm_num
  have := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_exp] at this
  push_cast at this ⊢
  linarith

/-- **`Eθ` from BKLNW.** On `[e^{100}, e^{25000}]`, `Eθ ≤ 2.4530·10⁻¹²`: Table 8 bounds `|ψ − x|`, and
`0 ≤ ψ − θ < (1 + 1.1199·10⁻⁹)√x + a₂(100)·x^{1/3}` costs less than `10⁻²⁰` relative to `x`. -/
theorem eTheta_le_bklnw (hψ : BKLNW.v1.table8_psi_bound_above)
    (hcor : BKLNW.v1.corollary_5_1_above) :
    ∀ y : ℝ, exp 100 ≤ y → y ≤ exp 25000 → Eθ y ≤ 2.4530e-12 := by
  intro y hy1 hy2
  have hy0 : 0 < y := (exp_pos 100).trans_le hy1
  have hmem1 : ((100 : ℕ), (2.45299e-12 : ℝ)) ∈ BKLNW.v1.table8 := by
    unfold BKLNW.v1.table8
    repeat (first | exact List.mem_cons_self .. | apply List.mem_cons_of_mem)
  have hmem2 : ((50 : ℕ), (1.11990e-9 : ℝ)) ∈ BKLNW.v1.table8 := by
    unfold BKLNW.v1.table8
    repeat (first | exact List.mem_cons_self .. | apply List.mem_cons_of_mem)
  have hpsi := hψ _ hmem1 y (by simpa using hy1) hy2
  have hdiff := hcor _ hmem2 thirtyeight_log_ten y (by
    simp only [Nat.cast_ofNat]; norm_num; exact hy1)
  simp only [Nat.cast_ofNat] at hdiff
  norm_num at hdiff
  have hθψ := Chebyshev.theta_le_psi y
  -- the two lower-order terms, relative to `y`
  have hs : y ^ ((1 : ℝ) / 2) ≤ y * (1 / 10 ^ 21) := by
    have hsq : y ^ ((1 : ℝ) / 2) * y ^ ((1 : ℝ) / 2) = y := by
      rw [← rpow_add hy0]; norm_num
    have hge : exp 50 ≤ y ^ ((1 : ℝ) / 2) := by
      have : (exp 100) ^ ((1 : ℝ) / 2) ≤ y ^ ((1 : ℝ) / 2) :=
        rpow_le_rpow (exp_pos _).le hy1 (by norm_num)
      rwa [← exp_mul, show (100 : ℝ) * (1 / 2) = 50 by norm_num] at this
    have h50 : (10 : ℝ) ^ 21 ≤ exp 50 := by
      calc (10 : ℝ) ^ 21 ≤ 2.7182818283 ^ 50 := by norm_num
        _ ≤ exp ((50 : ℕ) : ℝ) := exp_nat_ge 50
        _ = exp 50 := by norm_num
    have hpos : 0 < y ^ ((1 : ℝ) / 2) := rpow_pos_of_pos hy0 _
    nlinarith
  have hc : y ^ ((1 : ℝ) / 3) ≤ y * (1 / 10 ^ 28) := by
    have hsq : y ^ ((1 : ℝ) / 3) * y ^ ((2 : ℝ) / 3) = y := by
      rw [← rpow_add hy0]; norm_num
    have hge : exp 66 ≤ y ^ ((2 : ℝ) / 3) := by
      have : (exp 100) ^ ((2 : ℝ) / 3) ≤ y ^ ((2 : ℝ) / 3) :=
        rpow_le_rpow (exp_pos _).le hy1 (by norm_num)
      rw [← exp_mul] at this
      exact (exp_le_exp.mpr (by norm_num)).trans this
    have h66 : (10 : ℝ) ^ 28 ≤ exp 66 := by
      calc (10 : ℝ) ^ 28 ≤ 2.7182818283 ^ 66 := by norm_num
        _ ≤ exp ((66 : ℕ) : ℝ) := exp_nat_ge 66
        _ = exp 66 := by norm_num
    have hpos : 0 < y ^ ((1 : ℝ) / 3) := rpow_pos_of_pos hy0 _
    nlinarith
  have ha2 := bklnw_a2_le
  have ha2' : 0 ≤ BKLNW.v1.a₂ 100 := by
    unfold BKLNW.v1.a₂
    apply mul_nonneg (by norm_num)
    apply le_max_of_le_left
    unfold BKLNW.v1.f
    exact Finset.sum_nonneg (fun k _ => rpow_nonneg (exp_pos _).le _)
  have hcube0 : 0 ≤ y ^ ((1 : ℝ) / 3) := rpow_nonneg hy0.le _
  have habs : |Chebyshev.theta y - y| ≤ 2.45299e-12 * y + (1 + 1.11990e-9) * (y * (1 / 10 ^ 21))
      + 146 * (y * (1 / 10 ^ 28)) := by
    have h1 : |Chebyshev.psi y - y| ≤ 2.45299e-12 * y := hpsi
    have h2 : Chebyshev.psi y - Chebyshev.theta y
        ≤ (1 + 1.11990e-9) * (y * (1 / 10 ^ 21)) + 146 * (y * (1 / 10 ^ 28)) := by
      have e1 : (1 + 1.11990e-9 : ℝ) * y ^ ((1 : ℝ) / 2) ≤ (1 + 1.11990e-9) * (y * (1 / 10 ^ 21)) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      have e2 : BKLNW.v1.a₂ 100 * y ^ ((1 : ℝ) / 3) ≤ 146 * (y * (1 / 10 ^ 28)) :=
        mul_le_mul ha2 hc hcube0 (by norm_num)
      linarith
    rw [abs_le] at h1 ⊢
    constructor <;> linarith
  unfold Eθ
  rw [div_le_iff₀ hy0]
  linarith

/-- The BKLNW piece for `c = 1/24`: `e^{128} ≤ x ≤ e^{160}`. -/
theorem bklnw_piece_24 (hψ : BKLNW.v1.table8_psi_bound_above)
    (hcor : BKLNW.v1.corollary_5_1_above) (hcrit : PrimeInterval.v1.eTheta_criterion) :
    ∀ x : ℝ, exp 128 ≤ x → log x ≤ 160 →
      HasPrimeInInterval x ((1 / 24 : ℝ) * x ^ ((7 : ℝ) / 8)) := by
  intro x hx hlog
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have hx1 : 1 ≤ x := (one_le_exp (by norm_num)).trans hx
  have hw0 : 0 < x ^ ((7 : ℝ) / 8) := rpow_pos_of_pos hx0 _
  set h := (1 / 24 : ℝ) * x ^ ((7 : ℝ) / 8) with hh
  have hh0 : 0 < h := by positivity
  have hwx : x ^ ((7 : ℝ) / 8) ≤ x := by
    calc x ^ ((7 : ℝ) / 8) ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := rpow_one x
  have hhx : h ≤ x := by rw [hh]; linarith
  have hxe : x ≤ exp 160 := by rw [← exp_log hx0]; exact exp_le_exp.mpr hlog
  have hbig : 2 * exp 160 ≤ exp 25000 := by
    have : exp (161 : ℝ) ≤ exp 25000 := exp_le_exp.mpr (by norm_num)
    have h2 : 2 * exp (160 : ℝ) ≤ exp 161 := by
      rw [show (161 : ℝ) = 160 + 1 by norm_num, exp_add]
      have : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
      nlinarith [exp_pos (160 : ℝ)]
    linarith
  have hE1 := eTheta_le_bklnw hψ hcor x ((exp_le_exp.mpr (by norm_num)).trans hx) (by linarith)
  have hE2 := eTheta_le_bklnw hψ hcor (x + h)
    (((exp_le_exp.mpr (by norm_num)).trans hx).trans (by linarith)) (by linarith)
  apply hcrit x h hx0 hh0
  have hE1' : x * Eθ x ≤ x * 2.4530e-12 := mul_le_mul_of_nonneg_left hE1 hx0.le
  have hE2' : (x + h) * Eθ (x + h) ≤ (x + h) * 2.4530e-12 :=
    mul_le_mul_of_nonneg_left hE2 (by linarith)
  -- x = x^{1/8}·x^{7/8} with x^{1/8} ≤ e^{20} < 4.8517·10^8
  have hsplit : x = x ^ ((1 : ℝ) / 8) * x ^ ((7 : ℝ) / 8) := by
    rw [← rpow_add hx0]; norm_num
  have hroot : x ^ ((1 : ℝ) / 8) ≤ 485166000 := by
    rw [rpow_def_of_pos hx0]
    calc exp (log x * (1 / 8)) ≤ exp ((20 : ℕ) : ℝ) := exp_le_exp.mpr (by push_cast; linarith)
      _ ≤ 2.7182818286 ^ 20 := (exp_nat_lt 20 (by norm_num)).le
      _ ≤ 485166000 := by norm_num
  have hroot0 : 0 ≤ x ^ ((1 : ℝ) / 8) := rpow_nonneg hx0.le _
  have hxle : x ≤ 485166000 * x ^ ((7 : ℝ) / 8) := by
    calc x = x ^ ((1 : ℝ) / 8) * x ^ ((7 : ℝ) / 8) := hsplit
      _ ≤ 485166000 * x ^ ((7 : ℝ) / 8) := by gcongr
  nlinarith

theorem twentyfourth_interval (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hKL : KadiriLumley.v1.table_2)
    (hψ : BKLNW.v1.table8_psi_bound_above) (hcor : BKLNW.v1.corollary_5_1_above)
    (hcrit : PrimeInterval.v1.eTheta_criterion) :
    ∀ x : ℝ, 1339 ≤ x → HasPrimeInInterval x ((1 / 24 : ℝ) * x ^ ((7 : ℝ) / 8)) := by
  intro x hx
  have hx0 : 0 < x := by linarith
  have hc : (0 : ℝ) < 1 / 24 := by norm_num
  -- the ladder
  by_cases hl : x < 90583
  · have hlast : (1339 :: ladder24.tail).getLast (List.cons_ne_nil _ _) = 90583 := by decide
    have := ladder_sound 1 24 (by norm_num) 1339 ladder24.tail ladder24_prime ladder24_ok x
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
        _ ≤ 1 / 24 * 11 ^ 3 := by norm_num
    · replace h32 := (not_le.mp h32).le
      refine dusart_piece hD (a := 32) (b := 48) (by norm_num) ?_ x (by linarith) h32 (by linarith)
      calc exp ((48 : ℝ) / 8) = exp ((6 : ℕ) : ℝ) := by norm_num
        _ ≤ 2.7182818286 ^ 6 := (exp_nat_lt 6 (by norm_num)).le
        _ ≤ 1 / 24 * 32 ^ 3 := by norm_num
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
        _ ≤ 1 / 24 * (36082898 - 1) := by norm_num
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
        _ ≤ 1 / 24 * (((1966196911 : ℕ) : ℝ) - 1) := by norm_num
  replace h128 := (not_le.mp h128).le
  -- BKLNW, log x ≤ 160
  by_cases h160 : log x ≤ 160
  · exact bklnw_piece_24 hψ hcor hcrit x (by rw [← exp_log hx0]; exact exp_le_exp.mpr h128) h160
  replace h160 := (not_le.mp h160).le
  -- QRH, the frontier row (160, 0.02069)
  have hrowθ : ((160 : ℝ), (0.02069 : ℝ)) ∈ CH2.v6.densityFrontier := by
    norm_num [CH2.v6.densityFrontier]
  have hb := hθ 160 0.02069 hrowθ
  refine interval_of_theta_power hcrit hb (by norm_num) hc ?_ x ?_
  · have he : exp (-160 / 8 : ℝ) ≤ 1 / 10 ^ 6 := by
      have h20 := exp_nat_ge 20
      rw [show (-160 / 8 : ℝ) = -((20 : ℕ) : ℝ) by norm_num, exp_neg, inv_le_comm₀ (exp_pos _)
        (by norm_num)]
      calc ((1 / 10 ^ 6 : ℝ))⁻¹ ≤ 2.7182818283 ^ 20 := by norm_num
        _ ≤ _ := h20
    nlinarith
  · rw [← exp_log hx0]; exact exp_le_exp.mpr h160

/-- Prime gaps after `1339`: the next prime after `p` is at most `p + p^{7/8}/24`. -/
theorem prime_gap_twentyfourth (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hKL : KadiriLumley.v1.table_2)
    (hψ : BKLNW.v1.table8_psi_bound_above) (hcor : BKLNW.v1.corollary_5_1_above)
    (hcrit : PrimeInterval.v1.eTheta_criterion) {p : ℕ} (h : 1339 ≤ p) :
    ∃ q : ℕ, q.Prime ∧ p < q ∧ (q : ℝ) ≤ p + (p : ℝ) ^ ((7 : ℝ) / 8) / 24 := by
  obtain ⟨q, hq, hpq, hle⟩ :=
    twentyfourth_interval hθ hD hKL hψ hcor hcrit p (by exact_mod_cast h)
  exact ⟨q, hq, by exact_mod_cast hpq, by linarith⟩

/-! ### Sharp integer thresholds -/

/-- `1/16` from `1328`: one extra rung `1328 → 1361` in front of `sixteenth_interval`. -/
theorem sixteenth_interval_sharp (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hKL : KadiriLumley.v1.table_2)
    (hcrit : PrimeInterval.v1.eTheta_criterion) :
    ∀ x : ℝ, 1328 ≤ x → HasPrimeInInterval x ((1 / 16 : ℝ) * x ^ ((7 : ℝ) / 8)) := by
  intro x hx
  by_cases h : x < 1361
  · have hok : ladderOK 1 16 [1328, 1361] = true := by decide
    have hpr : ∀ q ∈ [1361], q.Prime := by simp only [List.forall_mem_cons]; norm_num
    have := ladder_sound 1 16 (by norm_num) 1328 [1361] hpr hok x (by exact_mod_cast hx)
      (by simpa using h)
    norm_num at this ⊢
    exact this
  exact sixteenth_interval hθ hD hKL hcrit x (not_lt.mp h)

/-- No interval `(n, n + n^{7/8}/24]` with `n = 1338` contains a prime: `1338^{7/8}/24 < 23` and
`1339, …, 1360` are composite. So `1339` in `twentyfourth_interval` cannot be lowered to `1338`. -/
theorem not_twentyfourth_1338 :
    ¬ HasPrimeInInterval 1338 ((1 / 24 : ℝ) * (1338 : ℝ) ^ ((7 : ℝ) / 8)) := by
  rintro ⟨p, hp, h1, h2⟩
  have hpow : (1338 : ℝ) ^ ((7 : ℝ) / 8) < 552 := by
    have h8 : ((1338 : ℝ) ^ ((7 : ℝ) / 8)) ^ 8 < (552 : ℝ) ^ 8 := by
      rw [rpow_seven_eighths_pow_eight (by norm_num)]; norm_num
    exact lt_of_pow_lt_pow_left₀ 8 (by norm_num) h8
  have hp1 : 1338 < p := by exact_mod_cast h1
  have hp2 : p < 1361 := by
    have : (p : ℝ) < 1361 := by linarith
    exact_mod_cast this
  interval_cases p <;> norm_num at hp

/-- The same for `1/16` at `1327`: `1327^{7/8}/16 < 34` and `1328, …, 1360` are composite. -/
theorem not_sixteenth_1327 :
    ¬ HasPrimeInInterval 1327 ((1 / 16 : ℝ) * (1327 : ℝ) ^ ((7 : ℝ) / 8)) := by
  rintro ⟨p, hp, h1, h2⟩
  have hpow : (1327 : ℝ) ^ ((7 : ℝ) / 8) < 544 := by
    have h8 : ((1327 : ℝ) ^ ((7 : ℝ) / 8)) ^ 8 < (544 : ℝ) ^ 8 := by
      rw [rpow_seven_eighths_pow_eight (by norm_num)]; norm_num
    exact lt_of_pow_lt_pow_left₀ 8 (by norm_num) h8
  have hp1 : 1327 < p := by exact_mod_cast h1
  have hp2 : p < 1361 := by
    have : (p : ℝ) < 1361 := by linarith
    exact_mod_cast this
  interval_cases p <;> norm_num at hp

end QRHGlobal
