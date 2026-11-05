/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import QRHGlobalIntervals.Criterion
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Counting primes in `(x, x + c·x^{7/8}]`

Existence of one prime is the shape of `PrimeInterval.v1`. This file counts them, from either an
`Eθ` or an `Eπ` power bound, with both a lower and an upper bound. Writing
`w = x^{7/8}`, `h = c·w` and `N = π(x + h) − π(x)`:

* **θ route** (`count_of_theta_power`), from `Eθ ≤ C·y^{-1/8}` on `[e^L, ∞)`:
  `(c − C·(2 + c·e^{-L/8}))·w ≤ N·log(x + h)` and `N·log x ≤ (c + C·(2 + c·e^{-L/8}))·w`.
  The bridge is `θ(y) − θ(x) = Σ_{x<p≤y} log p`, between `N·log x` and `N·log y`
  (`theta_sub_bounds`).
* **π route** (`count_of_pi_power`), from `Eπ ≤ K·y^{-1/8}` on `[e^L, ∞)`, `L ≥ 1`:
  `(c − K·(2 + c·e^{-L/8}·(1 + 1/L)))·w ≤ N·log(x + h)` and `N·log x ≤ (c + K·(2 + c·e^{-L/8}))·w`.
  The bridge is `h/log(x + h) ≤ Li(x + h) − Li(x) ≤ h/log x` (`Li_sub_bounds`).

The expected count is `≈ w/log x`, so with `c = 1` the constants say what fraction of it is
guaranteed. A positive lower bound is again a prime in the interval (`interval_of_pi_power`), now
from a bound on `π` rather than on `θ`; that route is not in `PrimeInterval.v1`.
-/

namespace QRHGlobal

open Real IEANTN

/-! ### Finite bridges -/

/-- `θ(y) − θ(x)` is a sum of `log p` over the primes in `(x, y]`; there are
`π(y) − π(x)` of them, each with `x < p ≤ y`. -/
theorem theta_sub_bounds {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (primeCounting y - primeCounting x) * log x ≤ Chebyshev.theta y - Chebyshev.theta x ∧
      Chebyshev.theta y - Chebyshev.theta x ≤ (primeCounting y - primeCounting x) * log y := by
  set m := ⌊x⌋₊ with hm
  set n := ⌊y⌋₊ with hn
  have hmn : m ≤ n := Nat.floor_le_floor hxy
  have hsub : Nat.primesLE m ⊆ Nat.primesLE n := fun p hp => by
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans hmn, hp.2⟩
  set s := Nat.primesLE n \ Nat.primesLE m with hs
  have hθ : Chebyshev.theta y - Chebyshev.theta x = ∑ p ∈ s, log (p : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE y, Chebyshev.theta_eq_sum_primesLE x, ← hm, ← hn,
      ← Finset.sum_sdiff hsub]
    ring
  have hcard : (s.card : ℝ) = primeCounting y - primeCounting x := by
    rw [hs, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub),
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
    simp [IEANTN.primeCounting, hm, hn]
  have hmem : ∀ p ∈ s, x < (p : ℝ) ∧ (p : ℝ) ≤ y := by
    intro p hp
    rw [hs, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
    obtain ⟨⟨hpn, hpp⟩, hpm⟩ := hp
    have hmp : m < p := by
      by_contra hcon
      exact hpm ⟨not_lt.mp hcon, hpp⟩
    constructor
    · calc x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
        _ ≤ p := by exact_mod_cast hmp
    · calc (p : ℝ) ≤ n := by exact_mod_cast hpn
        _ ≤ y := Nat.floor_le (hx.le.trans hxy)
  rw [hθ, ← hcard]
  constructor
  · calc (s.card : ℝ) * log x = ∑ _p ∈ s, log x := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ s, log (p : ℝ) :=
          Finset.sum_le_sum (fun p hp => log_le_log hx (hmem p hp).1.le)
  · calc ∑ p ∈ s, log (p : ℝ) ≤ ∑ _p ∈ s, log y :=
          Finset.sum_le_sum (fun p hp => log_le_log (hx.trans (hmem p hp).1) (hmem p hp).2)
      _ = (s.card : ℝ) * log y := by rw [Finset.sum_const, nsmul_eq_mul]

/-- A positive count is a prime in the interval. -/
theorem hasPrimeInInterval_of_count {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h)
    (hpos : 0 < primeCounting (x + h) - primeCounting x) : HasPrimeInInterval x h := by
  set m := ⌊x⌋₊ with hm
  set n := ⌊x + h⌋₊ with hn
  have hmn : m ≤ n := Nat.floor_le_floor (by linarith)
  have hsub : Nat.primesLE m ⊆ Nat.primesLE n := fun p hp => by
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans hmn, hp.2⟩
  have hcard : ((Nat.primesLE n \ Nat.primesLE m).card : ℝ) =
      primeCounting (x + h) - primeCounting x := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub),
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
    simp [IEANTN.primeCounting, hm, hn]
  have hne : (Nat.primesLE n \ Nat.primesLE m).Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < ((Nat.primesLE n \ Nat.primesLE m).card : ℝ) := by rw [hcard]; exact hpos
    exact_mod_cast this
  obtain ⟨p, hp⟩ := hne
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
  obtain ⟨⟨hpn, hpp⟩, hpm⟩ := hp
  have hmp : m < p := by
    by_contra hcon
    exact hpm ⟨not_lt.mp hcon, hpp⟩
  refine ⟨p, hpp, ?_, ?_⟩
  · calc x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
      _ ≤ p := by exact_mod_cast hmp
  · calc (p : ℝ) ≤ n := by exact_mod_cast hpn
      _ ≤ x + h := Nat.floor_le (by linarith)

/-- `h/log(x + h) ≤ Li(x + h) − Li(x) ≤ h/log x` for `x ≥ 2`, `h ≥ 0`: `1/log` decreases. -/
theorem Li_sub_bounds {x h : ℝ} (hx : 2 ≤ x) (hh : 0 ≤ h) :
    h / log (x + h) ≤ Li (x + h) - Li x ∧ Li (x + h) - Li x ≤ h / log x := by
  have hcont : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      IntervalIntegrable (fun t : ℝ => 1 / log t) MeasureTheory.volume a b := by
    intro a b ha hab
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1])
    · intro t ht
      exact (log_pos (by linarith [ht.1])).ne'
  have hsplit : Li (x + h) - Li x = ∫ t in x..x + h, 1 / log t := by
    unfold Li
    rw [intervalIntegral.integral_interval_sub_left (hcont 2 (x + h) le_rfl (by linarith))
      (hcont 2 x le_rfl hx)]
  have hxh : x ≤ x + h := by linarith
  have hI := hcont x (x + h) hx hxh
  have hlx : 0 < log x := log_pos (by linarith)
  have hly : 0 < log (x + h) := log_pos (by linarith)
  rw [hsplit]
  constructor
  · have hm := intervalIntegral.integral_mono_on hxh
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 / log (x + h))
        MeasureTheory.volume x (x + h)) hI (fun t ht => by
          apply one_div_le_one_div_of_le (log_pos (by linarith [ht.1]))
          exact log_le_log (by linarith [ht.1]) ht.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hm
    calc h / log (x + h) = (x + h - x) * (1 / log (x + h)) := by ring
      _ ≤ _ := hm
  · have hm := intervalIntegral.integral_mono_on hxh hI
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 / log x)
        MeasureTheory.volume x (x + h)) (fun t ht => by
          apply one_div_le_one_div_of_le hlx
          exact log_le_log (by linarith) ht.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hm
    calc _ ≤ (x + h - x) * (1 / log x) := hm
      _ = h / log x := by ring

/-! ### The two routes -/

/-- Shared exponent bookkeeping: `w = x^{7/8}`, `u = x^{-1/8} ≤ e^{-L/8}`, `x·u = w`, and
`y^{7/8} ≤ w + h·u` at `y = x + h`. -/
theorem power_bookkeeping {L x h : ℝ} (hx : exp L ≤ x) (hh : 0 ≤ h) :
    let w := x ^ ((7 : ℝ) / 8)
    let u := x ^ ((7 : ℝ) / 8 - 1)
    0 < w ∧ 0 < u ∧ x * u = w ∧ u ≤ exp (-L / 8) ∧
      (x + h) * (x + h) ^ ((7 : ℝ) / 8 - 1) ≤ w + h * u := by
  intro w u
  have hx0 : 0 < x := (exp_pos L).trans_le hx
  have hLx : L ≤ log x := by simpa using log_le_log (exp_pos L) hx
  have hxu : x * u = w := by
    simp only [u, w]; rw [rpow_sub hx0, rpow_one]; field_simp
  have huL : u ≤ exp (-L / 8) := by
    simp only [u]
    rw [rpow_def_of_pos hx0]
    apply exp_le_exp.mpr
    have : log x * ((7 : ℝ) / 8 - 1) = -(log x) / 8 := by ring
    rw [this]
    linarith
  refine ⟨rpow_pos_of_pos hx0 _, rpow_pos_of_pos hx0 _, hxu, huL, ?_⟩
  have hmono : (x + h) ^ ((7 : ℝ) / 8 - 1) ≤ u :=
    rpow_le_rpow_of_nonpos hx0 (by linarith) (by norm_num)
  calc (x + h) * (x + h) ^ ((7 : ℝ) / 8 - 1) ≤ (x + h) * u :=
        mul_le_mul_of_nonneg_left hmono (by linarith)
    _ = x * u + h * u := by ring
    _ = w + h * u := by rw [hxu]

/-- **Counting from `Eθ`.** -/
theorem count_of_theta_power {C c L : ℝ} (hθ : HasPowerLogBound Eθ C 0 (7 / 8) (exp L))
    (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ x ≥ exp L,
      (c - C * (2 + c * exp (-L / 8))) * x ^ ((7 : ℝ) / 8) ≤
          (primeCounting (x + c * x ^ ((7 : ℝ) / 8)) - primeCounting x) *
            log (x + c * x ^ ((7 : ℝ) / 8)) ∧
        (primeCounting (x + c * x ^ ((7 : ℝ) / 8)) - primeCounting x) * log x ≤
          (c + C * (2 + c * exp (-L / 8))) * x ^ ((7 : ℝ) / 8) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos L).trans_le hx
  set w := x ^ ((7 : ℝ) / 8) with hw
  set h := c * w with hh
  have hw0 : 0 < w := rpow_pos_of_pos hx0 _
  have hh0 : 0 < h := by positivity
  obtain ⟨-, hu0, hxu, huL, hy⟩ := power_bookkeeping (L := L) hx hh0.le
  set u := x ^ ((7 : ℝ) / 8 - 1) with hu
  have hb1 := hθ x hx
  have hb2 := hθ (x + h) (by linarith)
  simp only [pow_zero, mul_one] at hb1 hb2
  -- endpoint errors
  have e1 : x * Eθ x ≤ C * w := by
    calc x * Eθ x ≤ x * (C * u) := mul_le_mul_of_nonneg_left hb1 hx0.le
      _ = C * (x * u) := by ring
      _ = C * w := by rw [hxu]
  have e2 : (x + h) * Eθ (x + h) ≤ C * (w + h * u) := by
    calc (x + h) * Eθ (x + h) ≤ (x + h) * (C * (x + h) ^ ((7 : ℝ) / 8 - 1)) :=
          mul_le_mul_of_nonneg_left hb2 (by linarith)
      _ = C * ((x + h) * (x + h) ^ ((7 : ℝ) / 8 - 1)) := by ring
      _ ≤ C * (w + h * u) := mul_le_mul_of_nonneg_left hy hC
  have hhu : h * u ≤ c * w * exp (-L / 8) := by
    rw [hh, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left huL hw0.le) hc.le
  have hsum : x * Eθ x + (x + h) * Eθ (x + h) ≤ C * (2 + c * exp (-L / 8)) * w := by
    have := mul_le_mul_of_nonneg_left hhu hC
    nlinarith
  -- θ at the endpoints
  have habs1 : |Chebyshev.theta x - x| = x * Eθ x := by
    unfold Eθ; field_simp
  have habs2 : |Chebyshev.theta (x + h) - (x + h)| = (x + h) * Eθ (x + h) := by
    unfold Eθ; field_simp
  have hT := theta_sub_bounds hx0 (show x ≤ x + h by linarith)
  have hlo : h - (x * Eθ x + (x + h) * Eθ (x + h)) ≤
      Chebyshev.theta (x + h) - Chebyshev.theta x := by
    have a1 := neg_abs_le (Chebyshev.theta (x + h) - (x + h))
    have a2 := le_abs_self (Chebyshev.theta x - x)
    rw [habs1] at a2; rw [habs2] at a1
    linarith
  have hhi : Chebyshev.theta (x + h) - Chebyshev.theta x ≤
      h + (x * Eθ x + (x + h) * Eθ (x + h)) := by
    have a1 := le_abs_self (Chebyshev.theta (x + h) - (x + h))
    have a2 := neg_abs_le (Chebyshev.theta x - x)
    rw [habs1] at a2; rw [habs2] at a1
    linarith
  constructor
  · calc (c - C * (2 + c * exp (-L / 8))) * w = h - C * (2 + c * exp (-L / 8)) * w := by
          rw [hh]; ring
      _ ≤ h - (x * Eθ x + (x + h) * Eθ (x + h)) := by linarith
      _ ≤ _ := hlo
      _ ≤ _ := hT.2
  · calc _ ≤ Chebyshev.theta (x + h) - Chebyshev.theta x := hT.1
      _ ≤ h + (x * Eθ x + (x + h) * Eθ (x + h)) := hhi
      _ ≤ h + C * (2 + c * exp (-L / 8)) * w := by linarith
      _ = (c + C * (2 + c * exp (-L / 8))) * w := by rw [hh]; ring

/-- **Counting from `Eπ`.** -/
theorem count_of_pi_power {K c L : ℝ} (hπ : HasPowerLogBound Eπ K 0 (7 / 8) (exp L))
    (hK : 0 ≤ K) (hc : 0 < c) (hL : 1 ≤ L) :
    ∀ x ≥ exp L,
      (c - K * (2 + c * exp (-L / 8) * (1 + 1 / L))) * x ^ ((7 : ℝ) / 8) ≤
          (primeCounting (x + c * x ^ ((7 : ℝ) / 8)) - primeCounting x) *
            log (x + c * x ^ ((7 : ℝ) / 8)) ∧
        (primeCounting (x + c * x ^ ((7 : ℝ) / 8)) - primeCounting x) * log x ≤
          (c + K * (2 + c * exp (-L / 8))) * x ^ ((7 : ℝ) / 8) := by
  intro x hx
  have he1 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hx2 : 2 ≤ x := he1.trans ((exp_le_exp.mpr hL).trans hx)
  have hx0 : 0 < x := by linarith
  have hLx : L ≤ log x := by simpa using log_le_log (exp_pos L) hx
  set w := x ^ ((7 : ℝ) / 8) with hw
  set h := c * w with hh
  have hw0 : 0 < w := rpow_pos_of_pos hx0 _
  have hh0 : 0 < h := by positivity
  obtain ⟨-, hu0, hxu, huL, hy⟩ := power_bookkeeping (L := L) hx hh0.le
  set u := x ^ ((7 : ℝ) / 8 - 1) with hu
  set y := x + h with hyd
  have hlx : 0 < log x := log_pos (by linarith)
  have hly : 0 < log y := log_pos (by linarith)
  have hlxy : log x ≤ log y := log_le_log hx0 (by linarith)
  -- |π − Li| at the two endpoints
  have hb1 := hπ x hx
  have hb2 := hπ y (by linarith)
  simp only [pow_zero, mul_one] at hb1 hb2
  have habs1 : |primeCounting x - Li x| ≤ K * w / log x := by
    have heq : |primeCounting x - Li x| = Eπ x * (x / log x) := by
      unfold Eπ; field_simp
    rw [heq]
    calc Eπ x * (x / log x) ≤ K * u * (x / log x) :=
          mul_le_mul_of_nonneg_right hb1 (by positivity)
      _ = K * (x * u) / log x := by ring
      _ = K * w / log x := by rw [hxu]
  have habs2 : |primeCounting y - Li y| ≤ K * (w + h * u) / log y := by
    have hy0 : 0 < y := by linarith
    have heq : |primeCounting y - Li y| = Eπ y * (y / log y) := by
      unfold Eπ; field_simp
    rw [heq]
    calc Eπ y * (y / log y) ≤ K * y ^ ((7 : ℝ) / 8 - 1) * (y / log y) :=
          mul_le_mul_of_nonneg_right hb2 (by positivity)
      _ = K * (y * y ^ ((7 : ℝ) / 8 - 1)) / log y := by ring
      _ ≤ K * (w + h * u) / log y := by
          apply div_le_div_of_nonneg_right _ hly.le
          exact mul_le_mul_of_nonneg_left hy hK
  obtain ⟨hLi1, hLi2⟩ := Li_sub_bounds hx2 hh0.le
  have hhu : h * u ≤ c * w * exp (-L / 8) := by
    rw [hh, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left huL hw0.le) hc.le
  rw [abs_le] at habs1 habs2
  constructor
  · -- (π y − π x)·log y ≥ h − K(w + h u) − K w·(log y / log x)
    have hratio : log y ≤ log x * (1 + c * u / L) := by
      have hq : log y - log x ≤ h / x := by
        rw [← log_div (by linarith) hx0.ne']
        have := log_le_sub_one_of_pos (show 0 < y / x by positivity)
        have e : y / x - 1 = h / x := by rw [hyd]; field_simp; ring
        linarith
      have hhx : h / x = c * u := by
        rw [hh, hw, ← hxu]; field_simp
      have hcu : 0 ≤ c * u := by positivity
      have : log x * (c * u / L) ≥ c * u := by
        rw [ge_iff_le, mul_div_assoc', le_div_iff₀ (by linarith)]
        nlinarith
      linarith
    have hkey : (primeCounting y - primeCounting x) * log y ≥
        h - K * (w + h * u) - K * w * (log y / log x) := by
      have hdiff : primeCounting y - primeCounting x ≥
          h / log y - K * (w + h * u) / log y - K * w / log x := by linarith [habs1.2, habs2.1]
      have := mul_le_mul_of_nonneg_right hdiff hly.le
      have e1 : (h / log y - K * (w + h * u) / log y - K * w / log x) * log y =
          h - K * (w + h * u) - K * w * (log y / log x) := by
        field_simp
      linarith
    have hr : log y / log x ≤ 1 + c * u / L := by
      rw [div_le_iff₀ hlx]; linarith
    have hKw : K * w * (log y / log x) ≤ K * w * (1 + c * u / L) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    have hcuL : c * u / L ≤ c * exp (-L / 8) / L := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left huL hc.le
    have hfin : (c - K * (2 + c * exp (-L / 8) * (1 + 1 / L))) * w ≤
        h - K * (w + h * u) - K * w * (1 + c * u / L) := by
      have e2 : K * (h * u) ≤ K * (c * w * exp (-L / 8)) := mul_le_mul_of_nonneg_left hhu hK
      have e3 : K * w * (c * u / L) ≤ K * w * (c * exp (-L / 8) / L) :=
        mul_le_mul_of_nonneg_left hcuL (by positivity)
      have e4 : (c - K * (2 + c * exp (-L / 8) * (1 + 1 / L))) * w =
          h - K * w - K * (c * w * exp (-L / 8)) - K * w - K * w * (c * exp (-L / 8) / L) := by
        rw [hh]; field_simp; ring
      rw [e4]
      nlinarith
    linarith
  · have hdiff : primeCounting y - primeCounting x ≤
        h / log x + K * (w + h * u) / log y + K * w / log x := by linarith [habs1.1, habs2.2]
    have h2 : K * (w + h * u) / log y ≤ K * (w + h * u) / log x :=
      div_le_div_of_nonneg_left (by positivity) hlx hlxy
    have h3 : (primeCounting y - primeCounting x) * log x ≤
        (h / log x + K * (w + h * u) / log x + K * w / log x) * log x :=
      mul_le_mul_of_nonneg_right (by linarith) hlx.le
    have e1 : (h / log x + K * (w + h * u) / log x + K * w / log x) * log x =
        h + K * (w + h * u) + K * w := by field_simp
    have e2 : K * (h * u) ≤ K * (c * w * exp (-L / 8)) := mul_le_mul_of_nonneg_left hhu hK
    calc (primeCounting y - primeCounting x) * log x ≤ h + K * (w + h * u) + K * w := by
          linarith
      _ = c * w + 2 * K * w + K * (h * u) := by rw [hh]; ring
      _ ≤ c * w + 2 * K * w + K * (c * w * exp (-L / 8)) := by linarith
      _ = (c + K * (2 + c * exp (-L / 8))) * w := by ring

/-- **Primes in short intervals from `Eπ`.** If `K·(2 + c·e^{-L/8}·(1 + 1/L)) < c`, every
`(x, x + c·x^{7/8}]` with `x ≥ e^L` contains a prime. -/
theorem interval_of_pi_power {K c L : ℝ} (hπ : HasPowerLogBound Eπ K 0 (7 / 8) (exp L))
    (hK : 0 ≤ K) (hc : 0 < c) (hL : 1 ≤ L) (hsmall : K * (2 + c * exp (-L / 8) * (1 + 1 / L)) < c) :
    ∀ x ≥ exp L, HasPrimeInInterval x (c * x ^ ((7 : ℝ) / 8)) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos L).trans_le hx
  have hw0 : 0 < x ^ ((7 : ℝ) / 8) := rpow_pos_of_pos hx0 _
  have hh0 : 0 < c * x ^ ((7 : ℝ) / 8) := by positivity
  have hcnt := (count_of_pi_power hπ hK hc hL x hx).1
  have hly : 0 < log (x + c * x ^ ((7 : ℝ) / 8)) := by
    have he1 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    have : 2 ≤ x := he1.trans ((exp_le_exp.mpr hL).trans hx)
    exact log_pos (by linarith)
  have hpos : 0 < (c - K * (2 + c * exp (-L / 8) * (1 + 1 / L))) * x ^ ((7 : ℝ) / 8) :=
    mul_pos (by linarith) hw0
  apply hasPrimeInInterval_of_count hx0 hh0.le
  by_contra hneg
  push Not at hneg
  have := mul_le_mul_of_nonneg_right hneg hly.le
  linarith

end QRHGlobal
