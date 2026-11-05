/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import QRHGlobalIntervals.Criterion
import IEANTN.Nodes.KadiriLumley.v1.Conclusions

/-!
# Short intervals from a Kadiri–Lumley row

A row `(X, Δ)` of `KadiriLumley.v1.table_2` gives, for every `y ≥ X`, a prime in
`(y(1 - 1/Δ), y)`. Taking `y = x + h` with `h = c·x^{7/8}`, the prime is above `x` as soon as
`h(Δ - 1) ≥ x`, i.e. `x^{1/8} ≤ c(Δ - 1)`. So the row covers `[X, (c(Δ-1))^8]`.
-/

namespace QRHGlobal

open Real IEANTN

theorem kl_piece {X Δ c : ℝ}
    (hrow : ∀ y : ℝ, X ≤ y → ∃ p : ℕ, Nat.Prime p ∧ y * (1 - 1 / Δ) < p ∧ (p : ℝ) < y)
    (hΔ : 1 < Δ) (hc : 0 < c) :
    ∀ x : ℝ, X ≤ x → 0 < x → x ^ ((1 : ℝ) / 8) ≤ c * (Δ - 1) →
      HasPrimeInInterval x (c * x ^ ((7 : ℝ) / 8)) := by
  intro x hX hx0 hsmall
  have hw : 0 < x ^ ((7 : ℝ) / 8) := rpow_pos_of_pos hx0 _
  set h := c * x ^ ((7 : ℝ) / 8) with hh
  have hh0 : 0 < h := by positivity
  obtain ⟨p, hp, hlo, hhi⟩ := hrow (x + h) (by linarith)
  refine ⟨p, hp, ?_, hhi.le⟩
  have hsplit : x = x ^ ((1 : ℝ) / 8) * x ^ ((7 : ℝ) / 8) := by
    rw [← rpow_add hx0]; norm_num
  have hkey : x ≤ h * (Δ - 1) := by
    calc x = x ^ ((1 : ℝ) / 8) * x ^ ((7 : ℝ) / 8) := hsplit
      _ ≤ c * (Δ - 1) * x ^ ((7 : ℝ) / 8) := by gcongr
      _ = h * (Δ - 1) := by rw [hh]; ring
  have hΔ0 : 0 < Δ := by linarith
  have : x ≤ (x + h) * (1 - 1 / Δ) := by
    have e : (x + h) * (1 - 1 / Δ) - x = (h * (Δ - 1) - x) / Δ := by field_simp; ring
    have : 0 ≤ (h * (Δ - 1) - x) / Δ := div_nonneg (by linarith) hΔ0.le
    linarith
  linarith

end QRHGlobal
