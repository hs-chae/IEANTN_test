/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityNumericDefs
import DensityFastSupport

namespace DensityNumeric
noncomputable def cellTerm (L τ : ℝ) (i : ℕ) : ℝ :=
  (Q (7 / 8 - (i + 1 : ℝ) / 4096) τ - Q (7 / 8 - (i : ℝ) / 4096) τ) * 4096 *
    (Real.exp (-L * (i : ℝ) / 4096) - Real.exp (-L * (i + 1 : ℝ) / 4096)) / L

/-- A verified partition of every finite sum into equal consecutive blocks. -/
theorem sum_range_blocks (f : ℕ → ℝ) (m n : ℕ) :
    (∑ i ∈ Finset.range (m * n), f i) =
      ∑ b ∈ Finset.range m, ∑ j ∈ Finset.range n, f (b * n + j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- The concrete cells used by every certificate are all present, exactly once. -/
theorem sum_512_blocks (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range 512, f i) =
      ∑ b ∈ Finset.range 32, ∑ j ∈ Finset.Icc 0 15, f (b * 16 + j) := by
  have he := sum_range_blocks f 32 16
  have hs : Finset.range 16 = Finset.Icc (0 : ℕ) 15 := by
    ext j
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega
  norm_num only [Nat.reduceMul] at he
  rw [hs] at he
  exact he
end DensityNumeric
#print axioms DensityNumeric.sum_512_blocks
