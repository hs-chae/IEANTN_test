/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityBlockSupport
set_option leancert.trust "kernel"
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityBlockRow160
theorem block_00 : (∑ k ∈ Finset.Icc (0 : ℕ) 15, cellTerm 160 55 (0 * 16 + k)) ≤ (277531 : ℝ) / 100000000 := by
  dsimp only [cellTerm, Q]
  push_cast
  conv_lhs =>
    arg 2
    ext k
    simp only [pow_succ, pow_zero, mul_one, div_eq_mul_inv, sub_eq_add_neg]
  density_fast_finsum 18
#print axioms block_00
end DensityBlockRow160
