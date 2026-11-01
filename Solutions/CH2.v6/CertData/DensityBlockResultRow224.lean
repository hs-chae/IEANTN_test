/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CertData.DensityPointRow224
import Mathlib.Tactic.IntervalCases
import CertData.DensityBlockRow224_00
import CertData.DensityBlockRow224_01
import CertData.DensityBlockRow224_02
import CertData.DensityBlockRow224_03
import CertData.DensityBlockRow224_04
import CertData.DensityBlockRow224_05
import CertData.DensityBlockRow224_06
import CertData.DensityBlockRow224_07
import CertData.DensityBlockRow224_08
import CertData.DensityBlockRow224_09
import CertData.DensityBlockRow224_10
import CertData.DensityBlockRow224_11
import CertData.DensityBlockRow224_12
import CertData.DensityBlockRow224_13
import CertData.DensityBlockRow224_14
import CertData.DensityBlockRow224_15
import CertData.DensityBlockRow224_16
import CertData.DensityBlockRow224_17
import CertData.DensityBlockRow224_18
import CertData.DensityBlockRow224_19
import CertData.DensityBlockRow224_20
import CertData.DensityBlockRow224_21
import CertData.DensityBlockRow224_22
import CertData.DensityBlockRow224_23
import CertData.DensityBlockRow224_24
import CertData.DensityBlockRow224_25
import CertData.DensityBlockRow224_26
import CertData.DensityBlockRow224_27
import CertData.DensityBlockRow224_28
import CertData.DensityBlockRow224_29
import CertData.DensityBlockRow224_30
import CertData.DensityBlockRow224_31
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityBlockResultRow224
theorem endpoint_upper : Q (7/8) 67 ≤ (18473 : ℝ) / 2000000 := DensityPointRow224.endpoint_upper
theorem base_upper : Real.exp (-(224:ℝ)/8) *
    (((67:ℝ)+(1:ℝ)/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((67:ℝ)+(1:ℝ)/10^9)) ≤ (1 : ℝ) / 10000000 := DensityPointRow224.base_upper

private noncomputable def blockBound (b : ℕ) : ℝ :=
  [(246993 : ℝ) / 100000000, (18187 : ℝ) / 12500000, (85743 : ℝ) / 100000000, (6319 : ℝ) / 12500000, (29819 : ℝ) / 100000000, (8799 : ℝ) / 50000000, (10391 : ℝ) / 100000000, (307 : ℝ) / 5000000, (3631 : ℝ) / 100000000, (2149 : ℝ) / 100000000, (637 : ℝ) / 50000000, (189 : ℝ) / 25000000, (9 : ℝ) / 2000000, (269 : ℝ) / 100000000, (81 : ℝ) / 50000000, (49 : ℝ) / 50000000, (61 : ℝ) / 100000000, (19 : ℝ) / 50000000, (1 : ℝ) / 4000000, (17 : ℝ) / 100000000, (3 : ℝ) / 25000000, (1 : ℝ) / 10000000, (1 : ℝ) / 12500000, (7 : ℝ) / 100000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000].getD b 0

theorem sum_upper : (∑ i ∈ Finset.range 512, cellTerm 224 67 i) ≤ (6023399999 : ℝ) / 1000000000000 := by
  rw [sum_512_blocks]
  have h : ∀ b ∈ Finset.range 32,
      (∑ k ∈ Finset.Icc (0 : ℕ) 15, cellTerm 224 67 (b * 16 + k)) ≤ blockBound b := by
    intro b hb
    have hb' : b < 32 := Finset.mem_range.mp hb
    interval_cases b
    · exact DensityBlockRow224.block_00
    · exact DensityBlockRow224.block_01
    · exact DensityBlockRow224.block_02
    · exact DensityBlockRow224.block_03
    · exact DensityBlockRow224.block_04
    · exact DensityBlockRow224.block_05
    · exact DensityBlockRow224.block_06
    · exact DensityBlockRow224.block_07
    · exact DensityBlockRow224.block_08
    · exact DensityBlockRow224.block_09
    · exact DensityBlockRow224.block_10
    · exact DensityBlockRow224.block_11
    · exact DensityBlockRow224.block_12
    · exact DensityBlockRow224.block_13
    · exact DensityBlockRow224.block_14
    · exact DensityBlockRow224.block_15
    · exact DensityBlockRow224.block_16
    · exact DensityBlockRow224.block_17
    · exact DensityBlockRow224.block_18
    · exact DensityBlockRow224.block_19
    · exact DensityBlockRow224.block_20
    · exact DensityBlockRow224.block_21
    · exact DensityBlockRow224.block_22
    · exact DensityBlockRow224.block_23
    · exact DensityBlockRow224.block_24
    · exact DensityBlockRow224.block_25
    · exact DensityBlockRow224.block_26
    · exact DensityBlockRow224.block_27
    · exact DensityBlockRow224.block_28
    · exact DensityBlockRow224.block_29
    · exact DensityBlockRow224.block_30
    · exact DensityBlockRow224.block_31
  apply (Finset.sum_le_sum h).trans
  norm_num [blockBound, Finset.sum_range_succ]
#print axioms endpoint_upper
#print axioms base_upper
#print axioms sum_upper
end DensityBlockResultRow224
