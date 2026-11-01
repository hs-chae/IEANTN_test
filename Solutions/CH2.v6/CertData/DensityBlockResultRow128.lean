/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CertData.DensityPointRow128
import Mathlib.Tactic.IntervalCases
import CertData.DensityBlockRow128_00
import CertData.DensityBlockRow128_01
import CertData.DensityBlockRow128_02
import CertData.DensityBlockRow128_03
import CertData.DensityBlockRow128_04
import CertData.DensityBlockRow128_05
import CertData.DensityBlockRow128_06
import CertData.DensityBlockRow128_07
import CertData.DensityBlockRow128_08
import CertData.DensityBlockRow128_09
import CertData.DensityBlockRow128_10
import CertData.DensityBlockRow128_11
import CertData.DensityBlockRow128_12
import CertData.DensityBlockRow128_13
import CertData.DensityBlockRow128_14
import CertData.DensityBlockRow128_15
import CertData.DensityBlockRow128_16
import CertData.DensityBlockRow128_17
import CertData.DensityBlockRow128_18
import CertData.DensityBlockRow128_19
import CertData.DensityBlockRow128_20
import CertData.DensityBlockRow128_21
import CertData.DensityBlockRow128_22
import CertData.DensityBlockRow128_23
import CertData.DensityBlockRow128_24
import CertData.DensityBlockRow128_25
import CertData.DensityBlockRow128_26
import CertData.DensityBlockRow128_27
import CertData.DensityBlockRow128_28
import CertData.DensityBlockRow128_29
import CertData.DensityBlockRow128_30
import CertData.DensityBlockRow128_31
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityBlockResultRow128
theorem endpoint_upper : Q (7/8) 50 ≤ (92367 : ℝ) / 10000000 := DensityPointRow128.endpoint_upper
theorem base_upper : Real.exp (-(128:ℝ)/8) *
    (((50:ℝ)+(1:ℝ)/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((50:ℝ)+(1:ℝ)/10^9)) ≤ (579 : ℝ) / 10000000 := DensityPointRow128.base_upper

private noncomputable def blockBound (b : ℕ) : ℝ :=
  [(294767 : ℝ) / 100000000, (63161 : ℝ) / 25000000, (216629 : ℝ) / 100000000, (185827 : ℝ) / 100000000, (39869 : ℝ) / 25000000, (5477 : ℝ) / 4000000, (117619 : ℝ) / 100000000, (101087 : ℝ) / 100000000, (21731 : ℝ) / 25000000, (74787 : ℝ) / 100000000, (32191 : ℝ) / 50000000, (55459 : ℝ) / 100000000, (23901 : ℝ) / 50000000, (41231 : ℝ) / 100000000, (8897 : ℝ) / 25000000, (1537 : ℝ) / 5000000, (26573 : ℝ) / 100000000, (22991 : ℝ) / 100000000, (19909 : ℝ) / 100000000, (17257 : ℝ) / 100000000, (14973 : ℝ) / 100000000, (2601 : ℝ) / 20000000, (2827 : ℝ) / 25000000, (1969 : ℝ) / 20000000, (8583 : ℝ) / 100000000, (7493 : ℝ) / 100000000, (6551 : ℝ) / 100000000, (5737 : ℝ) / 100000000, (5033 : ℝ) / 100000000, (553 : ℝ) / 12500000, (3897 : ℝ) / 100000000, (3441 : ℝ) / 100000000].getD b 0

theorem sum_upper : (∑ i ∈ Finset.range 512, cellTerm 128 50 i) ≤ (20835399999 : ℝ) / 1000000000000 := by
  rw [sum_512_blocks]
  have h : ∀ b ∈ Finset.range 32,
      (∑ k ∈ Finset.Icc (0 : ℕ) 15, cellTerm 128 50 (b * 16 + k)) ≤ blockBound b := by
    intro b hb
    have hb' : b < 32 := Finset.mem_range.mp hb
    interval_cases b
    · exact DensityBlockRow128.block_00
    · exact DensityBlockRow128.block_01
    · exact DensityBlockRow128.block_02
    · exact DensityBlockRow128.block_03
    · exact DensityBlockRow128.block_04
    · exact DensityBlockRow128.block_05
    · exact DensityBlockRow128.block_06
    · exact DensityBlockRow128.block_07
    · exact DensityBlockRow128.block_08
    · exact DensityBlockRow128.block_09
    · exact DensityBlockRow128.block_10
    · exact DensityBlockRow128.block_11
    · exact DensityBlockRow128.block_12
    · exact DensityBlockRow128.block_13
    · exact DensityBlockRow128.block_14
    · exact DensityBlockRow128.block_15
    · exact DensityBlockRow128.block_16
    · exact DensityBlockRow128.block_17
    · exact DensityBlockRow128.block_18
    · exact DensityBlockRow128.block_19
    · exact DensityBlockRow128.block_20
    · exact DensityBlockRow128.block_21
    · exact DensityBlockRow128.block_22
    · exact DensityBlockRow128.block_23
    · exact DensityBlockRow128.block_24
    · exact DensityBlockRow128.block_25
    · exact DensityBlockRow128.block_26
    · exact DensityBlockRow128.block_27
    · exact DensityBlockRow128.block_28
    · exact DensityBlockRow128.block_29
    · exact DensityBlockRow128.block_30
    · exact DensityBlockRow128.block_31
  apply (Finset.sum_le_sum h).trans
  norm_num [blockBound, Finset.sum_range_succ]
#print axioms endpoint_upper
#print axioms base_upper
#print axioms sum_upper
end DensityBlockResultRow128
