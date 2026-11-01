/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CertData.DensityPointRow112
import Mathlib.Tactic.IntervalCases
import CertData.DensityBlockRow112_00
import CertData.DensityBlockRow112_01
import CertData.DensityBlockRow112_02
import CertData.DensityBlockRow112_03
import CertData.DensityBlockRow112_04
import CertData.DensityBlockRow112_05
import CertData.DensityBlockRow112_06
import CertData.DensityBlockRow112_07
import CertData.DensityBlockRow112_08
import CertData.DensityBlockRow112_09
import CertData.DensityBlockRow112_10
import CertData.DensityBlockRow112_11
import CertData.DensityBlockRow112_12
import CertData.DensityBlockRow112_13
import CertData.DensityBlockRow112_14
import CertData.DensityBlockRow112_15
import CertData.DensityBlockRow112_16
import CertData.DensityBlockRow112_17
import CertData.DensityBlockRow112_18
import CertData.DensityBlockRow112_19
import CertData.DensityBlockRow112_20
import CertData.DensityBlockRow112_21
import CertData.DensityBlockRow112_22
import CertData.DensityBlockRow112_23
import CertData.DensityBlockRow112_24
import CertData.DensityBlockRow112_25
import CertData.DensityBlockRow112_26
import CertData.DensityBlockRow112_27
import CertData.DensityBlockRow112_28
import CertData.DensityBlockRow112_29
import CertData.DensityBlockRow112_30
import CertData.DensityBlockRow112_31
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityBlockResultRow112
theorem endpoint_upper : Q (7/8) 48 ≤ (9237 : ℝ) / 1000000 := DensityPointRow112.endpoint_upper
theorem base_upper : Real.exp (-(112:ℝ)/8) *
    (((48:ℝ)+(1:ℝ)/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((48:ℝ)+(1:ℝ)/10^9)) ≤ (159 : ℝ) / 400000 := DensityPointRow112.base_upper

private noncomputable def blockBound (b : ℕ) : ℝ :=
  [(37993 : ℝ) / 12500000, (138657 : ℝ) / 50000000, (253121 : ℝ) / 100000000, (115569 : ℝ) / 50000000, (105579 : ℝ) / 50000000, (48249 : ℝ) / 25000000, (176481 : ℝ) / 100000000, (80731 : ℝ) / 50000000, (739 : ℝ) / 500000, (135369 : ℝ) / 100000000, (15507 : ℝ) / 12500000, (113759 : ℝ) / 100000000, (1631 : ℝ) / 1562500, (95847 : ℝ) / 100000000, (88071 : ℝ) / 100000000, (20247 : ℝ) / 25000000, (37267 : ℝ) / 50000000, (68653 : ℝ) / 100000000, (31647 : ℝ) / 50000000, (58409 : ℝ) / 100000000, (13489 : ℝ) / 25000000, (49897 : ℝ) / 100000000, (23099 : ℝ) / 50000000, (42827 : ℝ) / 100000000, (7951 : ℝ) / 20000000, (36957 : ℝ) / 100000000, (3441 : ℝ) / 10000000, (32093 : ℝ) / 100000000, (29987 : ℝ) / 100000000, (14037 : ℝ) / 50000000, (26341 : ℝ) / 100000000, (6193 : ℝ) / 25000000].getD b 0

theorem sum_upper : (∑ i ∈ Finset.range 512, cellTerm 112 48 i) ≤ (34085499999 : ℝ) / 1000000000000 := by
  rw [sum_512_blocks]
  have h : ∀ b ∈ Finset.range 32,
      (∑ k ∈ Finset.Icc (0 : ℕ) 15, cellTerm 112 48 (b * 16 + k)) ≤ blockBound b := by
    intro b hb
    have hb' : b < 32 := Finset.mem_range.mp hb
    interval_cases b
    · exact DensityBlockRow112.block_00
    · exact DensityBlockRow112.block_01
    · exact DensityBlockRow112.block_02
    · exact DensityBlockRow112.block_03
    · exact DensityBlockRow112.block_04
    · exact DensityBlockRow112.block_05
    · exact DensityBlockRow112.block_06
    · exact DensityBlockRow112.block_07
    · exact DensityBlockRow112.block_08
    · exact DensityBlockRow112.block_09
    · exact DensityBlockRow112.block_10
    · exact DensityBlockRow112.block_11
    · exact DensityBlockRow112.block_12
    · exact DensityBlockRow112.block_13
    · exact DensityBlockRow112.block_14
    · exact DensityBlockRow112.block_15
    · exact DensityBlockRow112.block_16
    · exact DensityBlockRow112.block_17
    · exact DensityBlockRow112.block_18
    · exact DensityBlockRow112.block_19
    · exact DensityBlockRow112.block_20
    · exact DensityBlockRow112.block_21
    · exact DensityBlockRow112.block_22
    · exact DensityBlockRow112.block_23
    · exact DensityBlockRow112.block_24
    · exact DensityBlockRow112.block_25
    · exact DensityBlockRow112.block_26
    · exact DensityBlockRow112.block_27
    · exact DensityBlockRow112.block_28
    · exact DensityBlockRow112.block_29
    · exact DensityBlockRow112.block_30
    · exact DensityBlockRow112.block_31
  apply (Finset.sum_le_sum h).trans
  norm_num [blockBound, Finset.sum_range_succ]
#print axioms endpoint_upper
#print axioms base_upper
#print axioms sum_upper
end DensityBlockResultRow112
