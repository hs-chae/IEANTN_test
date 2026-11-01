/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CertData.DensityPointRow160
import Mathlib.Tactic.IntervalCases
import CertData.DensityBlockRow160_00
import CertData.DensityBlockRow160_01
import CertData.DensityBlockRow160_02
import CertData.DensityBlockRow160_03
import CertData.DensityBlockRow160_04
import CertData.DensityBlockRow160_05
import CertData.DensityBlockRow160_06
import CertData.DensityBlockRow160_07
import CertData.DensityBlockRow160_08
import CertData.DensityBlockRow160_09
import CertData.DensityBlockRow160_10
import CertData.DensityBlockRow160_11
import CertData.DensityBlockRow160_12
import CertData.DensityBlockRow160_13
import CertData.DensityBlockRow160_14
import CertData.DensityBlockRow160_15
import CertData.DensityBlockRow160_16
import CertData.DensityBlockRow160_17
import CertData.DensityBlockRow160_18
import CertData.DensityBlockRow160_19
import CertData.DensityBlockRow160_20
import CertData.DensityBlockRow160_21
import CertData.DensityBlockRow160_22
import CertData.DensityBlockRow160_23
import CertData.DensityBlockRow160_24
import CertData.DensityBlockRow160_25
import CertData.DensityBlockRow160_26
import CertData.DensityBlockRow160_27
import CertData.DensityBlockRow160_28
import CertData.DensityBlockRow160_29
import CertData.DensityBlockRow160_30
import CertData.DensityBlockRow160_31
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityBlockResultRow160
theorem endpoint_upper : Q (7/8) 55 ≤ (18473 : ℝ) / 2000000 := DensityPointRow160.endpoint_upper
theorem base_upper : Real.exp (-(160:ℝ)/8) *
    (((55:ℝ)+(1:ℝ)/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((55:ℝ)+(1:ℝ)/10^9)) ≤ (13 : ℝ) / 10000000 := DensityPointRow160.base_upper

private noncomputable def blockBound (b : ℕ) : ℝ :=
  [(277531 : ℝ) / 100000000, (209919 : ℝ) / 100000000, (39711 : ℝ) / 25000000, (120247 : ℝ) / 100000000, (91069 : ℝ) / 100000000, (69003 : ℝ) / 100000000, (52309 : ℝ) / 100000000, (19837 : ℝ) / 50000000, (30107 : ℝ) / 100000000, (1143 : ℝ) / 5000000, (2171 : ℝ) / 12500000, (13203 : ℝ) / 100000000, (2511 : ℝ) / 25000000, (3823 : ℝ) / 50000000, (233 : ℝ) / 4000000, (4441 : ℝ) / 100000000, (3389 : ℝ) / 100000000, (647 : ℝ) / 25000000, (1979 : ℝ) / 100000000, (303 : ℝ) / 20000000, (1161 : ℝ) / 100000000, (891 : ℝ) / 100000000, (137 : ℝ) / 20000000, (527 : ℝ) / 100000000, (407 : ℝ) / 100000000, (157 : ℝ) / 50000000, (61 : ℝ) / 25000000, (189 : ℝ) / 100000000, (37 : ℝ) / 25000000, (29 : ℝ) / 25000000, (91 : ℝ) / 100000000, (9 : ℝ) / 12500000].getD b 0

theorem sum_upper : (∑ i ∈ Finset.range 512, cellTerm 160 55 i) ≤ (11452199999 : ℝ) / 1000000000000 := by
  rw [sum_512_blocks]
  have h : ∀ b ∈ Finset.range 32,
      (∑ k ∈ Finset.Icc (0 : ℕ) 15, cellTerm 160 55 (b * 16 + k)) ≤ blockBound b := by
    intro b hb
    have hb' : b < 32 := Finset.mem_range.mp hb
    interval_cases b
    · exact DensityBlockRow160.block_00
    · exact DensityBlockRow160.block_01
    · exact DensityBlockRow160.block_02
    · exact DensityBlockRow160.block_03
    · exact DensityBlockRow160.block_04
    · exact DensityBlockRow160.block_05
    · exact DensityBlockRow160.block_06
    · exact DensityBlockRow160.block_07
    · exact DensityBlockRow160.block_08
    · exact DensityBlockRow160.block_09
    · exact DensityBlockRow160.block_10
    · exact DensityBlockRow160.block_11
    · exact DensityBlockRow160.block_12
    · exact DensityBlockRow160.block_13
    · exact DensityBlockRow160.block_14
    · exact DensityBlockRow160.block_15
    · exact DensityBlockRow160.block_16
    · exact DensityBlockRow160.block_17
    · exact DensityBlockRow160.block_18
    · exact DensityBlockRow160.block_19
    · exact DensityBlockRow160.block_20
    · exact DensityBlockRow160.block_21
    · exact DensityBlockRow160.block_22
    · exact DensityBlockRow160.block_23
    · exact DensityBlockRow160.block_24
    · exact DensityBlockRow160.block_25
    · exact DensityBlockRow160.block_26
    · exact DensityBlockRow160.block_27
    · exact DensityBlockRow160.block_28
    · exact DensityBlockRow160.block_29
    · exact DensityBlockRow160.block_30
    · exact DensityBlockRow160.block_31
  apply (Finset.sum_le_sum h).trans
  norm_num [blockBound, Finset.sum_range_succ]
#print axioms endpoint_upper
#print axioms base_upper
#print axioms sum_upper
end DensityBlockResultRow160
