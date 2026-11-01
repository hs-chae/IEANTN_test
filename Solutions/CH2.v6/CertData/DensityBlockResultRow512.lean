/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CertData.DensityPointRow512
import Mathlib.Tactic.IntervalCases
import CertData.DensityBlockRow512_00
import CertData.DensityBlockRow512_01
import CertData.DensityBlockRow512_02
import CertData.DensityBlockRow512_03
import CertData.DensityBlockRow512_04
import CertData.DensityBlockRow512_05
import CertData.DensityBlockRow512_06
import CertData.DensityBlockRow512_07
import CertData.DensityBlockRow512_08
import CertData.DensityBlockRow512_09
import CertData.DensityBlockRow512_10
import CertData.DensityBlockRow512_11
import CertData.DensityBlockRow512_12
import CertData.DensityBlockRow512_13
import CertData.DensityBlockRow512_14
import CertData.DensityBlockRow512_15
import CertData.DensityBlockRow512_16
import CertData.DensityBlockRow512_17
import CertData.DensityBlockRow512_18
import CertData.DensityBlockRow512_19
import CertData.DensityBlockRow512_20
import CertData.DensityBlockRow512_21
import CertData.DensityBlockRow512_22
import CertData.DensityBlockRow512_23
import CertData.DensityBlockRow512_24
import CertData.DensityBlockRow512_25
import CertData.DensityBlockRow512_26
import CertData.DensityBlockRow512_27
import CertData.DensityBlockRow512_28
import CertData.DensityBlockRow512_29
import CertData.DensityBlockRow512_30
import CertData.DensityBlockRow512_31
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityBlockResultRow512
theorem endpoint_upper : Q (7/8) 140 ≤ (18473 : ℝ) / 2000000 := DensityPointRow512.endpoint_upper
theorem base_upper : Real.exp (-(512:ℝ)/8) *
    (((140:ℝ)+(1:ℝ)/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((140:ℝ)+(1:ℝ)/10^9)) ≤ (1 : ℝ) / 10000000 := DensityPointRow512.base_upper

private noncomputable def blockBound (b : ℕ) : ℝ :=
  [(7777 : ℝ) / 5000000, (29749 : ℝ) / 100000000, (89 : ℝ) / 1562500, (219 : ℝ) / 20000000, (107 : ℝ) / 50000000, (9 : ℝ) / 20000000, (13 : ℝ) / 100000000, (7 : ℝ) / 100000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000].getD b 0

theorem sum_upper : (∑ i ∈ Finset.range 512, cellTerm 512 140 i) ≤ (1933399999 : ℝ) / 1000000000000 := by
  rw [sum_512_blocks]
  have h : ∀ b ∈ Finset.range 32,
      (∑ k ∈ Finset.Icc (0 : ℕ) 15, cellTerm 512 140 (b * 16 + k)) ≤ blockBound b := by
    intro b hb
    have hb' : b < 32 := Finset.mem_range.mp hb
    interval_cases b
    · exact DensityBlockRow512.block_00
    · exact DensityBlockRow512.block_01
    · exact DensityBlockRow512.block_02
    · exact DensityBlockRow512.block_03
    · exact DensityBlockRow512.block_04
    · exact DensityBlockRow512.block_05
    · exact DensityBlockRow512.block_06
    · exact DensityBlockRow512.block_07
    · exact DensityBlockRow512.block_08
    · exact DensityBlockRow512.block_09
    · exact DensityBlockRow512.block_10
    · exact DensityBlockRow512.block_11
    · exact DensityBlockRow512.block_12
    · exact DensityBlockRow512.block_13
    · exact DensityBlockRow512.block_14
    · exact DensityBlockRow512.block_15
    · exact DensityBlockRow512.block_16
    · exact DensityBlockRow512.block_17
    · exact DensityBlockRow512.block_18
    · exact DensityBlockRow512.block_19
    · exact DensityBlockRow512.block_20
    · exact DensityBlockRow512.block_21
    · exact DensityBlockRow512.block_22
    · exact DensityBlockRow512.block_23
    · exact DensityBlockRow512.block_24
    · exact DensityBlockRow512.block_25
    · exact DensityBlockRow512.block_26
    · exact DensityBlockRow512.block_27
    · exact DensityBlockRow512.block_28
    · exact DensityBlockRow512.block_29
    · exact DensityBlockRow512.block_30
    · exact DensityBlockRow512.block_31
  apply (Finset.sum_le_sum h).trans
  norm_num [blockBound, Finset.sum_range_succ]
#print axioms endpoint_upper
#print axioms base_upper
#print axioms sum_upper
end DensityBlockResultRow512
