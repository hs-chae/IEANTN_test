/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CertData.DensityPointRow96
import Mathlib.Tactic.IntervalCases
import CertData.DensityBlockRow96_00
import CertData.DensityBlockRow96_01
import CertData.DensityBlockRow96_02
import CertData.DensityBlockRow96_03
import CertData.DensityBlockRow96_04
import CertData.DensityBlockRow96_05
import CertData.DensityBlockRow96_06
import CertData.DensityBlockRow96_07
import CertData.DensityBlockRow96_08
import CertData.DensityBlockRow96_09
import CertData.DensityBlockRow96_10
import CertData.DensityBlockRow96_11
import CertData.DensityBlockRow96_12
import CertData.DensityBlockRow96_13
import CertData.DensityBlockRow96_14
import CertData.DensityBlockRow96_15
import CertData.DensityBlockRow96_16
import CertData.DensityBlockRow96_17
import CertData.DensityBlockRow96_18
import CertData.DensityBlockRow96_19
import CertData.DensityBlockRow96_20
import CertData.DensityBlockRow96_21
import CertData.DensityBlockRow96_22
import CertData.DensityBlockRow96_23
import CertData.DensityBlockRow96_24
import CertData.DensityBlockRow96_25
import CertData.DensityBlockRow96_26
import CertData.DensityBlockRow96_27
import CertData.DensityBlockRow96_28
import CertData.DensityBlockRow96_29
import CertData.DensityBlockRow96_30
import CertData.DensityBlockRow96_31
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityBlockResultRow96
theorem endpoint_upper : Q (7/8) 47 ≤ (46187 : ℝ) / 5000000 := DensityPointRow96.endpoint_upper
theorem base_upper : Real.exp (-(96:ℝ)/8) *
    (((47:ℝ)+(1:ℝ)/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((47:ℝ)+(1:ℝ)/10^9)) ≤ (28297 : ℝ) / 10000000 := DensityPointRow96.base_upper

private noncomputable def blockBound (b : ℕ) : ℝ :=
  [(313511 : ℝ) / 100000000, (152247 : ℝ) / 50000000, (295859 : ℝ) / 100000000, (287593 : ℝ) / 100000000, (279683 : ℝ) / 100000000, (272119 : ℝ) / 100000000, (264889 : ℝ) / 100000000, (257983 : ℝ) / 100000000, (982 : ℝ) / 390625, (61277 : ℝ) / 25000000, (119561 : ℝ) / 50000000, (233427 : ℝ) / 100000000, (228017 : ℝ) / 100000000, (222887 : ℝ) / 100000000, (21803 : ℝ) / 10000000, (53361 : ℝ) / 25000000, (1673 : ℝ) / 800000, (20507 : ℝ) / 10000000, (629 : ℝ) / 312500, (197753 : ℝ) / 100000000, (194491 : ℝ) / 100000000, (191497 : ℝ) / 100000000, (94387 : ℝ) / 50000000, (186329 : ℝ) / 100000000, (23021 : ℝ) / 12500000, (182303 : ℝ) / 100000000, (90373 : ℝ) / 50000000, (179511 : ℝ) / 100000000, (89309 : ℝ) / 50000000, (178089 : ℝ) / 100000000, (177951 : ℝ) / 100000000, (178237 : ℝ) / 100000000].getD b 0

theorem sum_upper : (∑ i ∈ Finset.range 512, cellTerm 96 47 i) ≤ (71422899999 : ℝ) / 1000000000000 := by
  rw [sum_512_blocks]
  have h : ∀ b ∈ Finset.range 32,
      (∑ k ∈ Finset.Icc (0 : ℕ) 15, cellTerm 96 47 (b * 16 + k)) ≤ blockBound b := by
    intro b hb
    have hb' : b < 32 := Finset.mem_range.mp hb
    interval_cases b
    · exact DensityBlockRow96.block_00
    · exact DensityBlockRow96.block_01
    · exact DensityBlockRow96.block_02
    · exact DensityBlockRow96.block_03
    · exact DensityBlockRow96.block_04
    · exact DensityBlockRow96.block_05
    · exact DensityBlockRow96.block_06
    · exact DensityBlockRow96.block_07
    · exact DensityBlockRow96.block_08
    · exact DensityBlockRow96.block_09
    · exact DensityBlockRow96.block_10
    · exact DensityBlockRow96.block_11
    · exact DensityBlockRow96.block_12
    · exact DensityBlockRow96.block_13
    · exact DensityBlockRow96.block_14
    · exact DensityBlockRow96.block_15
    · exact DensityBlockRow96.block_16
    · exact DensityBlockRow96.block_17
    · exact DensityBlockRow96.block_18
    · exact DensityBlockRow96.block_19
    · exact DensityBlockRow96.block_20
    · exact DensityBlockRow96.block_21
    · exact DensityBlockRow96.block_22
    · exact DensityBlockRow96.block_23
    · exact DensityBlockRow96.block_24
    · exact DensityBlockRow96.block_25
    · exact DensityBlockRow96.block_26
    · exact DensityBlockRow96.block_27
    · exact DensityBlockRow96.block_28
    · exact DensityBlockRow96.block_29
    · exact DensityBlockRow96.block_30
    · exact DensityBlockRow96.block_31
  apply (Finset.sum_le_sum h).trans
  norm_num [blockBound, Finset.sum_range_succ]
#print axioms endpoint_upper
#print axioms base_upper
#print axioms sum_upper
end DensityBlockResultRow96
