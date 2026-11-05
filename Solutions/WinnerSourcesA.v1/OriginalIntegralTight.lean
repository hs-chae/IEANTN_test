/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OriginalIntegral
import DensityCachedSum
import Lean

namespace WinnerOriginalDensity.Tight
open LeanCert.Core LeanCert.Engine MeasureTheory Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def integrationCfg : DyadicConfig := { precision := -100, taylorDepth := 24 }
def negativeBody := cellExpr (-1) (-20) (5/512)
def positiveBody := cellExpr 1 0 (3/4096)

/-- Concrete native execution of every interval-safe left-cell majorant. -/
theorem negative_check : CH2QRH.DensityComputation.checkUpperBound
    negativeBody 0 2047 (2634/12500) integrationCfg = true := by native_decide
/-- Concrete native execution of every interval-safe right-cell majorant. -/
theorem positive_check : CH2QRH.DensityComputation.checkUpperBound
    positiveBody 0 4095 (336973/100000) integrationCfg = true := by native_decide

private theorem Icc_zero_eq_range (n : ℕ) (hn : 0<n) :
    Finset.Icc 0 (n-1)=Finset.range n := by
  ext k
  simp only [Finset.mem_Icc,Finset.mem_range]
  omega

theorem negative_integral : (∫ y in (-20:ℝ)..0, kernelReal (-1) y) ≤ 2634/12500 := by
  have hg := kernel_grid_integral_bound (-1) (-20) (5/512) 2048
    (by norm_num) (Or.inl rfl) (by norm_num)
  have hs := CH2QRH.DensityComputation.verify_upper negativeBody 0 2047
    (2634/12500) integrationCfg (by decide) negative_check
  rw [show (2047:ℕ)=2048-1 by norm_num,Icc_zero_eq_range 2048 (by decide)] at hs
  simp only [negativeBody,cell_semantics] at hs
  norm_num only [Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat,
    neg_mul,neg_add_rev] at hs hg ⊢
  exact hg.trans hs

theorem positive_integral : (∫ y in (0:ℝ)..3, kernelReal 1 y) ≤ 336973/100000 := by
  have hg := kernel_grid_integral_bound 1 0 (3/4096) 4096
    (by norm_num) (Or.inr rfl) (by norm_num)
  have hs := CH2QRH.DensityComputation.verify_upper positiveBody 0 4095
    (336973/100000) integrationCfg (by decide) positive_check
  rw [show (4095:ℕ)=4096-1 by norm_num,Icc_zero_eq_range 4096 (by decide)] at hs
  simp only [positiveBody,cell_semantics] at hs
  norm_num only [Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at hs hg ⊢
  exact hg.trans hs

theorem full_integral_bound : (∫ y : ℝ, kernelAll y) ≤ (358047/100000:ℝ) := by
  have hn : (∫ y in (-20:ℝ)..0,kernelAll y) ≤ 2634/12500 := by
    convert negative_integral using 1
    apply intervalIntegral.integral_congr
    intro y hy
    exact kernelAll_neg (by simpa using hy.2)
  have hp : (∫ y in (0:ℝ)..3,kernelAll y) ≤ 336973/100000 := by
    convert positive_integral using 1
    apply intervalIntegral.integral_congr
    intro y hy
    exact kernelAll_pos (by simpa using hy.1)
  have h0 := intervalIntegral.integral_Iic_sub_Iic
    (kernel_integrable.integrableOn (s:=Iic (-20)))
    (kernel_integrable.integrableOn (s:=Iic 0))
  have h3 := intervalIntegral.integral_Iic_sub_Iic
    (kernel_integrable.integrableOn (s:=Iic 0))
    (kernel_integrable.integrableOn (s:=Iic 3))
  have ha := intervalIntegral.integral_Iic_add_Ioi
    (kernel_integrable.integrableOn (s:=Iic 3))
    (kernel_integrable.integrableOn (s:=Ioi 3))
  linarith [low_tail_bound,high_tail_bound]


#print axioms full_integral_bound
#print axioms negative_integral
#print axioms positive_integral
end WinnerOriginalDensity.Tight
