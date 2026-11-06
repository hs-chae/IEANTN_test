/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.GaussianCombination
import OriginalIntegral

namespace PVEvolutionA.Recovery.Gaussian
open Real Set MeasureTheory
set_option maxHeartbeats 0

/-- Elementary shape constraints, proved for each numerical parameter record.
These are scalar inequalities, not a desired moment or prime-error hypothesis. -/
structure Shape (m1 m2 h r0 r1 : ℝ) : Prop where
  m1_nonneg : 0≤m1
  m1_upper : m1≤129/200
  m2_nonneg : 0≤m2
  m2_upper : m2≤23/250
  height_lower : 28≤h
  r0_nonneg : 0≤r0
  r0_upper : r0≤681/500000
  r1_nonneg : 0≤r1
  r1_upper : r1≤23/250000

theorem kernel_continuous (m1 m2 h r0 r1 : ℝ) :
    Continuous (WinnerBetaA.SignedHeight.kernel m1 m2 h r0 r1) := by
  unfold WinnerBetaA.SignedHeight.kernel
  fun_prop

theorem kernel_nonneg (m1 m2 h r0 r1 y : ℝ) :
    0≤WinnerBetaA.SignedHeight.kernel m1 m2 h r0 r1 y := by
  unfold WinnerBetaA.SignedHeight.kernel
  positivity

theorem kernel_dominated {m1 m2 h r0 r1 : ℝ} (hs : Shape m1 m2 h r0 r1) (y : ℝ) :
    WinnerBetaA.SignedHeight.kernel m1 m2 h r0 r1 y ≤ WinnerOriginalDensity.kernelAll y := by
  have hh : 0<h := lt_of_lt_of_le (by norm_num) hs.height_lower
  have hmax : max y 0≤|y| := max_le (le_abs_self y) (abs_nonneg y)
  have hf : 1+max y 0/h≤1+|y|/28 := by
    have h1 := div_le_div_of_nonneg_right hmax hh.le
    have h2 := div_le_div_of_nonneg_left (abs_nonneg y) (by norm_num : (0:ℝ)<28) hs.height_lower
    linarith
  have hm1 := hs.m1_nonneg
  have hm2 := hs.m2_nonneg
  have hr0 := hs.r0_nonneg
  have hr1 := hs.r1_nonneg
  unfold WinnerBetaA.SignedHeight.kernel WinnerOriginalDensity.kernelAll
  gcongr (exp (2*y-(601/2500)*exp (2*y))*
    (sqrt (?_*exp y+?_)*(exp (y/6)*?_+?_)+?_*exp (y/2))^2) <;>
    first | exact hf | exact hs.m1_upper | exact hs.m2_upper | exact hs.r0_upper |
      exact hs.r1_upper | positivity

theorem kernel_integrable {m1 m2 h r0 r1 : ℝ} (hs : Shape m1 m2 h r0 r1) :
    Integrable (WinnerBetaA.SignedHeight.kernel m1 m2 h r0 r1) := by
  apply WinnerOriginalDensity.kernel_integrable.mono'
    (kernel_continuous m1 m2 h r0 r1).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg m1 m2 h r0 r1 y)]
    exact kernel_dominated hs y

theorem low_tail {m1 m2 h r0 r1 : ℝ} (hs : Shape m1 m2 h r0 r1) :
    (∫y in Iic (-20:ℝ),WinnerBetaA.SignedHeight.kernel m1 m2 h r0 r1 y)≤1/100000 := by
  exact (setIntegral_mono_on ((kernel_integrable hs).integrableOn (s:=Iic (-20)))
    WinnerOriginalDensity.low_integrable measurableSet_Iic (fun y _ => kernel_dominated hs y)).trans
    WinnerOriginalDensity.low_tail_bound

theorem high_tail {m1 m2 h r0 r1 : ℝ} (hs : Shape m1 m2 h r0 r1) :
    (∫y in Ioi (3:ℝ),WinnerBetaA.SignedHeight.kernel m1 m2 h r0 r1 y)≤1/100000 := by
  exact (setIntegral_mono_on ((kernel_integrable hs).integrableOn (s:=Ioi 3))
    WinnerOriginalDensity.high_integrable measurableSet_Ioi (fun y _ => kernel_dominated hs y)).trans
    WinnerOriginalDensity.high_tail_bound

/-- All of the infinite tails are retained. This is the exact kernel-budget
contract consumed by the existing count-at-anchor source adapter. -/
theorem full_budget {m1 m2 h r0 r1 ε : ℝ} (hs : Shape m1 m2 h r0 r1)
    (hε : 0<ε) (caps : Fin 12→ℝ) (hcaps : ∀i,basisIntegral i≤caps i) :
    (∫y:ℝ,WinnerBetaA.SignedHeight.kernel m1 m2 h r0 r1 y)≤
      (∑i : Fin 12,coefficient m1 m2 h r0 r1 ε 1 i*caps i)+2/100000 := by
  have hi := kernel_integrable hs
  have hm := finite_integral_le_caps (r1:=r1) caps hs.m1_nonneg hs.m2_nonneg
    (lt_of_lt_of_le (by norm_num) hs.height_lower) hs.r0_nonneg hε hcaps
  have hd := intervalIntegral.integral_Iic_sub_Iic
    (hi.integrableOn (s:=Iic (-20))) (hi.integrableOn (s:=Iic 3))
  have ha := intervalIntegral.integral_Iic_add_Ioi
    (hi.integrableOn (s:=Iic 3)) (hi.integrableOn (s:=Ioi 3))
  linarith [low_tail hs,high_tail hs]

#print axioms full_budget
end PVEvolutionA.Recovery.Gaussian
