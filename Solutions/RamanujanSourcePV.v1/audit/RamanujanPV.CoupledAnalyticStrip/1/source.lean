/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.CoupledActualPi
import RamanujanPV.CoupledBaseEnvelope
import RamanujanPV.CoupledScalarComparison
import RamanujanPV.CoupledStripGuards

/-! Completed actual-prime-count strip using the retained common theta error.
The one additional literature input is explicitly ButheThetaUpper, final
Büthe2017 Theorem2(1.6). The earlier 24-input ray and all numerical arrays are
unchanged. Exact Taylor endpoint arithmetic is a kernel analytic proof, not a
source-first C execution claim. -/
namespace RamanujanPV.CoupledAnalyticStrip
open Real Set AnalyticTransition CoupledActualPi CoupledUniformBounds
set_option autoImplicit false
set_option maxHeartbeats 0

section Sources
variable (hseries : LogIntegralSeriesIdentity IEANTN.li)
    (hoffset : Middle.LiOffsetIdentity)
    (hpositive : ButhePiBelowLi)
    (hbuthe : ButhePiLower IEANTN.primeCounting IEANTN.li)
    (htheta : ButheThetaDeficit) (hlower : AxlerPiLower)
    (hupper : ButheThetaUpper)

/-- The complete real strip has a proved normalized margin; no prime-count
value, finite Ramanujan positivity or endpoint evaluation is assumed. -/
theorem normalized_margin {x : ℝ}
    (hx : x ∈ Icc (1250000000000:ℝ) 1490000000000) :
    (50:ℝ) < IEANTN.primeCounting (x/exp 1)-
      (log x/(exp 1*x))*(IEANTN.primeCounting x)^2 := by
  have hd : LogIntegralDerivative IEANTN.li := by
    intro t ht
    exact LiBarriers.actual_li_hasDerivAt hoffset ht
  have hA : ∀t∈Icc (1250000000000:ℝ) 1490000000000,
      t/(log t-1-1/log t)<IEANTN.li t := by
    intro t ht
    exact (hlower t (by linarith [ht.1])).trans
      (hpositive t ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hR := CoupledBaseEnvelope.strip_positive hseries hd hA hx
  have hp := CoupledStripGuards.positive_guards hx.1
  have hcomp := CoupledScalarComparison.comparison
    (A:=IEANTN.li (x/exp 1)) (B:=IEANTN.li x)
    (k:=CoupledStripGuards.k x) (q:=q x) (S:=CoupledStripGuards.s x)
    (U:=Uerr x) (J:=0) hp.2.1 hp.2.2 (by norm_num)
    (CoupledStripGuards.s_upper hx.1) (Uerr_uniform hx.1)
    (CoupledStripGuards.li_lower_guard hlower hpositive hx.1 hx.2)
    (by simpa only [add_zero] using CoupledStripGuards.small_product hx.1)
  have hc : CoupledBaseEnvelope.R IEANTN.li x+q x/1000 ≤ coupledEnvelope x := by
    convert hcomp using 1 <;>
      dsimp [CoupledBaseEnvelope.R,coupledEnvelope,CoupledStripGuards.k,CoupledStripGuards.s] <;>
      ring
  have hguard := CoupledStripGuards.antitone_guard hseries hd hx.1 hx.2
    (initialConstant_le_three hpositive)
  have hactual := actual_coupled_envelope hx hoffset hbuthe htheta hupper hguard
  have hq : 0 ≤ q x/1000 := div_nonneg hp.2.1 (by norm_num)
  linarith

/-- Retain the quantitative margin on the actual IEANTN Ramanujan gap. -/
theorem gap9005 {x : ℝ}
    (hx : x ∈ Icc (1250000000000:ℝ) 1490000000000) : (9005:ℝ)<gap x := by
  have hn := normalized_margin hseries hoffset hpositive hbuthe htheta hlower hupper hx
  have hx0 : 0<x := by linarith [hx.1]
  have hL : 0<log x := log_pos (by linarith [hx.1])
  have hLu : log x ≤ 29 := CoupledStripGuards.log_upper hx.2 hx0
  have he : (1:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have hEx : x≤exp 1*x := by nlinarith
  have hf : 0<exp 1*x/log x := div_pos (mul_pos (exp_pos 1) hx0) hL
  have hs := mul_lt_mul_of_pos_left hn hf
  have hid : (exp 1*x/log x)*(IEANTN.primeCounting (x/exp 1)-
      (log x/(exp 1*x))*(IEANTN.primeCounting x)^2)=gap x := by
    dsimp [gap]
    field_simp [hL.ne',hx0.ne',exp_ne_zero 1]
    ring
  rw [hid] at hs
  have hmargin : (9005:ℝ)<(exp 1*x/log x)*50 := by
    apply (lt_div_iff₀ hL).2
    nlinarith [hx.1]
  exact hmargin.trans hs

theorem holds_strip {x : ℝ}
    (hx : x ∈ Icc (1250000000000:ℝ) 1490000000000) : Holds x := by
  apply (holds_iff_gap_pos x).2
  exact (by norm_num : (0:ℝ)<9005).trans
    (gap9005 hseries hoffset hpositive hbuthe htheta hlower hupper hx)
end Sources

#print axioms normalized_margin
#print axioms gap9005
#print axioms holds_strip
end RamanujanPV.CoupledAnalyticStrip
