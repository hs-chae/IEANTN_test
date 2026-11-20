/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.AnalyticTransition
import RamanujanPV.CoupledIntegralBounds
import RamanujanPV.CoupledIntegralEnvelope

/-! The actual prime-count partial-summation error is retained in BOTH bounds.
The only new literature input is Büthe2017 final Theorem2(1.6), with its exact
1423..10^19 domain. Existing analytic normalization inputs remain explicit. -/
namespace RamanujanPV.CoupledActualPi
open Real Set MeasureTheory
open AnalyticTransition CoupledIntegralBounds
set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable def deficit (t : ℝ) : ℝ := t-Chebyshev.theta t
noncomputable def weight (t : ℝ) : ℝ := deficit t/(t*(Real.log t)^2)
noncomputable def sharedIntegral (x : ℝ) : ℝ := ∫ t in (2:ℝ)..x, weight t
noncomputable def initialConstant : ℝ := 2/Real.log 2-IEANTN.li 2

/-- Additional source-exact input: Büthe arXiv1511.02032v2 p2 Theorem2(1.6). -/
def ButheThetaUpper : Prop := ∀ t ∈ Icc (1423:ℝ) 10000000000000000000,
    deficit t ≤ (39/20:ℝ)*Real.sqrt t

lemma weight_integrable {a x : ℝ} (ha : 1<a) (hax : a≤x) :
    IntervalIntegrable weight volume a x := by
  have h := (ActualPartialSummation.intervalIntegrable_sub_div ha hax).neg
  simpa only [weight,deficit,neg_div,neg_sub] using h

theorem actual_pi_identity {x : ℝ} (hx : 2≤x) (hoffset : Middle.LiOffsetIdentity) :
    IEANTN.primeCounting x = IEANTN.li x+initialConstant-
      deficit x/Real.log x-sharedIntegral x := by
  have h := ActualPartialSummation.piMinusLi_eq hx
  have he : sharedIntegral x = -(∫ t in (2:ℝ)..x,
      (Chebyshev.theta t-t)/(t*(Real.log t)^2)) := by
    rw [←intervalIntegral.integral_neg]
    unfold sharedIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [weight,deficit]
    ring
  rw [he,hoffset x hx]
  dsimp [initialConstant,deficit]
  linarith

theorem shared_split {y x : ℝ} (hy : 2≤y) (hyx : y≤x) :
    sharedIntegral x = sharedIntegral y + ∫ t in y..x,weight t := by
  have h := intervalIntegral.integral_interval_sub_left
    (weight_integrable (by norm_num : (1:ℝ)<2) (hy.trans hyx))
    (weight_integrable (by norm_num : (1:ℝ)<2) hy)
  dsimp [sharedIntegral]
  linarith

theorem shared_nonneg {y : ℝ} (hy : 2≤y)
    (hθ : ∀ t∈Icc (2:ℝ) y, 0≤deficit t) : 0≤sharedIntegral y := by
  apply intervalIntegral.integral_nonneg hy
  intro t ht
  exact div_nonneg (hθ t ht) (by dsimp;positivity)

lemma sqrt_weight {t : ℝ} (ht : 1<t) :
    Real.sqrt t/(t*(Real.log t)^2)=kernel t := by
  have ht0 : 0<t := by linarith
  have hs : Real.sqrt t≠0 := (Real.sqrt_pos.mpr ht0).ne'
  have hl : Real.log t≠0 := (Real.log_pos ht).ne'
  dsimp [kernel]
  field_simp [ht0.ne',hs,hl]
  nlinarith [Real.sq_sqrt ht0.le]

theorem shared_tail_upper {a y c : ℝ} (ha : 1<a) (hay : a≤y) (hc : 0≤c)
    (hθ : ∀t∈Icc a y, deficit t≤c*Real.sqrt t) :
    (∫t in a..y,weight t)≤c*(∫t in a..y,kernel t) := by
  have h := intervalIntegral.integral_mono_on hay (weight_integrable ha hay)
    ((kernel_intervalIntegrable ha hay).const_mul c) (by
      intro t ht
      have ht1 : 1<t := ha.trans_le ht.1
      have hden : 0≤t*(Real.log t)^2 := by have : 0≤t := by linarith;positivity
      have hh := div_le_div_of_nonneg_right (hθ t ht) hden
      simpa only [weight,mul_div_assoc,sqrt_weight ht1] using hh)
  simpa only [intervalIntegral.integral_const_mul] using h

theorem shared_tail_lower {a y c : ℝ} (ha : 1<a) (hay : a≤y) (hc : 0≤c)
    (hθ : ∀t∈Icc a y,c*Real.sqrt t≤deficit t) :
    c*(∫t in a..y,kernel t)≤∫t in a..y,weight t := by
  have h := intervalIntegral.integral_mono_on hay
    ((kernel_intervalIntegrable ha hay).const_mul c) (weight_integrable ha hay) (by
      intro t ht
      have ht1 : 1<t := ha.trans_le ht.1
      have hden : 0≤t*(Real.log t)^2 := by have : 0≤t := by linarith;positivity
      have hh := div_le_div_of_nonneg_right (hθ t ht) hden
      simpa only [weight,mul_div_assoc,sqrt_weight ht1] using hh)
  simpa only [intervalIntegral.integral_const_mul] using h

/-- The actual common-integral pair, before taking its shared upper bound. -/
theorem counts_with_shared_integral {x y b c J : ℝ}
    (hy : 2≤y) (hyx : y≤x) (hoffset : Middle.LiOffsetIdentity)
    (hθy : deficit y≤c*Real.sqrt y) (hθx : b*Real.sqrt x≤deficit x)
    (hJ : J≤∫t in y..x,weight t) :
    li y+initialConstant-c*Real.sqrt y/Real.log y-sharedIntegral y≤IEANTN.primeCounting y ∧
    IEANTN.primeCounting x≤li x+initialConstant-b*Real.sqrt x/Real.log x-J-sharedIntegral y := by
  have hylog : 0<Real.log y := Real.log_pos (by linarith)
  have hxlog : 0<Real.log x := Real.log_pos (by linarith)
  have hpY := actual_pi_identity hy hoffset
  have hpX := actual_pi_identity (hy.trans hyx) hoffset
  have hsplit := shared_split hy hyx
  have hY := div_le_div_of_nonneg_right hθy hylog.le
  have hX := div_le_div_of_nonneg_right hθx hxlog.le
  constructor <;> linarith

/-- Anchor at log(a)=15, retaining the source point deficit as well as the
source pi bound. No numerical count or desired Ramanujan positivity is assumed. -/
theorem shared_anchor {a : ℝ} (ha : 2≤a) (hau : a≤10000000000000000000)
    (hloga : Real.log a=15) (hoffset : Middle.LiOffsetIdentity)
    (hbuthe : ButhePiLower IEANTN.primeCounting IEANTN.li)
    (hθ : (1/20:ℝ)*Real.sqrt a≤deficit a) :
    sharedIntegral a≤initialConstant+(337/2250:ℝ)*Real.sqrt a := by
  have hp := actual_pi_identity ha hoffset
  have hpi := hbuthe a ⟨ha,hau⟩
  rw [hloga] at hp hpi
  have hdiv := div_le_div_of_nonneg_right hθ (by norm_num : (0:ℝ)≤15)
  norm_num at hpi hdiv
  linarith

/-- Exact common error-integral bound from the same source, with all anchor
constants retained. The initial li normalization constant cancels later. -/
theorem shared_upper {a y : ℝ} (ha : 2≤a) (hay : a≤y)
    (hyu : y≤10000000000000000000) (hloga : Real.log a=15)
    (hoffset : Middle.LiOffsetIdentity)
    (hbuthe : ButhePiLower IEANTN.primeCounting IEANTN.li)
    (hθa : (1/20:ℝ)*Real.sqrt a≤deficit a)
    (hθ : ∀t∈Icc a y,deficit t≤(39/20:ℝ)*Real.sqrt t) :
    sharedIntegral y≤initialConstant+(1561/12375:ℝ)*Real.sqrt a+
      (117/22:ℝ)*Real.sqrt y/(Real.log y)^2 := by
  have han := shared_anchor ha (hay.trans hyu) hloga hoffset hbuthe hθa
  have htail := shared_tail_upper (by linarith : 1<a) hay (by norm_num : (0:ℝ)≤39/20) hθ
  have hkernel := integral_upper (by linarith : 1<a) hay (by rw [hloga])
  have hmul := mul_le_mul_of_nonneg_left hkernel (by norm_num : (0:ℝ)≤39/20)
  have hsplit := shared_split ha hay
  dsimp [phi] at hmul
  rw [hloga] at hmul
  linarith

#print axioms actual_pi_identity
#print axioms shared_split
#print axioms shared_nonneg
#print axioms counts_with_shared_integral
#print axioms shared_anchor
#print axioms shared_upper
end RamanujanPV.CoupledActualPi
