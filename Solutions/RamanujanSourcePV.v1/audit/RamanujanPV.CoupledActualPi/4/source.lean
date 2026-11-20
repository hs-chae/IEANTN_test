/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.AnalyticTransition
import RamanujanPV.CoupledIntegralBounds
import RamanujanPV.CoupledIntegralEnvelope
import RamanujanPV.CoupledUniformBounds

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
    deficit t   ≤   (39/20:ℝ)*Real.sqrt t

lemma weight_integrable {a x : ℝ} (ha : 1<a) (hax : a  ≤  x) :
    IntervalIntegrable weight volume a x := by
  have h := (ActualPartialSummation.intervalIntegrable_sub_div ha hax).neg
  convert h using 1
  ext t
  simp only [Pi.neg_apply,weight,deficit]
  ring

theorem actual_pi_identity {x : ℝ} (hx : 2  ≤  x) (hoffset : Middle.LiOffsetIdentity) :
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
  have hneg : deficit x/Real.log x = -((Chebyshev.theta x-x)/Real.log x) := by
    dsimp [deficit]
    ring
  rw [he,hneg,hoffset x hx]
  dsimp [initialConstant]
  linarith

theorem shared_split {y x : ℝ} (hy : 2  ≤  y) (hyx : y  ≤  x) :
    sharedIntegral x = sharedIntegral y + ∫ t in y..x,weight t := by
  have h := intervalIntegral.integral_interval_sub_left
    (weight_integrable (by norm_num : (1:ℝ)<2) (hy.trans hyx))
    (weight_integrable (by norm_num : (1:ℝ)<2) hy)
  dsimp [sharedIntegral]
  linarith

theorem shared_nonneg {y : ℝ} (hy : 2  ≤  y)
    (hθ : ∀ t∈Icc (2:ℝ) y, 0  ≤  deficit t) : 0  ≤  sharedIntegral y := by
  apply intervalIntegral.integral_nonneg hy
  intro t ht
  have ht0 : 0  ≤  t := by linarith [ht.1]
  exact div_nonneg (hθ t ht) (mul_nonneg ht0 (sq_nonneg _))

lemma sqrt_weight {t : ℝ} (ht : 1<t) :
    Real.sqrt t/(t*(Real.log t)^2)=kernel t := by
  have ht0 : 0<t := by linarith
  have hs : Real.sqrt t≠0 := (Real.sqrt_pos.mpr ht0).ne'
  have hl : Real.log t≠0 := (Real.log_pos ht).ne'
  dsimp [kernel]
  field_simp [ht0.ne',hs,hl]
  nlinarith [Real.sq_sqrt ht0.le]

theorem shared_tail_upper {a y c : ℝ} (ha : 1<a) (hay : a  ≤  y) (hc : 0  ≤  c)
    (hθ : ∀t∈Icc a y, deficit t  ≤  c*Real.sqrt t) :
    (∫t in a..y,weight t)  ≤  c*(∫t in a..y,kernel t) := by
  have h := intervalIntegral.integral_mono_on hay (weight_integrable ha hay)
    ((kernel_intervalIntegrable ha hay).const_mul c) (by
      intro t ht
      have ht1 : 1<t := ha.trans_le ht.1
      have ht0 : 0  ≤  t := by linarith
      have hden : 0  ≤  t*(Real.log t)^2 := mul_nonneg ht0 (sq_nonneg _)
      have hh := div_le_div_of_nonneg_right (hθ t ht) hden
      simpa only [weight,mul_div_assoc,sqrt_weight ht1] using hh)
  simpa only [intervalIntegral.integral_const_mul] using h

theorem shared_tail_lower {a y c : ℝ} (ha : 1<a) (hay : a  ≤  y) (hc : 0  ≤  c)
    (hθ : ∀t∈Icc a y,c*Real.sqrt t  ≤  deficit t) :
    c*(∫t in a..y,kernel t)  ≤  ∫t in a..y,weight t := by
  have h := intervalIntegral.integral_mono_on hay
    ((kernel_intervalIntegrable ha hay).const_mul c) (weight_integrable ha hay) (by
      intro t ht
      have ht1 : 1<t := ha.trans_le ht.1
      have ht0 : 0  ≤  t := by linarith
      have hden : 0  ≤  t*(Real.log t)^2 := mul_nonneg ht0 (sq_nonneg _)
      have hh := div_le_div_of_nonneg_right (hθ t ht) hden
      simpa only [weight,mul_div_assoc,sqrt_weight ht1] using hh)
  simpa only [intervalIntegral.integral_const_mul] using h

/-- The actual common-integral pair, before taking its shared upper bound. -/
theorem counts_with_shared_integral {x y b c J : ℝ}
    (hy : 2  ≤  y) (hyx : y  ≤  x) (hoffset : Middle.LiOffsetIdentity)
    (hθy : deficit y  ≤  c*Real.sqrt y) (hθx : b*Real.sqrt x  ≤  deficit x)
    (hJ : J  ≤  ∫t in y..x,weight t) :
    IEANTN.li y+initialConstant-c*Real.sqrt y/Real.log y-sharedIntegral y  ≤  IEANTN.primeCounting y ∧
    IEANTN.primeCounting x  ≤  IEANTN.li x+initialConstant-b*Real.sqrt x/Real.log x-J-sharedIntegral y := by
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
theorem shared_anchor {a : ℝ} (ha : 2  ≤  a) (hau : a  ≤  10000000000000000000)
    (hloga : Real.log a=15) (hoffset : Middle.LiOffsetIdentity)
    (hbuthe : ButhePiLower IEANTN.primeCounting IEANTN.li)
    (hθ : (1/20:ℝ)*Real.sqrt a  ≤  deficit a) :
    sharedIntegral a  ≤  initialConstant+(337/2250:ℝ)*Real.sqrt a := by
  have hp := actual_pi_identity ha hoffset
  have hpi := hbuthe a ⟨ha,hau⟩
  rw [hloga] at hp hpi
  have hdiv := div_le_div_of_nonneg_right hθ (by norm_num : (0:ℝ)  ≤  15)
  norm_num at hpi hdiv
  linarith

/-- Exact common error-integral bound from the same source, with all anchor
constants retained. The initial li normalization constant cancels later. -/
theorem shared_upper {a y : ℝ} (ha : 2  ≤  a) (hay : a  ≤  y)
    (hyu : y  ≤  10000000000000000000) (hloga : Real.log a=15)
    (hoffset : Middle.LiOffsetIdentity)
    (hbuthe : ButhePiLower IEANTN.primeCounting IEANTN.li)
    (hθa : (1/20:ℝ)*Real.sqrt a  ≤  deficit a)
    (hθ : ∀t∈Icc a y,deficit t  ≤  (39/20:ℝ)*Real.sqrt t) :
    sharedIntegral y  ≤  initialConstant+(1561/12375:ℝ)*Real.sqrt a+
      (117/22:ℝ)*Real.sqrt y/(Real.log y)^2 := by
  have han := shared_anchor ha (hay.trans hyu) hloga hoffset hbuthe hθa
  have htail := shared_tail_upper (by linarith : 1<a) hay (by norm_num : (0:ℝ)  ≤  39/20) hθ
  have hkernel := integral_upper (by linarith : 1<a) hay (by rw [hloga])
  have hmul := mul_le_mul_of_nonneg_left hkernel (by norm_num : (0:ℝ)  ≤  39/20)
  have hsplit := shared_split ha hay
  dsimp [phi] at hmul
  rw [hloga] at hmul
  have hh : (39/20:ℝ)*(15/11*(2*Real.sqrt y/(Real.log y)^2-2*Real.sqrt a/15^2)) =
      (117/22:ℝ)*Real.sqrt y/(Real.log y)^2-(13/550:ℝ)*Real.sqrt a := by ring
  rw [hh] at hmul
  linarith

#print axioms actual_pi_identity
#print axioms shared_split
#print axioms shared_nonneg
#print axioms counts_with_shared_integral
#print axioms shared_anchor
#print axioms shared_upper

lemma anchor_lower : (1423:ℝ)  ≤  Real.exp 15 := by
  have he : (2:ℝ)  ≤  Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)  ≤  2) he 15
  have heq : (Real.exp 1)^15=Real.exp (15:ℝ) := by rw [←Real.exp_nat_mul];norm_num
  rw [heq] at h
  norm_num at h
  linarith

lemma anchor_upper : Real.exp 15  ≤  (4000000:ℝ) :=
  CoupledUniformBounds.exp_fifteen_upper.trans (by norm_num)

lemma initialConstant_le_three (hpositive : ButhePiBelowLi) : initialConstant  ≤  3 := by
  have hli2 : 0  ≤  IEANTN.li 2 :=
    (RamanujanPV.primeCounting_nonneg 2).trans (hpositive 2 (by norm_num)).le
  have hlog2 : (2/3:ℝ)  ≤  Real.log 2 := by linarith [log_two_decimal.1]
  have hconst : (2:ℝ)/Real.log 2  ≤  3 := (div_le_iff₀ (by linarith)).2 (by linarith)
  dsimp [initialConstant]
  linarith

noncomputable def coupledEnvelope (x : ℝ) : ℝ :=
  IEANTN.li (x/Real.exp 1)-(39/20:ℝ)*Real.sqrt (x/Real.exp 1)/(Real.log x-1)-
    CoupledUniformBounds.Uerr x-
    (Real.log x/(Real.exp 1*x))*(IEANTN.li x-CoupledUniformBounds.q x/20-
      CoupledUniformBounds.Uerr x)^2

/-- Actual theta/pi source instantiation of the shared-integral envelope.
The remaining scalar derivative guard is an elementary inequality, discharged
on the strip by the separate guard module. No desired positivity is assumed. -/
theorem actual_coupled_envelope {x : ℝ}
    (hx : x ∈ Icc (1250000000000:ℝ) 1490000000000)
    (hoffset : Middle.LiOffsetIdentity)
    (hbuthe : ButhePiLower IEANTN.primeCounting IEANTN.li)
    (hlower : ButheThetaDeficit) (hupper : ButheThetaUpper)
    (hguard : 2*(Real.log x/(Real.exp 1*x))*(IEANTN.li x+initialConstant-
      CoupledUniformBounds.q x/20)  ≤  1) :
    coupledEnvelope x  ≤  IEANTN.primeCounting (x/Real.exp 1)-
      (Real.log x/(Real.exp 1*x))*(IEANTN.primeCounting x)^2 := by
  let y := x/Real.exp 1
  have hx0 : 0<x := by linarith [hx.1]
  have he0 := Real.exp_pos (1:ℝ)
  have he1 : (1:ℝ)  ≤  Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hyx : y  ≤  x := (div_le_iff₀ he0).2 (by dsimp [y];nlinarith)
  have hay : Real.exp 15  ≤  y := by
    apply anchor_upper.trans
    apply (le_div_iff₀ he0).2
    have he := CoupledUniformBounds.exp_one_upper
    nlinarith [hx.1]
  have hy : 2 ≤ y := by linarith [anchor_lower]
  have hyu : y ≤ 10000000000000000000 := by linarith [hx.2]
  have hxU : x ≤ 10000000000000000000 := by linarith [hx.2]
  have ha2 : (2:ℝ) ≤ Real.exp 15 := by linarith [anchor_lower]
  have hda : (1/20:ℝ)*Real.sqrt (Real.exp 15) ≤ deficit (Real.exp 15) := by
    have h := hlower (Real.exp 15) ⟨ha2,hay.trans hyu⟩
    dsimp [deficit]
    linarith
  have hθUpper : ∀t∈Icc (Real.exp 15) y,deficit t ≤ (39/20:ℝ)*Real.sqrt t := by
    intro t ht
    exact hupper t ⟨anchor_lower.trans ht.1,ht.2.trans hyu⟩
  have hIu := shared_upper ha2 hay hyu (by simp) hoffset hbuthe hda hθUpper
  have hlogy : Real.log y=Real.log x-1 := by dsimp [y];rw [Real.log_div hx0.ne' he0.ne',Real.log_exp]
  have hIupper : sharedIntegral y ≤ initialConstant+CoupledUniformBounds.Uerr x := by
    simpa only [CoupledUniformBounds.Uerr,CoupledUniformBounds.K,hlogy,y] using hIu
  have hDn : ∀t∈Icc (2:ℝ) x,0 ≤ deficit t := by
    intro t ht
    have h := hlower t ⟨ht.1,ht.2.trans hxU⟩
    have hs := Real.sqrt_nonneg t
    dsimp [deficit]
    linarith
  have hIn : 0 ≤ sharedIntegral y := shared_nonneg hy (by
    intro t ht
    exact hDn t ⟨ht.1,ht.2.trans hyx⟩)
  have hJ : (0:ℝ) ≤ ∫t in y..x,weight t := by
    apply intervalIntegral.integral_nonneg hyx
    intro t ht
    have ht2 : 2 ≤ t := hy.trans ht.1
    have ht0 : 0 ≤ t := by linarith
    exact div_nonneg (hDn t ⟨ht2,ht.2⟩) (mul_nonneg ht0 (sq_nonneg _))
  have hdy : deficit y ≤ (39/20:ℝ)*Real.sqrt y := hupper y ⟨anchor_lower.trans hay,hyu⟩
  have hdx : (1/20:ℝ)*Real.sqrt x ≤ deficit x := by
    have h := hlower x ⟨by linarith [hx.1],hxU⟩
    dsimp [deficit]
    linarith
  have hcounts := counts_with_shared_integral hy hyx hoffset hdy hdx hJ
  have hk : 0 ≤ Real.log x/(Real.exp 1*x) := by positivity
  have hP : IEANTN.primeCounting x ≤ (IEANTN.li x+initialConstant-CoupledUniformBounds.q x/20)-sharedIntegral y := by
    convert hcounts.2 using 1 <;> dsimp [CoupledUniformBounds.q] <;> ring
  have hQ : (IEANTN.li y+initialConstant-(39/20:ℝ)*Real.sqrt y/(Real.log x-1))-sharedIntegral y ≤ IEANTN.primeCounting y := by
    simpa only [hlogy] using hcounts.1
  have result := CoupledIntegralEnvelope.at_upper_from_counts
    (A:=IEANTN.li y+initialConstant-(39/20:ℝ)*Real.sqrt y/(Real.log x-1))
    (B:=IEANTN.li x+initialConstant-CoupledUniformBounds.q x/20)
    (k:=Real.log x/(Real.exp 1*x)) (L:=0) (I:=sharedIntegral y)
    (U:=initialConstant+CoupledUniformBounds.Uerr x)
    hk (RamanujanPV.primeCounting_nonneg x) hP hQ hIn hIupper (by simpa using hguard)
  convert result using 1 <;> dsimp [coupledEnvelope,CoupledIntegralEnvelope.envelope,y] <;> ring

#print axioms initialConstant_le_three
#print axioms actual_coupled_envelope
end RamanujanPV.CoupledActualPi
