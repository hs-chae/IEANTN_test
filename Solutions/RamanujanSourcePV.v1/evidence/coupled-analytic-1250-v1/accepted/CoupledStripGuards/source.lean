/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.AnalyticTransition
import RamanujanPV.CoupledUniformBounds

/-! Elementary guards on the actual closed transition strip. The li bounds
are derived from the existing named source inputs and proved upper barrier.
No new numerical or analytic premise is hidden in a guard. -/
namespace RamanujanPV.CoupledStripGuards
open Real Set AnalyticTransition CoupledUniformBounds
set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable def k (x : ℝ) : ℝ := Real.log x / (Real.exp 1*x)
noncomputable def s (x : ℝ) : ℝ := Real.sqrt (x/Real.exp 1)/(Real.log x-1)

lemma log_upper {x : ℝ} (hx : x ≤ 1490000000000)
    (hx0 : 0<x) : Real.log x ≤ 29 := by
  have h := (Real.log_le_log hx0 hx).trans log_endpoint_bounds.2
  linarith

theorem positive_guards {x : ℝ} (hx : 1250000000000 ≤ x) :
    0 ≤ k x ∧ 0 ≤ q x ∧ 0 ≤ Uerr x := by
  have hx0 : 0<x := by linarith
  have hL := log_lower hx
  have hL0 : 0<Real.log x := by linarith
  refine ⟨?_,?_,?_⟩
  · unfold k; positivity
  · unfold q; positivity
  · unfold Uerr
    exact add_nonneg K_nonneg (by positivity)

theorem s_upper {x : ℝ} (hx : 1250000000000 ≤ x) :
    s x ≤ (3/4:ℝ)*q x := by
  have hx0 : 0<x := by linarith
  have hL := log_lower hx
  have hL0 : 0<Real.log x := by linarith
  have hLm : 0<Real.log x-1 := by linarith
  have he : 0<Real.sqrt (Real.exp 1) := Real.sqrt_pos.mpr (Real.exp_pos 1)
  have hs : Real.sqrt (x/Real.exp 1) ≤ (2/3:ℝ)*Real.sqrt x := by
    rw [Real.sqrt_div hx0.le]
    apply (div_le_iff₀ he).2
    have hm := mul_le_mul_of_nonneg_left
      (show (3/2:ℝ) ≤ Real.sqrt (Real.exp 1) by linarith [sqrt_e_lower])
      (Real.sqrt_nonneg x)
    nlinarith
  have hr : (2/3:ℝ)/(Real.log x-1) ≤ (3/4:ℝ)/Real.log x :=
    (div_le_div_iff₀ hLm hL0).2 (by linarith)
  calc
    s x ≤ ((2/3:ℝ)*Real.sqrt x)/(Real.log x-1) :=
      div_le_div_of_nonneg_right hs hLm.le
    _ = Real.sqrt x*((2/3:ℝ)/(Real.log x-1)) := by ring
    _ ≤ Real.sqrt x*((3/4:ℝ)/Real.log x) :=
      mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg x)
    _ = (3/4:ℝ)*q x := by unfold q; ring

theorem small_product {x : ℝ} (hx : 1250000000000 ≤ x) :
    k x*(q x/20+Uerr x) ≤ (1/1000:ℝ) := by
  have hx0 : 0<x := by linarith
  have hL0 : 0<Real.log x := by linarith [log_lower hx]
  have hs : 0<Real.sqrt x := Real.sqrt_pos.mpr hx0
  have he : 0<Real.exp 1 := Real.exp_pos 1
  have hp := positive_guards hx
  have hz : q x/20+Uerr x ≤ q x := by linarith [Uerr_uniform hx]
  have hm := mul_le_mul_of_nonneg_left hz hp.1
  have hid : k x*q x = 1/(Real.exp 1*Real.sqrt x) := by
    unfold k q
    field_simp [hx0.ne',hL0.ne',he.ne',hs.ne']
    nlinarith [Real.sq_sqrt hx0.le]
  have hr : (1118000:ℝ) ≤ Real.sqrt x :=
    threshold_sqrt_lower.trans (Real.sqrt_le_sqrt hx)
  have he2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hh := mul_le_mul_of_nonneg_right he2 (Real.sqrt_nonneg x)
  have hbig : (1000:ℝ) ≤ Real.exp 1*Real.sqrt x := by linarith
  have hdiv : 1/(Real.exp 1*Real.sqrt x) ≤ (1/1000:ℝ) :=
    (div_le_div_iff₀ (mul_pos he hs) (by norm_num : (0:ℝ)<1000)).2 (by linarith)
  exact hm.trans (hid ▸ hdiv)

theorem li_lower_guard (hlower : AxlerPiLower) (hbelow : ButhePiBelowLi)
    {x : ℝ} (hx : 1250000000000 ≤ x) (hxhi : x ≤ 1490000000000) :
    (94/125:ℝ) ≤ 2*k x*IEANTN.li x := by
  have hx0 : 0<x := by linarith
  have hL := log_lower hx
  have hL0 : 0<Real.log x := by linarith
  have hLm : 0<Real.log x-1 := by linarith
  have hinv : 1/Real.log x ≤ 1 := (div_le_one hL0).2 (by linarith)
  have hd : 0<Real.log x-1-1/Real.log x := by linarith
  have hpi := hlower x (by linarith)
  have hli := hpi.trans (hbelow x ⟨by linarith,by linarith⟩)
  have hweak : x/(Real.log x-1) ≤ IEANTN.li x := by
    refine (div_le_div_of_nonneg_left hx0.le hd ?_).trans hli.le
    exact sub_le_self _ (div_nonneg (by norm_num) hL0.le)
  have he : 0<Real.exp 1 := Real.exp_pos 1
  have heup : Real.exp 1 ≤ (11/4:ℝ) := by linarith [exp_one_upper]
  have hLu := log_upper hxhi hx0
  have hm := mul_le_mul_of_nonneg_right heup hLm.le
  have hn : (94/125:ℝ)*(Real.exp 1*(Real.log x-1)) ≤ 2*Real.log x := by
    nlinarith
  have hquot : (94/125:ℝ) ≤
      2*Real.log x/(Real.exp 1*(Real.log x-1)) :=
    (le_div_iff₀ (mul_pos he hLm)).2 hn
  have hid : 2*k x*(x/(Real.log x-1)) =
      2*Real.log x/(Real.exp 1*(Real.log x-1)) := by
    unfold k
    field_simp [hx0.ne',he.ne',hLm.ne']
    <;> ring
  have hmul := mul_le_mul_of_nonneg_left hweak
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (positive_guards hx).1)
  rw [hid] at hmul
  exact hquot.trans hmul

theorem antitone_guard (hseries : LogIntegralSeriesIdentity IEANTN.li)
    (hderiv : LogIntegralDerivative IEANTN.li)
    {x C0 : ℝ} (hx : 1250000000000 ≤ x) (hxhi : x ≤ 1490000000000)
    (hC0 : C0 ≤ 3) :
    2*k x*(IEANTN.li x+C0-q x/20) ≤ 1 := by
  have hx0 : 0<x := by linarith
  have hL := log_lower hx
  have hLm : 0<Real.log x-2 := by linarith
  have hex : Real.exp 4 ≤ x :=
    (Real.le_log_iff_exp_le hx0).1 (by linarith)
  have hli : IEANTN.li x ≤ x/25 := by
    exact (li_upper_barrier hseries hderiv hex).trans
      (div_le_div_of_nonneg_left hx0.le (by norm_num : (0:ℝ)<25) (by linarith))
  have hp := positive_guards hx
  have hb : IEANTN.li x+C0-q x/20 ≤ x/25+3 := by linarith
  have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : (0:ℝ)≤2) hp.1)
  have hLu := log_upper hxhi hx0
  have he : 0<Real.exp 1 := Real.exp_pos 1
  have hel : (27/10:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hnum : 2*Real.log x*(x/25+3) ≤ Real.exp 1*x := by
    have ha := mul_le_mul_of_nonneg_right hLu (show 0≤x/25+3 by positivity)
    have heprod := mul_le_mul_of_nonneg_right hel hx0.le
    nlinarith
  have hbound : 2*k x*(x/25+3) ≤ 1 := by
    have hid : 2*k x*(x/25+3) = 2*Real.log x*(x/25+3)/(Real.exp 1*x) := by
      unfold k
      ring
    rw [hid]
    exact (div_le_one (mul_pos he hx0)).2 hnum
  exact hm.trans hbound

theorem initial_constant_upper (hbelow : ButhePiBelowLi) :
    2/Real.log 2-IEANTN.li 2 ≤ 3 := by
  have hli : 0 ≤ IEANTN.li 2 :=
    (RamanujanPV.primeCounting_nonneg 2).trans (hbelow 2 (by norm_num)).le
  have hlog : (2/3:ℝ) ≤ Real.log 2 := by linarith [log_two_decimal.1]
  have hd : 2/Real.log 2 ≤ (3:ℝ) :=
    (div_le_iff₀ (show 0<Real.log 2 by linarith)).2 (by linarith)
  linarith

#print axioms positive_guards
#print axioms s_upper
#print axioms small_product
#print axioms li_lower_guard
#print axioms antitone_guard
#print axioms initial_constant_upper
end RamanujanPV.CoupledStripGuards
