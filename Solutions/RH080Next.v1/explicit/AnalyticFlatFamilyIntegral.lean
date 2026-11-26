/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AnalyticFlatFamilyDirichlet
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real MeasureTheory
namespace RH080Next.AnalyticFlatFamily

def cut (r:ℝ):ℝ:=1/(r*Real.pi)

theorem cut_pos (r:ℝ) (hr:1≤r):0<cut r:=by
  have h:0<r:=by linarith
  unfold cut
  positivity

theorem cut_le_half (r:ℝ) (hr:1≤r):cut r≤1/2:=by
  have h:0<r:=by linarith
  unfold cut
  apply (div_le_iff₀ (mul_pos h Real.pi_pos)).mpr
  nlinarith[Real.pi_gt_three]

theorem integral_csc_cut_half (r:ℝ) (hr:1≤r):
    (∫t in cut r..(1/2:ℝ),1/sin (Real.pi*t))≤log (2*r)/Real.pi:=by
  have hr0:0<r:=by linarith
  have ha:=cut_pos r hr
  have hab:=cut_le_half r hr
  have hcont:ContinuousOn (fun t:ℝ=>1/sin (Real.pi*t)) (Set.Icc (cut r) (1/2)):=by
    apply continuousOn_const.div (by fun_prop)
    intro t ht
    exact (RH080Next.AnalyticFlat64.sin_positive_half t (lt_of_lt_of_le ha ht.1) ht.2).ne'
  have hint:IntervalIntegrable (fun t:ℝ=>1/sin (Real.pi*t)) volume (cut r) (1/2):=hcont.intervalIntegrable_of_Icc hab
  have heq:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=cut r) (b:=(1/2:ℝ))
    (fun t ht=>by
      have hmem:t∈Set.Icc (cut r) (1/2:ℝ):=by simpa only[Set.uIcc_of_le hab] using ht
      exact RH080Next.AnalyticFlat64.cscPrimitive_hasDerivAt t (lt_of_lt_of_le ha hmem.1) hmem.2) hint
  have hcutarg:Real.pi*cut r/2=1/(2*r):=by unfold cut;field_simp
  have hhalfarg:Real.pi*((1:ℝ)/2)/2=Real.pi/4:=by ring
  have hinv0:0<(1:ℝ)/(2*r):=by positivity
  have hinvle:(1:ℝ)/(2*r)≤1/2:=by apply (div_le_iff₀ (by positivity:0<(2:ℝ)*r)).mpr;linarith
  have htan:(1:ℝ)/(2*r)≤tan ((1:ℝ)/(2*r)):=Real.le_tan hinv0.le (by nlinarith[Real.pi_gt_three])
  have hlog:=Real.log_le_log hinv0 htan
  have hlogInv:log ((1:ℝ)/(2*r)) = -log (2*r):=by rw [one_div,Real.log_inv]
  rw[hlogInv] at hlog
  rw[heq]
  unfold RH080Next.AnalyticFlat64.cscPrimitive
  rw[hhalfarg,Real.tan_pi_div_four,Real.log_one,zero_div,hcutarg]
  simp only[zero_sub]
  calc
    -(log (tan ((1:ℝ)/(2*r)))/Real.pi)≤-((-log (2*r))/Real.pi):=
      neg_le_neg (div_le_div_of_nonneg_right hlog Real.pi_pos.le)
    _=log (2*r)/Real.pi:=by ring

theorem periodic_norm_bound (m:ℕ) (hm:0<m):
    (∫t in (0:ℝ)..1,|poly m t|)≤2/Real.pi*(1+log (4*(m:ℝ)-2)):=by
  have hr:=order_ge_one m hm
  have ha:=cut_pos (order m) hr
  have hab:=cut_le_half (order m) hr
  have hr0:0<order m:=by linarith
  have hsmall:(∫t in (0:ℝ)..cut (order m),|poly m t|)≤1/Real.pi:=by
    calc
      _≤∫t in (0:ℝ)..cut (order m),order m:=
        intervalIntegral.integral_mono_on ha.le ((continuous_poly m).abs.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) (fun t _=>poly_abs_le m hm t)
      _=1/Real.pi:=by simp[cut];field_simp
  have hcsc:IntervalIntegrable (fun t:ℝ=>1/sin (Real.pi*t)) volume (cut (order m)) (1/2):=by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply continuousOn_const.div (by fun_prop)
    intro t ht
    exact (RH080Next.AnalyticFlat64.sin_positive_half t (lt_of_lt_of_le ha ht.1) ht.2).ne'
  have hlarge:(∫t in cut (order m)..(1/2:ℝ),|poly m t|)≤log (2*order m)/Real.pi:=by
    calc
      _≤∫t in cut (order m)..(1/2:ℝ),1/sin (Real.pi*t):=
        intervalIntegral.integral_mono_on hab ((continuous_poly m).abs.intervalIntegrable _ _) hcsc
          (fun t ht=>poly_abs_le_csc m hm t (lt_of_lt_of_le ha ht.1) ht.2)
      _≤log (2*order m)/Real.pi:=integral_csc_cut_half (order m) hr
  rw[periodic_norm_eq_twice_half,←intervalIntegral.integral_add_adjacent_intervals
    ((continuous_poly m).abs.intervalIntegrable 0 (cut (order m)))
    ((continuous_poly m).abs.intervalIntegrable (cut (order m)) (1/2))]
  calc
    _≤2*(1/Real.pi+log (2*order m)/Real.pi):=by linarith
    _=2/Real.pi*(1+log (4*(m:ℝ)-2)):=by rw[show 2*order m=4*(m:ℝ)-2 by unfold order;ring];ring

#print axioms periodic_norm_bound
end RH080Next.AnalyticFlatFamily
