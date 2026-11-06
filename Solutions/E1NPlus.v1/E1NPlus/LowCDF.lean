/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.RVM
import E1FrozenN.Interval.ClippedCDF
namespace E1NPlus
open Real Set MeasureTheory
set_option maxHeartbeats 0

theorem sharp_log_moment_identity {U V : ℝ} (hU : 0 < U) (hUV : U ≤ V) :
    (V*log V/(2*Real.pi))/V+(∫t in U..V,(t*log t/(2*Real.pi))/t^2)=
      (log V+(log V^2-log U^2)/2)/(2*Real.pi) := by
  have hV:0<V:=hU.trans_le hUV
  have hd:∀t∈uIcc U V,
      HasDerivAt (fun z:ℝ↦log z^(2:ℕ)/2) (log t/t) t := by
    intro t ht
    rw [uIcc_of_le hUV] at ht
    have ht0:t≠0:=(hU.trans_le ht.1).ne'
    convert! ((Real.hasDerivAt_log ht0).pow 2).div_const 2 using 1 <;> norm_num <;> ring
  have hi:IntervalIntegrable (fun t:ℝ↦log t/t) volume U V := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hUV] at ht
    have ht0:t≠0:=(hU.trans_le ht.1).ne'
    exact ((Real.continuousAt_log ht0).div continuousAt_id ht0).continuousWithinAt
  have hI:=intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have he:(∫t in U..V,(t*log t/(2*Real.pi))/t^2)=
      (∫t in U..V,log t/t)/(2*Real.pi) := by
    calc
      _ = (∫t in U..V,(1/(2*Real.pi))*(log t/t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hUV] at ht
        have ht0:t≠0:=(hU.trans_le ht.1).ne'
        change (t*log t/(2*Real.pi))/t^2=(1/(2*Real.pi))*(log t/t)
        field_simp
      _ = (1/(2*Real.pi))*(∫t in U..V,log t/t) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by ring
  rw [he,hI]
  field_simp
  <;> ring

theorem finite_clipped_sharp_majorant {α:Type*} (S:Finset α) (γ w:α→ℝ)
    {U V:ℝ} (hU:0<U) (hUV:U≤V) (hγV:∀z∈S,γ z≤V)
    (hcount:∀t∈Icc U V,(∑z∈S,if γ z≤t then w z else 0)≤t*log t/(2*Real.pi)) :
    (∑z∈S,w z/max U (γ z))≤
      (log V+(log V^2-log U^2)/2)/(2*Real.pi) := by
  have hF:ContinuousOn (fun t:ℝ↦t*log t/(2*Real.pi)) (uIcc U V) := by
    intro t ht
    rw [uIcc_of_le hUV] at ht
    have ht0:t≠0:=(hU.trans_le ht.1).ne'
    exact (((continuousAt_id.mul (Real.continuousAt_log ht0)).div_const (2*Real.pi))).continuousWithinAt
  have hh:=E1FrozenN.Interval.finite_clipped_reciprocal_majorant S γ w hU hUV hγV
    (fun t↦t*log t/(2*Real.pi)) hF hcount
  rw [sharp_log_moment_identity hU hUV] at hh
  exact hh
#print axioms sharp_log_moment_identity
#print axioms finite_clipped_sharp_majorant
end E1NPlus
