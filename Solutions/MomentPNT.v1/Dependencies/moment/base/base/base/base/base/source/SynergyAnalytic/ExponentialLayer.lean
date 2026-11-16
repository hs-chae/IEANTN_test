import SynergyAnalytic.PairedEnvelope
import DensityLayer
namespace SynergyAnalytic
open Real Set MeasureTheory Finset
set_option maxHeartbeats 0

/-- Normalized layer-cake formula for one real part, including values below
the lower strip edge. -/
theorem exponential_layer_point_le {L a b beta : ℝ}
    (hL : 0 ≤ L) (ha : a ≤ beta) (hb : b ≤ beta) :
    Real.exp (L*(b-beta)) ≤ Real.exp (L*(a-beta))+L*
      (∫ s in a..beta, (Iio b).indicator (fun u => Real.exp (L*(u-beta))) s) := by
  have hf : Continuous (fun u : ℝ => Real.exp (L*(u-beta))) := by fun_prop
  by_cases hba : b ≤ a
  · have hi : (∫ s in a..beta, (Iio b).indicator (fun u => Real.exp (L*(u-beta))) s) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards [] with u hu
      rw [uIoc_of_le ha] at hu
      exact Set.indicator_of_notMem (by change ¬u<b;linarith [hu.1]) _
    rw [hi,mul_zero,add_zero]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hL)
  · have hab : a ≤ b := (lt_of_not_ge hba).le
    rw [CH2QRH.integral_strict_cutoff ⟨hab,hb⟩]
    have hd : ∀ u ∈ uIcc a b, HasDerivAt (fun v => Real.exp (L*(v-beta)))
        (L*Real.exp (L*(u-beta))) u := by
      intro u hu
      convert (((hasDerivAt_id u).sub_const beta).const_mul L).exp using 1 <;>
        first | rfl | (simp only [id_eq];ring)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((hf.const_mul L).intervalIntegrable a b)
    rw [intervalIntegral.integral_const_mul] at he
    linarith

/-- A finite weighted family is bounded by ANY continuous cumulative envelope.
The envelope can be a finite positive exponential sum computed once. -/
theorem finite_exponential_envelope {α : Type*} (S : Finset α) (w b : α → ℝ)
    {L beta r : ℝ} {Q : ℝ → ℝ}
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hw : ∀ z ∈ S, 0 ≤ w z)
    (hb : ∀ z ∈ S, b z ≤ beta)
    (htotal : (∑ z ∈ S, w z) ≤ Q (beta-r))
    (hQ : Continuous Q)
    (hcount : ∀ s ∈ Icc (beta-r) beta,
      (∑ z ∈ S, if s<b z then w z else 0) ≤ Q s) :
    (∑ z ∈ S, w z*Real.exp (L*(b z-beta))) ≤ pairedFunctional beta r L Q := by
  classical
  let a := beta-r
  have ha : a ≤ beta := by dsimp [a];linarith
  let f : ℝ → ℝ := fun u => Real.exp (L*(u-beta))
  have hf : Continuous f := by unfold f;fun_prop
  have hind : ∀ z ∈ S, IntervalIntegrable ((Iio (b z)).indicator f) volume a beta := by
    intro z hz
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ha]
    exact hf.continuousOn.integrableOn_Icc.indicator measurableSet_Iio
  have hswap : (∑ z ∈ S, w z*(∫ u in a..beta, (Iio (b z)).indicator f u)) =
      ∫ u in a..beta, ∑ z ∈ S, w z*(Iio (b z)).indicator f u := by
    simp_rw [←intervalIntegral.integral_const_mul]
    exact (intervalIntegral.integral_finsetSum (fun z hz => (hind z hz).const_mul (w z))).symm
  have hpt := Finset.sum_le_sum (s:=S) (fun z hz => mul_le_mul_of_nonneg_left
    (exponential_layer_point_le hL ha (hb z hz)) (hw z hz))
  have he : (∑ z ∈ S, w z*(Real.exp (L*(a-beta))+L*(∫ u in a..beta, (Iio (b z)).indicator f u))) =
      Real.exp (L*(a-beta))*(∑ z ∈ S,w z)+L*(∫ u in a..beta, f u*(∑ z ∈ S,if u<b z then w z else 0)) := by
    calc
      _ = Real.exp (L*(a-beta))*(∑ z ∈ S,w z)+L*(∑ z ∈ S,w z*(∫ u in a..beta,(Iio (b z)).indicator f u)) := by
        rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _ = _ := by
        rw [hswap]
        congr 2
        apply intervalIntegral.integral_congr
        intro u hu
        change (∑ z ∈ S,w z*(Iio (b z)).indicator f u) = f u*(∑ z ∈ S,if u<b z then w z else 0)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hz' : u<b z
        · rw [Set.indicator_of_mem (show u ∈ Iio (b z) from hz'),if_pos hz'];ring
        · rw [Set.indicator_of_notMem (show u ∉ Iio (b z) from hz'),if_neg hz'];ring
  have hleft := mul_le_mul_of_nonneg_left htotal (Real.exp_pos (L*(a-beta))).le
  have hsumI : IntervalIntegrable (fun u => f u*(∑ z ∈ S,if u<b z then w z else 0)) volume a beta := by
    have hi := IntervalIntegrable.sum S (fun z hz => (hind z hz).const_mul (w z))
    apply hi.congr
    intro u hu
    simp only [Finset.sum_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hz' : u<b z
    · rw [Set.indicator_of_mem (show u ∈ Iio (b z) from hz'),if_pos hz'];ring
    · rw [Set.indicator_of_notMem (show u ∉ Iio (b z) from hz'),if_neg hz'];ring
  have hupperI : IntervalIntegrable (fun u => f u*Q u) volume a beta := (hf.mul hQ).intervalIntegrable _ _
  have hright := intervalIntegral.integral_mono_on ha hsumI hupperI (fun u hu =>
    mul_le_mul_of_nonneg_left (hcount u hu) (Real.exp_pos _).le)
  have hh := (hpt.trans_eq he).trans (add_le_add hleft (mul_le_mul_of_nonneg_left hright hL))
  convert hh using 1 <;> first | rfl | (unfold pairedFunctional a f; congr 2;ring)

#print axioms exponential_layer_point_le
#print axioms finite_exponential_envelope
end SynergyAnalytic
