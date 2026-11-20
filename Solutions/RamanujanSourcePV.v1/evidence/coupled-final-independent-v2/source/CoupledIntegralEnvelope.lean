/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import Mathlib

/-! Algebra for retaining a common error integral in the two prime-count
bounds. These lemmas introduce no analytic or numerical input. An application
must still prove its actual integral decomposition, bounds and domain. -/
namespace RamanujanPV.CoupledIntegralEnvelope
set_option autoImplicit false

def envelope (A B k I : ℝ) : ℝ := A - I - k * (B - I)^2

/-- Both estimates use the SAME integral. Increasing it lowers this envelope
under the displayed derivative bound; independent endpoint optimization loses
that dependence. -/
theorem antitone {A B k I U : ℝ} (hIU : I ≤ U) (hk : 0 ≤ k)
    (hderivative : 2*k*(B-I) ≤ 1) : envelope A B k U ≤ envelope A B k I := by
  have hd : 0 ≤ U-I := sub_nonneg.mpr hIU
  have hf : 0 ≤ 1-2*k*(B-I)+k*(U-I) :=
    add_nonneg (sub_nonneg.mpr hderivative) (mul_nonneg hk hd)
  have hprod := mul_nonneg hd hf
  have identity : envelope A B k I - envelope A B k U =
      (U-I)*(1-2*k*(B-I)+k*(U-I)) := by
    unfold envelope
    ring
  rw [← identity] at hprod
  exact sub_nonneg.mp hprod

/-- A lower endpoint for the common integral suffices for the derivative
guard; neither endpoint is required to be nonnegative. -/
theorem antitone_from_lower {A B k L I U : ℝ} (hLI : L ≤ I) (hIU : I ≤ U)
    (hk : 0 ≤ k) (hderivative : 2*k*(B-L) ≤ 1) :
    envelope A B k U ≤ envelope A B k I := by
  apply antitone hIU hk
  have hm : 2*k*(B-I) ≤ 2*k*(B-L) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hLI B) (mul_nonneg (by norm_num) hk)
  exact hm.trans hderivative

/-- Transport bounds for the actual two counts into the common-integral
envelope, retaining the sign needed to square the upper bound. -/
theorem from_counts {A B k I p q : ℝ} (hk : 0 ≤ k) (hp : 0 ≤ p)
    (hP : p ≤ B-I) (hQ : A-I ≤ q) :
    envelope A B k I ≤ q-k*p^2 := by
  have hB : 0 ≤ B-I := hp.trans hP
  have hsquare : p^2 ≤ (B-I)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hP) (add_nonneg hp hB)]
  have hm := mul_le_mul_of_nonneg_left hsquare hk
  unfold envelope
  linarith

theorem at_upper_from_counts {A B k L I U p q : ℝ}
    (hk : 0 ≤ k) (hp : 0 ≤ p) (hP : p ≤ B-I) (hQ : A-I ≤ q)
    (hLI : L ≤ I) (hIU : I ≤ U) (hderivative : 2*k*(B-L) ≤ 1) :
    envelope A B k U ≤ q-k*p^2 :=
  (antitone_from_lower hLI hIU hk hderivative).trans (from_counts hk hp hP hQ)

/-- Exact recovered term relative to independently using I=U in the lower
count and I=0 in the upper count. This is algebra, not a numerical result. -/
theorem retained_term (A B k U : ℝ) :
    envelope A B k U - (A-U-k*B^2) = k*U*(2*B-U) := by
  unfold envelope
  ring

theorem strict_retained_term {A B k U : ℝ} (hk : 0 < k) (hU : 0 < U)
    (hUB : U < 2*B) : A-U-k*B^2 < envelope A B k U := by
  have hpos := mul_pos (mul_pos hk hU) (sub_pos.mpr hUB)
  rw [← retained_term A B k U] at hpos
  exact sub_pos.mp hpos

#print axioms antitone
#print axioms antitone_from_lower
#print axioms from_counts
#print axioms at_upper_from_counts
#print axioms retained_term
#print axioms strict_retained_term
end RamanujanPV.CoupledIntegralEnvelope
