import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import StieltjesTrapezoid

/-! Exact finite coefficients for identifying the actual first Stieltjes sequence
with the derivative of the regular zeta function. No Laurent coefficient or
limiting derivative identity is assumed. This is separate from the619 freeze. -/
namespace RHOcticPush.StieltjesZeta
open Real Set MeasureTheory Filter Finset
open scoped Topology
set_option maxHeartbeats 0

noncomputable def coefficient (n : ℕ) : ℝ :=
  ∫ x in (n:ℝ)..(n+1), (x-n)*(1-log x)/x^2

lemma coefficient_primitive (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => (1-(n:ℝ)/t)*log t-(log t)^2/2)
      ((x-n)*(1-log x)/x^2) x := by
  have h := (((hasDerivAt_const x (1:ℝ)).sub
    ((hasDerivAt_const x (n:ℝ)).div (hasDerivAt_id x) hx)).mul
      (Real.hasDerivAt_log hx)).sub ((Real.hasDerivAt_log hx).pow 2 |>.div_const 2)
  apply h.congr_deriv
  dsimp
  field_simp [hx]
  ring

lemma positive_on_unit (n : ℕ) (hn : 0<n) {x : ℝ}
    (hx : x ∈ uIcc (n:ℝ) (n+1)) : 0<x := by
  rw [uIcc_of_le (by linarith : (n:ℝ) ≤ n+1)] at hx
  exact (Nat.cast_pos.mpr hn).trans_le hx.1

lemma coefficient_eq (n : ℕ) (hn : 0 < n) :
    coefficient n = log (n+1)/(n+1) - ((log (n+1))^2-(log (n:ℝ))^2)/2 := by
  have hi : IntervalIntegrable (fun x : ℝ => (x-n)*(1-log x)/x^2)
      volume (n:ℝ) (n+1) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hp : 0 < x := positive_on_unit n hn hx
    exact (((continuousAt_id.sub continuousAt_const).mul
      (continuousAt_const.sub (Real.continuousAt_log hp.ne'))).div
        (continuousAt_id.pow 2) (pow_ne_zero 2 hp.ne')).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => coefficient_primitive n (by
      have hp : 0 < x := positive_on_unit n hn hx
      exact hp.ne')) hi
  unfold coefficient
  rw [h]
  have h0 : (n:ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have h1 : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp [h0,h1]
  ring

/-- Exact finite Euler-summation identity for the actual locked Stieltjes sequence. -/
theorem coefficient_sum (N : ℕ) :
    (∑ n ∈ Finset.range N, coefficient (n+1)) =
      BoxMellinInputs.v1.stieltjesSeq (N+1) := by
  induction N with
  | zero => norm_num [BoxMellinInputs.v1.stieltjesSeq]
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,coefficient_eq (N+1) (by omega)]
    unfold BoxMellinInputs.v1.stieltjesSeq
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ N+1+1)]
    push_cast
    ring

#print axioms coefficient_sum
#print axioms coefficient_primitive
#print axioms coefficient_eq
end RHOcticPush.StieltjesZeta
