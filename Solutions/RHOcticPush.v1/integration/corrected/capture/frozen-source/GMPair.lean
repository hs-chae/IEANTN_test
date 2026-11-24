import GMTransport

/-! Correlated two-height GM transport. The common prefix is cancelled before
absolute values are applied; the actual signed compensation identity is used. -/
namespace RHOcticPush.GM
open Real Set MeasureTheory IEANTN RHContinuation.Ramanujan
set_option maxHeartbeats 0

noncomputable def error (x : ℝ) : ℝ :=
  riemannPrimeCounting x - IEANTN.li x - (Chebyshev.psi x - x) / log x

noncomputable def pairBudget (K y x : ℝ) : ℝ :=
  K * (leading 5 x - leading 5 y + 2 * gmEnvelope y * gmWeight y +
    (919 / 500 : ℝ) / log y) + (exp 1 - K) * ((1551 / 100 : ℝ) + leading 5 y)

/-- A genuine signed two-height bound from the same published source inputs.
It cannot be recovered merely by combining the two scalar absolute envelopes. -/
theorem actual_pair_upper (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {K y x : ℝ} (hK0 : 0 ≤ K) (hK : K ≤ exp 1)
    (hy : exp 15 ≤ y) (hyx : y ≤ x) :
    K * error x - exp 1 * error y ≤ pairBudget K y x := by
  have he15 : (3 : ℝ) ≤ exp (15 : ℝ) := by interval_decide 80 (trust := kernel)
  have hy3 : (3 : ℝ) ≤ y := he15.trans hy
  have hy1 : 1 < y := by linarith
  have hi := actual_gm_weighted_error hRH hGM hy3 hyx
  have hc := actual_riemann_compensation hy1 hyx
  have hd : error x - error y ≤ gmTransport y x := by
    unfold error
    rw [hc]
    exact (le_abs_self _).trans hi
  have hey : |error y| ≤ (1551 / 100 : ℝ) + leading 5 y :=
    actual_J_b5 hRH hGM hP hJ hy
  have hney : -error y ≤ (1551 / 100 : ℝ) + leading 5 y :=
    (neg_le_abs _).trans hey
  have ht := transport_upper (b := 5) (H := 15) (by norm_num) (by norm_num)
    (by norm_num) hy hyx
  have hkd := mul_le_mul_of_nonneg_left hd hK0
  have hke := mul_le_mul_of_nonneg_left hney (sub_nonneg.mpr hK)
  have hkt := mul_le_mul_of_nonneg_left ht hK0
  unfold pairBudget
  nlinarith

theorem actual_pair_lower (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {K y x : ℝ} (hK0 : 0 ≤ K) (hK : K ≤ exp 1)
    (hy : exp 15 ≤ y) (hyx : y ≤ x) :
    -pairBudget K y x ≤ exp 1 * error y - K * error x := by
  have h := actual_pair_upper hRH hGM hP hJ hK0 hK hy hyx
  linarith

#print axioms actual_pair_upper
#print axioms actual_pair_lower
end RHOcticPush.GM
