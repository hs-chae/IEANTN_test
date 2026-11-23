import FactorialBarrier640
import Log35Barrier640

namespace Ramanujan640.AnalyticBarrier
open Real Set Finset RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable def A (li : ℝ → ℝ) (z : ℝ) : ℝ :=
  Real.exp (-z)*li (Real.exp z)
noncomputable def w (li : ℝ → ℝ) (z : ℝ) : ℝ := z*A li z
noncomputable def pN (N : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ range (N+1), (Nat.factorial k:ℝ)/z^k

theorem A_hasDerivAt {li : ℝ → ℝ} (hderiv : LogIntegralDerivative li)
    {z : ℝ} (hz : 1 < z) : HasDerivAt (A li) (1/z-A li z) z := by
  have he2 : (2:ℝ) < Real.exp z := by
    have he := Real.add_one_le_exp z
    linarith
  have hli := (hderiv (Real.exp z) he2).comp z (Real.hasDerivAt_exp z)
  have hd := (((hasDerivAt_id z).neg).exp).mul hli
  convert! hd using 1 <;> first | rfl | skip
  simp only [A, Pi.neg_apply, id_eq, Function.comp_apply, Real.log_exp, Real.exp_neg]
  have he : Real.exp z ≠ 0 := Real.exp_ne_zero z
  have hz0 : z ≠ 0 := by linarith
  field_simp
  <;> ring

lemma mul_pDiv {N : ℕ} {z : ℝ} (hz : z ≠ 0) : z*pDiv N z = pN N z := by
  unfold pDiv pN
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_succ]
  field_simp

theorem actual_residual_hasDerivAt {li : ℝ → ℝ}
    (hderiv : LogIntegralDerivative li) {N : ℕ} {z : ℝ} (hz : 1 < z) :
    HasDerivAt (fun t => A li t-pDiv N t)
      ((Nat.factorial (N+1):ℝ)/z^(N+2)-(A li z-pDiv N z)) z := by
  have hz0 : z ≠ 0 := by linarith
  convert! (A_hasDerivAt hderiv hz).sub (pDiv_hasDerivAt N hz0) using 1 <;>
    first | rfl | ring

/-- The exact finite-order factorial barrier for the actual li function.
Initial anchors are concrete evaluations, not whole-ray desired conclusions. -/
theorem actual_w_barriers {li : ℝ → ℝ} (hderiv : LogIntegralDerivative li)
    {N : ℕ} {a z C : ℝ} (ha : 1 < a) (haz : a ≤ z) (hC : 0 ≤ C)
    (hanchor : 0 ≤ A li a-pDiv N a ∧
      A li a-pDiv N a ≤ C*(Nat.factorial (N+1):ℝ)/a^(N+2))
    (hsuper : 1 ≤ C*(1-((N+2:ℕ):ℝ)/a)) :
    pN N z ≤ w li z ∧
    w li z ≤ pN N z+C*(Nat.factorial (N+1):ℝ)/z^(N+1) := by
  have ha0 : 0 < a := by linarith
  have hz0 : 0 < z := lt_of_lt_of_le ha0 haz
  have hd : ∀ t ∈ Ici a, HasDerivAt (fun t => A li t-pDiv N t)
      ((Nat.factorial (N+1):ℝ)/t^(N+2)-(A li t-pDiv N t)) t := by
    intro t ht
    exact actual_residual_hasDerivAt hderiv (ha.trans_le ht)
  have hlo := residual_lower ha0 haz hd hanchor.1
  have hup := residual_upper ha0 haz hC hd hanchor.2 hsuper
  have hlo' := mul_nonneg hz0.le hlo
  have hup' := mul_le_mul_of_nonneg_left hup hz0.le
  have hpoly := mul_pDiv (N:=N) hz0.ne'
  have htail : z*(C*(Nat.factorial (N+1):ℝ)/z^(N+2)) =
      C*(Nat.factorial (N+1):ℝ)/z^(N+1) := by
    have hpow : z^(N+2) = z^(N+1)*z := by rw [show N+2=N+1+1 by omega,pow_succ]
    rw [hpow]
    field_simp
  dsimp [w]
  rw [mul_sub, hpoly] at hlo' hup'
  rw [htail] at hup'
  constructor <;> linarith

#print axioms A_hasDerivAt
#print axioms actual_residual_hasDerivAt
#print axioms actual_w_barriers
end Ramanujan640.AnalyticBarrier
