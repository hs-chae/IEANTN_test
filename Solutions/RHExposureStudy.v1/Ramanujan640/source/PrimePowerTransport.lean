import RamAlgebra
import LeanCert.Tactic.IntervalAuto
namespace Ramanujan640
open Real IEANTN Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

lemma primeCounting_zero_of_lt_two {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 2) :
    primeCounting x = 0 := by
  unfold primeCounting
  have hf : ⌊x⌋₊ < 2 := (Nat.floor_lt hx0).2 hx
  have hz := Nat.primeCounting_eq_zero_iff.mpr (show ⌊x⌋₊ ≤ 1 by omega)
  simp [hz]

lemma root64_bound : Real.exp (42/64 : ℝ) < 2 := by
  interval_decide 60 (trust := kernel)

lemma far_power_zero {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 42) {k : ℕ} (hk : 64 ≤ k) :
    primeCounting (exp z ^ (1/(k+1:ℝ))) = 0 := by
  rw [← Real.exp_mul, mul_one_div]
  apply primeCounting_zero_of_lt_two (exp_pos _).le
  apply lt_of_le_of_lt _ root64_bound
  apply Real.exp_le_exp.mpr
  have hk' : (64:ℝ) ≤ k := by exact_mod_cast hk
  have hp : (0:ℝ) < k+1 := by positivity
  apply (div_le_iff₀ hp).2
  nlinarith

theorem riemann_exp_finite64 {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 42) :
    riemannPrimeCounting (exp z) =
      ∑ k ∈ range 64, primeCounting (exp (z/(k+1:ℝ)))/(k+1:ℝ) := by
  unfold riemannPrimeCounting
  rw [tsum_eq_sum (s:=range 64) (fun k hk => by
    have h : 64 ≤ k := by simpa only [mem_range, not_lt] using hk
    rw [far_power_zero hz0 hz h, zero_div])]
  apply sum_congr rfl
  intro k hk
  rw [← Real.exp_mul, mul_one_div]

theorem riemann_minus_pi_exp {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 42) :
    riemannPrimeCounting (exp z)-primeCounting (exp z) =
      ∑ k ∈ range 63, primeCounting (exp (z/(k+2:ℝ)))/(k+2:ℝ) := by
  rw [riemann_exp_finite64 hz0 hz]
  rw [show (64:ℕ)=63+1 by rfl, sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, div_one]
  have he : (∑ k ∈ range 63,
      primeCounting (exp (z/((k:ℝ)+1+1)))/((k:ℝ)+1+1)) =
      ∑ k ∈ range 63, primeCounting (exp (z/(k+2:ℝ)))/(k+2:ℝ) := by
    congr 1
    ext k
    ring_nf
  linarith

noncomputable def deficit (z : ℝ) : ℝ :=
  (li (exp z)-primeCounting (exp z))*z/exp (z/2)
noncomputable def riemannDeficit (z : ℝ) : ℝ :=
  (li (exp z)-riemannPrimeCounting (exp z))*z/exp (z/2)
noncomputable def primePart (z : ℝ) : ℝ :=
  (riemannPrimeCounting (exp z)-primeCounting (exp z))*z/exp (z/2)

theorem deficit_split (z : ℝ) :
    deficit z = riemannDeficit z+primePart z := by
  unfold deficit riemannDeficit primePart
  ring

theorem primePart_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 42) :
    0 ≤ primePart z := by
  unfold primePart
  rw [riemann_minus_pi_exp hz0 hz]
  exact div_nonneg (mul_nonneg (sum_nonneg (by
    intro k hk
    exact div_nonneg (RamanujanPV.primeCounting_nonneg _) (by positivity))) hz0)
    (exp_pos _).le

theorem primePart_square_lower {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 42) :
    z*primeCounting (exp (z/2))/(2*exp (z/2)) ≤ primePart z := by
  have hsum : primeCounting (exp (z/2))/2 ≤
      ∑ k ∈ range 63, primeCounting (exp (z/(k+2:ℝ)))/(k+2:ℝ) := by
    have h := single_le_sum (f:=fun k : ℕ => primeCounting (exp (z/(k+2:ℝ)))/(k+2:ℝ))
      (s:=range 63) (a:=0) (by
        intro k hk
        exact div_nonneg (RamanujanPV.primeCounting_nonneg _) (by positivity)) (by norm_num)
    simpa using h
  unfold primePart
  rw [riemann_minus_pi_exp hz0 hz]
  have h := mul_le_mul_of_nonneg_right hsum hz0
  have hh := div_le_div_of_nonneg_right h (exp_pos (z/2)).le
  simpa only [mul_div_assoc, mul_comm, div_div] using hh

#print axioms riemann_exp_finite64
#print axioms riemann_minus_pi_exp
#print axioms deficit_split
#print axioms primePart_square_lower
end Ramanujan640
