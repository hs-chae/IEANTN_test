import Mathlib
namespace SynergyAnalytic
open Real Set MeasureTheory Finset
set_option maxHeartbeats 0

noncomputable def logAtanhPoly (n : ℕ) (r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, 2*r^(2*k+1)/(2*k+1:ℕ)
noncomputable def logAtanhError (n : ℕ) (r : ℝ) : ℝ :=
  Real.log (1+r)-Real.log (1-r)-logAtanhPoly n r

theorem logAtanhPoly_deriv (n : ℕ) (r : ℝ) :
    HasDerivAt (logAtanhPoly n) (2*∑ k ∈ Finset.range n, r^(2*k)) r := by
  have hd : ∀ k ∈ Finset.range n,
      HasDerivAt (fun r : ℝ => 2*r^(2*k+1)/(2*k+1:ℕ)) (2*r^(2*k)) r := by
    intro k hk
    have hk0 : (2*k+1:ℝ) ≠ 0 := by positivity
    convert (((hasDerivAt_id r).pow (2*k+1)).const_mul 2).div_const (2*k+1:ℕ) using 1 <;>
      first | rfl | (norm_num <;> field_simp <;> ring)
  convert HasDerivAt.fun_sum hd using 1 <;> first | rfl | simp only [logAtanhPoly, Finset.mul_sum]

theorem logAtanh_geom (n : ℕ) (r : ℝ) :
    (1-r^2)*(∑ k ∈ Finset.range n, r^(2*k)) = 1-r^(2*n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have he : r^(2*(n+1)) = r^(2*n)*r^2 := by rw [Nat.mul_add,pow_add] <;> norm_num
    rw [he]
    nlinarith

theorem logAtanhError_deriv {r : ℝ} (hr : -(1:ℝ) < r) (hr1 : r < 1) (n : ℕ) :
    HasDerivAt (logAtanhError n) (2*r^(2*n)/(1-r^2)) r := by
  have hp : (1:ℝ)+r ≠ 0 := by linarith
  have hm : (1:ℝ)-r ≠ 0 := by linarith
  have hq : (1:ℝ)-r^2 ≠ 0 := by nlinarith
  have h1 := ((hasDerivAt_id r).const_add 1).log hp
  have h2 := ((hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_id r)).log hm
  have hd := (h1.sub h2).sub (logAtanhPoly_deriv n r)
  have hg := logAtanh_geom n r
  convert hd using 1 <;> first | rfl | (dsimp; field_simp [hp,hm,hq]; nlinarith)

#print axioms logAtanhPoly_deriv
#print axioms logAtanhError_deriv
end SynergyAnalytic
