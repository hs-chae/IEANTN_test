import MainTerm640
import TailW640
import LeanCert.Tactic.IntervalAuto

namespace Ramanujan640.RHTail
open Real Set Ramanujan640.AnalyticBarrier
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

noncomputable def a : ℝ := 1/(8*Real.pi)
noncomputable def D (c l : ℝ) : ℝ :=
  c*l^5*(l-1)*exp ((1-l)/2)+(21/10:ℝ)*c*l^6*exp (-l/2)+c^2*l^8*exp (-l)

theorem D_hasDerivAt (c l : ℝ) : HasDerivAt (D c)
    (c/2*l^4*(-l^2+13*l-10)*exp ((1-l)/2)+
      (21/20:ℝ)*c*l^5*(12-l)*exp (-l/2)+c^2*l^7*(8-l)*exp (-l)) l := by
  have h1 := ((((hasDerivAt_id l).pow 5).mul ((hasDerivAt_id l).sub_const 1)).mul
    (((hasDerivAt_const l (1:ℝ)).sub (hasDerivAt_id l)).div_const 2).exp).const_mul c
  have h2 := (((hasDerivAt_id l).pow 6).mul
    (((hasDerivAt_id l).neg).div_const 2).exp).const_mul ((21/10:ℝ)*c)
  have h3 := (((hasDerivAt_id l).pow 8).mul
    ((hasDerivAt_id l).neg).exp).const_mul (c^2)
  convert! (h1.add h2).add h3 using 1 <;>
    first | (funext x; simp [D]; ring) | (simp [D]; ring)

theorem D_antitone {c : ℝ} (hc : 0 ≤ c) : AntitoneOn (D c) (Ici (42:ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro l hl
    exact (D_hasDerivAt c l).continuousAt.continuousWithinAt
  · intro l hl
    exact (D_hasDerivAt c l).differentiableAt.differentiableWithinAt
  · intro l hl
    rw [(D_hasDerivAt c l).deriv]
    have hl42 : (42:ℝ) ≤ l := interior_subset hl
    have hl0 : 0 ≤ l := by linarith
    have hp : -l^2+13*l-10 ≤ 0 := by nlinarith [sq_nonneg (l-42)]
    have h1 : c/2*l^4*(-l^2+13*l-10)*exp ((1-l)/2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) hp) (exp_pos _).le
    have h2 : (21/20:ℝ)*c*l^5*(12-l)*exp (-l/2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) (exp_pos _).le
    have h3 : c^2*l^7*(8-l)*exp (-l) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) (exp_pos _).le
    linarith

theorem a_bounds : 0 ≤ a ∧ a ≤ (25/628:ℝ) := by
  constructor
  · unfold a; positivity
  · have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<8*(314/100))
      (show 8*(314/100:ℝ) ≤ 8*Real.pi by nlinarith [Real.pi_gt_d2])
    norm_num at h
    simpa [a,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using h

theorem D_mono_c {c b l : ℝ} (hc : 0 ≤ c) (hcb : c ≤ b) (hl : 1 ≤ l) :
    D c l ≤ D b l := by
  have hl0 : 0 ≤ l := by linarith
  have hlm : 0 ≤ l-1 := by linarith
  unfold D
  gcongr

theorem D42_kernel : D (25/628:ℝ) 42 ≤ 62/100 := by
  unfold D
  interval_decide 80 (trust := kernel)

theorem uniform_D_bound {l : ℝ} (hl : 42 ≤ l) : D a l ≤ 62/100 := by
  have ha := a_bounds
  have h1 := D_antitone ha.1 (show (42:ℝ) ∈ Ici 42 by simp) hl hl
  have h2 := D_mono_c ha.1 ha.2 (by norm_num : (1:ℝ)≤42)
  exact h1.trans (h2.trans D42_kernel)

#print axioms D_antitone
#print axioms D42_kernel
#print axioms uniform_D_bound
end Ramanujan640.RHTail
