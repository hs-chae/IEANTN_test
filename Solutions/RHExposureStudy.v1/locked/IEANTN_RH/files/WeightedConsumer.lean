import ThetaSigned

open Real IEANTN

namespace WeightedConsumer

/-- The lower spectral-band provider remains a premise. The cancellation,
the theta positivity, and the actual .99 psi-theta relay are proved here. -/
theorem log_primorial_margin
    (hRH : SharedRH.hypothesis) (hb : Buthe2016.v1.theorem_2_psi)
    {L P γ : ℝ} (hL : 34 ≤ L) (hP : 0 < P)
    (hband : (0.886:ℝ)/(exp (L/2)*L) ≤
      log (P/(exp γ*L)) - (Chebyshev.psi (exp L)-exp L)/(exp L*L)) :
    (1.876:ℝ)/(exp (L/2)*L) ≤
      log (P/(exp γ*log (Chebyshev.theta (exp L)))) := by
  let x := exp L
  let v := exp (L/2)
  let θ := Chebyshev.theta x
  let ψ := Chebyshev.psi x
  change (0.886:ℝ)/(v*L) ≤ log (P/(exp γ*L)) - (ψ-x)/(x*L) at hband
  change (1.876:ℝ)/(v*L) ≤ log (P/(exp γ*log θ))
  have hx : 0 < x := exp_pos L
  have hv : 0 < v := exp_pos (L/2)
  have hL0 : 0 < L := by linarith
  have hlogx : log x = L := log_exp L
  have hv2 : v*v = x := by
    dsimp [v,x]
    rw [← exp_add]
    congr 1
    ring
  obtain ⟨hd, hd'⟩ := ThetaSigned.signed_psi_to_theta hRH hb hL
  change (0.99:ℝ)*v ≤ ψ-θ at hd
  change ψ-θ ≤ (1.01:ℝ)*v at hd'
  have hv4 : 4 ≤ v := by
    change (4:ℝ) ≤ exp (L/2)
    linarith [add_one_le_exp (L/2)]
  have hx4 : 4*v ≤ x := hv2 ▸ mul_le_mul_of_nonneg_right hv4 hv.le
  have hr := (ThetaSigned.psi_relative hRH hb (show 6 ≤ L by linarith)).trans
    (mul_le_mul_of_nonneg_left
      (ThetaSigned.root_error (u0:=6) (n:=3) (by norm_num)
        (by norm_num; linarith) (by norm_num) (by norm_num :
          (1/25:ℝ)*6^2*(1000/2718)^3 ≤ 0.08)) hx.le)
  change |ψ-x| ≤ x*0.08 at hr
  have hθ : 1 < θ := by linarith [(abs_le.mp hr).1]
  have hθ0 : 0 < θ := by linarith
  have htlog : 0 < log θ := log_pos hθ
  have htan1 : log θ - L ≤ (θ-x)/x := by
    have ht := log_le_sub_one_of_pos (div_pos hθ0 hx)
    rw [log_div hθ0.ne' hx.ne', hlogx] at ht
    simpa only [sub_div, div_self hx.ne'] using ht
  have htan2 : log (log θ/L) ≤ (log θ-L)/L := by
    have ht := log_le_sub_one_of_pos (div_pos htlog hL0)
    simpa only [sub_div, div_self hL0.ne'] using ht
  have htan : log (log θ/L) ≤ (θ-x)/(x*L) := by
    calc
      _ ≤ ((θ-x)/x)/L := htan2.trans (div_le_div_of_nonneg_right htan1 hL0.le)
      _ = _ := by ring
  have hlogs : log (P/(exp γ*log θ)) =
      log (P/(exp γ*L)) - log (log θ/L) := by
    rw [log_div hP.ne' (mul_pos (exp_pos γ) htlog).ne',
      log_div hP.ne' (mul_pos (exp_pos γ) hL0).ne',
      log_div htlog.ne' hL0.ne',
      log_mul (exp_pos γ).ne' htlog.ne',
      log_mul (exp_pos γ).ne' hL0.ne']
    ring
  have hvdiv : v/(x*L) = 1/(v*L) := by
    rw [← hv2]
    field_simp [hv.ne', hL0.ne']
  have hdelta := div_le_div_of_nonneg_right hd (mul_pos hx hL0).le
  rw [mul_div_assoc, hvdiv] at hdelta
  rw [hlogs]
  calc
    _ = (0.886:ℝ)/(v*L) + (0.99:ℝ)*(1/(v*L)) := by ring
    _ ≤ (log (P/(exp γ*L)) - (ψ-x)/(x*L)) + (ψ-θ)/(x*L) :=
      add_le_add hband hdelta
    _ = log (P/(exp γ*L)) - (θ-x)/(x*L) := by ring
    _ ≤ _ := sub_le_sub_left htan _
#print axioms log_primorial_margin

end WeightedConsumer
