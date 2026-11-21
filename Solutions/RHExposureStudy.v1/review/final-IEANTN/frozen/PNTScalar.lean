import PNTFormal

open Real IEANTN
namespace PNTStudy

noncomputable def coeffA (L : ℝ) : ℝ :=
  let u := L/2 - log L + log (10/π)
  0.158*L + (u^2-u/3)/(2*π)

theorem scalar_simplify {L : ℝ} (hL : 34 ≤ L) (δ : ℝ) :
    (π/(height L - 1) + (π/height L)^2)*exp L +
        (CH2.v1.CT (height L)+δ)*sqrt (exp L)
      ≤ (coeffA L + δ)*sqrt (exp L) := by
  set T := height L with hT_def
  have hT := (height_conditions hL).1
  have ht0 : 0 < T := by linarith [show (10:ℝ)^7 > 0 by norm_num]
  have ht1 : 0 < T-1 := by linarith [show (10:ℝ)^7 > 1 by norm_num]
  have hL0 : 0 < L := by linarith
  have ht : T*L = 20*exp (L/2) := by
    rw [hT_def, height]
    field_simp
  have hcenter : (π/(T-1)+(π/T)^2)*T ≤ (3.16:ℝ) := by
    have he : (π/(T-1)+(π/T)^2)*T=π+π/(T-1)+π^2/T := by
      field_simp [ht0.ne',ht1.ne'] <;> ring
    rw [he]
    have hπ1 := pi_pos
    have hπ2 := pi_lt_d6
    have h1 : π/(T-1) ≤ (1/1000000:ℝ) := by
      apply (div_le_iff₀ ht1).2
      norm_num at hT
      linarith
    have h2 : π^2/T ≤ (2/1000000:ℝ) := by
      apply (div_le_iff₀ ht0).2
      norm_num at hT
      nlinarith [mul_nonneg hπ1.le (show 0 ≤ 4-π by linarith)]
    linarith
  have hs : sqrt (exp L) = exp (L/2) := (Real.exp_half L).symm
  have hex : exp L = sqrt (exp L)*sqrt (exp L) := (Real.mul_self_sqrt (exp_nonneg L)).symm
  have hnorm : (π/(T-1)+(π/T)^2)*sqrt (exp L) ≤ 0.158*L := by
    rw [hs, ← show T*L/20 = exp (L/2) by linarith]
    have hh := mul_le_mul_of_nonneg_right hcenter (show 0 ≤ L/20 by positivity)
    nlinarith
  have hf : log (T/(2*π)) = L/2-log L+log (10/π) := by
    rw [hT_def,height]
    have heq : (20*exp (L/2)/L)/(2*π) = (exp (L/2)*(10/π))/L := by field_simp; ring
    rw [heq,log_div (by positivity) hL0.ne',log_mul (exp_ne_zero _) (by positivity),log_exp]
    ring
  have hCT : coeffA L = 0.158*L+CH2.v1.CT T := by
    unfold coeffA CH2.v1.CT
    rw [hf]
    ring
  have hh := mul_le_mul_of_nonneg_right hnorm (sqrt_nonneg (exp L))
  rw [hCT]
  nth_rw 1 [hex]
  nlinarith
#print axioms scalar_simplify
end PNTStudy
