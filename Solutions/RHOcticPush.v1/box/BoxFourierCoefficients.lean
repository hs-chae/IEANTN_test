import BoxMellinCoefficients

namespace RHOcticPush.BoxFourier
open Real MeasureTheory Set
set_option maxHeartbeats 0

lemma absolute_sine_integral : (∫ y in (0:ℝ)..Real.pi, |Real.sin y|)=2 := by
  calc
    _ = ∫ y in (0:ℝ)..Real.pi, Real.sin y := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le Real.pi_pos.le] at hy
      exact abs_of_nonneg (Real.sin_nonneg_of_mem_Icc hy)
    _ = 2 := by rw [integral_sin];norm_num

lemma sine_frequency {c : ℝ} (hc : c≠0) (hp : Real.cos (c*Real.pi) = -1) :
    (∫ y in (0:ℝ)..Real.pi, Real.sin (c*y))=2/c := by
  rw [intervalIntegral.integral_comp_mul_left _ hc,integral_sin]
  simp [hp,smul_eq_mul]
  ring

/-- All positive-frequency real Fourier coefficients of the actual absolute sine. -/
theorem cosine_coefficient {n : ℕ} (hn : 1≤n) :
    (∫ y in (0:ℝ)..Real.pi, abs (Real.sin y) * Real.cos (2*(n:ℝ)*y)) =
      -2/(4*(n:ℝ)^2-1) := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have ha : (2*(n:ℝ)+1)≠0 := by linarith
  have hb : (2*(n:ℝ)-1)≠0 := by linarith
  have hcosA : Real.cos ((2*(n:ℝ)+1)*Real.pi) = -1 := by
    rw [show (2*(n:ℝ)+1)*Real.pi = (n:ℝ)*(2*Real.pi)+Real.pi by ring]
    exact Real.cos_nat_mul_two_pi_add_pi n
  have hcosB : Real.cos ((2*(n:ℝ)-1)*Real.pi) = -1 := by
    rw [show (2*(n:ℝ)-1)*Real.pi = (n:ℝ)*(2*Real.pi)-Real.pi by ring]
    exact Real.cos_nat_mul_two_pi_sub_pi n
  have hiA := sine_frequency ha hcosA
  have hiB := sine_frequency hb hcosB
  have hf (y : ℝ) : Real.sin y*Real.cos (2*(n:ℝ)*y)=
      (1/2:ℝ)*(Real.sin ((2*(n:ℝ)+1)*y)-Real.sin ((2*(n:ℝ)-1)*y)) := by
    rw [add_mul,sub_mul,one_mul,Real.sin_add,Real.sin_sub]
    ring
  calc
    _ = ∫ y in (0:ℝ)..Real.pi, Real.sin y*Real.cos (2*(n:ℝ)*y) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le Real.pi_pos.le] at hy
      dsimp only
      rw [abs_of_nonneg (Real.sin_nonneg_of_mem_Icc hy)]
    _ = (1/2:ℝ)*((∫ y in (0:ℝ)..Real.pi,Real.sin ((2*(n:ℝ)+1)*y))-
        ∫ y in (0:ℝ)..Real.pi,Real.sin ((2*(n:ℝ)-1)*y)) := by
      simp_rw [hf]
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub]
      · exact (by fun_prop : Continuous (fun y:ℝ=>Real.sin ((2*(n:ℝ)+1)*y))).intervalIntegrable _ _
      · exact (by fun_prop : Continuous (fun y:ℝ=>Real.sin ((2*(n:ℝ)-1)*y))).intervalIntegrable _ _
    _ = _ := by
      rw [hiA,hiB]
      have hd : 4*(n:ℝ)^2-1≠0 := by nlinarith [sq_nonneg (n:ℝ)]
      rw [show 4*(n:ℝ)^2-1=(2*(n:ℝ)+1)*(2*(n:ℝ)-1) by ring]
      field_simp [ha,hb]
      ring

#print axioms absolute_sine_integral
#print axioms cosine_coefficient
end RHOcticPush.BoxFourier
