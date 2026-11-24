import OcticGreenSource
import OcticFourierMollifier
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Exact Mellin/log-affine normalization for the actual mollified octic weight.
The transform step is proved here; no explicit formula is assumed in this file. -/
namespace RHOcticPush.MellinNormalize
open Set MeasureTheory
open scoped FourierTransform
open RHOcticPush.PhysicalWeight RHOcticPush.GreenSource RHOcticPush.Mollifier
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma green_mellin_eq (W : ℝ → ℝ) (s : ℂ) :
    RHOcticPush.GreenSource.mellin W s = _root_.mellin (fun t : ℝ => (W t : ℂ)) s := by
  unfold RHOcticPush.GreenSource.mellin _root_.mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  dsimp only
  rw [Complex.cpow_sub s 1 ht0, Complex.cpow_one]
  simp only [smul_eq_mul]
  ring

lemma green_scale (j : ℕ) (C L : ℝ) (s : ℂ) :
    (2 : ℂ) ^ s * RHOcticPush.GreenSource.mellin (greenWeight j C L) s =
      RHOcticPush.GreenSource.mellin (logWeight j C L) s := by
  rw [green_mellin_eq, green_mellin_eq]
  change (2 : ℂ) ^ s *
    _root_.mellin (fun t : ℝ => (logWeight j C L (2 * t) : ℂ)) s = _
  rw [mellin_comp_mul_left (fun t : ℝ => (logWeight j C L t : ℂ)) s
    (by norm_num : (0 : ℝ) < 2)]
  simp only [smul_eq_mul]
  norm_num
  rw [← mul_assoc, ← Complex.cpow_add s (-s) (by norm_num : (2 : ℂ) ≠ 0)]
  simp

lemma affine_integral (g : ℝ → ℂ) {δ : ℝ} (hδ : 0 < δ) (L : ℝ) :
    (∫ v : ℝ, g ((v - L) / δ)) = (δ : ℂ) * ∫ u : ℝ, g u := by
  calc
    _ = ∫ v : ℝ, g (v / δ) := by
      simpa only [sub_eq_add_neg] using
        (integral_add_right_eq_self (-L) (f := fun v : ℝ => g (v / δ)))
    _ = _ := by
      rw [Measure.integral_comp_div, abs_of_pos hδ, ← Complex.coe_smul, smul_eq_mul]

lemma sqrt_exp_complex (v : ℝ) :
    ((Real.sqrt (Real.exp v) : ℝ) : ℂ) = Complex.exp ((v : ℂ) / 2) := by
  rw [← Real.exp_half, Complex.ofReal_exp]
  congr 1
  push_cast
  rfl

lemma log_integrand (j : ℕ) (C L v : ℝ) (s : ℂ) :
    Real.exp v • ((logWeight j C L (Real.exp v) : ℂ) *
      (Real.exp v : ℂ) ^ s / (Real.exp v : ℂ)) =
      (smoothKernel j ((v - L) / EvenKernel.δ C L) : ℂ) *
        Complex.exp ((s - 1 / 2) * (v : ℂ)) := by
  have hx : (Real.exp v : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero v
  have hpow : (Real.exp v : ℂ) ^ s = Complex.exp ((v : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero hx, ← Complex.ofReal_log (Real.exp_pos v).le,
      Real.log_exp]
  have hquot : (Real.exp v : ℂ) ^ s / (Real.sqrt (Real.exp v) : ℂ) =
      Complex.exp ((s - 1 / 2) * (v : ℂ)) := by
    rw [hpow, sqrt_exp_complex, ← Complex.exp_sub]
    congr 1
    ring
  simp only [logWeight, Real.exp_pos, if_pos, Real.log_exp, Complex.ofReal_div]
  rw [← Complex.coe_smul, smul_eq_mul]
  calc
    _ = (smoothKernel j ((v - L) / EvenKernel.δ C L) : ℂ) *
        ((Real.exp v : ℂ) ^ s / (Real.sqrt (Real.exp v) : ℂ)) := by
      field_simp [hx]
      <;> ring
    _ = _ := by rw [hquot]

lemma log_weight_integral (j : ℕ) (C L : ℝ) (s : ℂ) :
    RHOcticPush.GreenSource.mellin (logWeight j C L) s =
      ∫ v : ℝ, (smoothKernel j ((v - L) / EvenKernel.δ C L) : ℂ) *
        Complex.exp ((s - 1 / 2) * (v : ℂ)) := by
  unfold RHOcticPush.GreenSource.mellin
  rw [← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards with v
  exact log_integrand j C L v s

/-- Entire Mellin parameter, not only critical-line zeros. The pole s=1 can
reuse this same normalization and the known evenness/cosh conversion. -/
theorem actual_mellin (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) (s : ℂ) :
    RHOcticPush.GreenSource.mellin (logWeight j C L) s =
      (EvenKernel.δ C L : ℂ) * Complex.exp ((s - 1 / 2) * (L : ℂ)) *
        ∫ u : ℝ, (smoothKernel j u : ℂ) *
          Complex.exp ((s - 1 / 2) * (EvenKernel.δ C L : ℂ) * (u : ℂ)) := by
  rw [log_weight_integral]
  let g : ℝ → ℂ := fun u => (smoothKernel j u : ℂ) *
    Complex.exp ((s - 1 / 2) * ((L + EvenKernel.δ C L * u : ℝ) : ℂ))
  have hcan (v : ℝ) : L + EvenKernel.δ C L * ((v - L) / EvenKernel.δ C L) = v := by
    field_simp [hδ.ne']
    <;> ring
  have he := affine_integral g hδ L
  simp only [g, hcan] at he
  rw [he]
  have hexp (u : ℝ) : Complex.exp ((s - 1 / 2) *
      ((L + EvenKernel.δ C L * u : ℝ) : ℂ)) =
      Complex.exp ((s - 1 / 2) * (L : ℂ)) *
        Complex.exp ((s - 1 / 2) * (EvenKernel.δ C L : ℂ) * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hexp]
  simp_rw [mul_left_comm (smoothKernel j _ : ℂ)
    (Complex.exp ((s - 1 / 2) * (L : ℂ)))]
  rw [integral_const_mul]
  ring


/-- The actual critical-line specialization, with Mathlib's exact negative
frequency -delta*gamma/(2pi) and the original positive Mellin convention. -/
theorem critical_mellin (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L)
    (s : ℂ) (hs : s.re = 1 / 2) :
    RHOcticPush.GreenSource.mellin (logWeight j C L) s =
      Complex.exp (Complex.I * ((s.im * L : ℝ) : ℂ)) * (EvenKernel.δ C L : ℂ) *
        𝓕 (fun u : ℝ => (smoothKernel j u : ℂ))
          (-(EvenKernel.δ C L * s.im) / (2 * Real.pi)) := by
  have hrep : s - 1 / 2 = Complex.I * (s.im : ℂ) := by
    apply Complex.ext <;> simp [hs]
  rw [actual_mellin j hδ s, hrep,
    Real.fourier_real_eq_integral_exp_smul]
  have hreal (u : ℝ) : -2 * Real.pi * u *
      (-(EvenKernel.δ C L * s.im) / (2 * Real.pi)) = EvenKernel.δ C L * s.im * u := by
    field_simp
    <;> ring
  have hphase (u : ℝ) : (((EvenKernel.δ C L * s.im * u : ℝ) : ℂ) * Complex.I) =
      Complex.I * (s.im : ℂ) * (EvenKernel.δ C L : ℂ) * (u : ℂ) := by
    push_cast
    ring
  have hhead : Complex.I * (s.im : ℂ) * (L : ℂ) =
      Complex.I * ((s.im * L : ℝ) : ℂ) := by push_cast; ring
  simp_rw [hreal, smul_eq_mul, hphase]
  rw [hhead]
  have hi : (∫ u : ℝ, Complex.exp (Complex.I * (s.im : ℂ) *
      (EvenKernel.δ C L : ℂ) * (u : ℂ)) * (smoothKernel j u : ℂ)) =
      ∫ u : ℝ, (smoothKernel j u : ℂ) * Complex.exp (Complex.I * (s.im : ℂ) *
        (EvenKernel.δ C L : ℂ) * (u : ℂ)) := by
    apply integral_congr_ae
    filter_upwards with u
    ring
  rw [hi]
  ring

def properZero (z : PsiSmoothing.Zero) : ProperZero :=
  ⟨z.val, by
    intro h
    have hr := congrArg Complex.re h
    have hz := z.property.1.2
    norm_num at hr
    linarith, z.property.2.2⟩

/-- Source's full Mellin packet equals the actual smooth Fourier packet,
including the integer order of vanishing and the scaling X=2. -/
theorem critical_source_packet (rh : RiemannHypothesis) (j : ℕ) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) (z : PsiSmoothing.Zero) :
    sourcePacket (greenWeight j C L) 2 (properZero z) =
      RHOcticPush.FourierMollifier.actualSmoothZeroPacket j C L z := by
  have hr := RHLimit.NicolasMass.zero_re rh (RHOcticPush.Convergence.zeroEquiv z)
  change z.val.re = 1 / 2 at hr
  unfold sourcePacket
  change (IEANTN.zetaOrder z : ℂ) * (2 : ℂ) ^ z.val *
    RHOcticPush.GreenSource.mellin (greenWeight j C L) z.val = _
  rw [mul_assoc, green_scale, critical_mellin j hδ z.val hr]
  unfold RHOcticPush.FourierMollifier.actualSmoothZeroPacket
  ring

#print axioms critical_mellin
#print axioms critical_source_packet

#print axioms green_scale
#print axioms actual_mellin
end RHOcticPush.MellinNormalize
