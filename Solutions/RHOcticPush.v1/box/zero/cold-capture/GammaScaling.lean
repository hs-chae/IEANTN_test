import GammaMellin

/-! Exact scale transport of the actual convergent cosine Mellin integral. -/
namespace RHOcticPush.BoxGamma
open Real Set MeasureTheory
set_option maxHeartbeats 0

lemma cosine_mellin_scale (s : ℝ) {c : ℝ} (hc : 0<c) :
    (∫ y in Ioi (0:ℝ),(1-Real.cos (c*y))*y^(s-2)) =
      c^(1-s)*(∫ y in Ioi (0:ℝ),(1-Real.cos y)*y^(s-2)) := by
  have h := integral_comp_mul_left_Ioi
    (fun y : ℝ => (1-Real.cos y)*y^(s-2)) 0 hc
  simp only [mul_zero,smul_eq_mul] at h
  have he : (∫ y in Ioi (0:ℝ),(1-Real.cos (c*y))*(c*y)^(s-2)) =
      c^(s-2)*(∫ y in Ioi (0:ℝ),(1-Real.cos (c*y))*y^(s-2)) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [Real.mul_rpow hc.le hy.le]
    ring
  rw [he] at h
  have hp : c^(s-2)*c^(1-s)=c⁻¹ := by
    rw [←Real.rpow_add hc,show (s-2)+(1-s)=(-1:ℝ) by ring,Real.rpow_neg_one]
  apply mul_left_cancel₀ (Real.rpow_pos_of_pos hc (s-2)).ne'
  rw [←mul_assoc,hp,h]

/-- The exact full-domain scaled kernel value, every real positive scale. -/
theorem cosine_mellin_scaled {s c : ℝ} (hs0 : 0<s) (hs1 : s<1) (hc : 0<c) :
    (∫ y in Ioi (0:ℝ),(1-Real.cos (c*y))*y^(s-2)) =
      c^(1-s)*(Real.pi/(2*Real.Gamma (2-s)*Real.cos (Real.pi*s/2))) := by
  rw [cosine_mellin_scale s hc,cosine_mellin hs0 hs1]

#print axioms cosine_mellin_scaled
end RHOcticPush.BoxGamma
