import GammaScaling
import BoxPositiveMellin

/-! Actual Box Mellin term evaluation and full convergent Dirichlet-series formula. -/
namespace RHOcticPush.BoxGamma
open Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def boxTermValue (s : ℝ) (n : ℕ+) : ℝ :=
  2*(2*(n:ℝ))^(1-s)/((4*(n:ℝ)^2-1)*Real.Gamma (2-s)*Real.cos (Real.pi*s/2))

/-- The actual source integrand is evaluated; no hardcoded term values are used. -/
theorem actual_box_term {s : ℝ} (hs0 : 0<s) (hs1 : s<1) (n : ℕ+) :
    (∫ y in Ioi (0:ℝ),BoxPositiveMellin.term s n y) = boxTermValue s n := by
  have hn : 0<(n:ℝ) := by exact_mod_cast n.pos
  have hc : 0<2*(n:ℝ) := by positivity
  have he : BoxPositiveMellin.term s n =
      (fun y : ℝ => ((4/Real.pi)/(4*(n:ℝ)^2-1))*((1-Real.cos (2*(n:ℝ)*y))*y^(s-2))) := by
    ext y
    unfold BoxPositiveMellin.term BoxPositiveMellin.positiveTerm
    ring
  rw [he,integral_const_mul,cosine_mellin_scaled hs0 hs1 hc]
  unfold boxTermValue
  have hΓ : Real.Gamma (2-s) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0<2-s)).ne'
  have hcos : 0<Real.cos (Real.pi*s/2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  field_simp
  ring

/-- The complete actual Mellin function equals its evaluated convergent series,
using the separately proved full-strip integral/series exchange. -/
theorem actual_box_mellin_hasSum {s : ℝ} (hs0 : 0<s) (hs1 : s<1) :
    HasSum (boxTermValue s) (BoxMellin.mellin s) := by
  exact (BoxPositiveMellin.actual_mellin_as_series hs0 hs1).congr_fun
    (fun n => (actual_box_term hs0 hs1 n).symm)

theorem actual_box_mellin_series {s : ℝ} (hs0 : 0<s) (hs1 : s<1) :
    BoxMellin.mellin s = ∑' n : ℕ+,boxTermValue s n :=
  (actual_box_mellin_hasSum hs0 hs1).tsum_eq.symm

#print axioms actual_box_term
#print axioms actual_box_mellin_hasSum
#print axioms actual_box_mellin_series
end RHOcticPush.BoxGamma
