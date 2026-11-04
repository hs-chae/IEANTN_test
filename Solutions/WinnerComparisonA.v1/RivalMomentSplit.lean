/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import RivalMomentMath
namespace WinnerRivalMoments
open Real MeasureTheory
set_option maxHeartbeats 0

noncomputable def fullMoment (b : ℝ) (n : ℕ) : ℝ :=
  ∫y in (-12:ℝ)..3,exp (b*y-(2371/10000)*exp (2*y))*y^n

theorem moment_reflect (b y : ℝ) (n : ℕ) :
    moment true b n (-y)=(-1:ℝ)^n*moment false b n y := by
  simp only [moment,ite_true,Bool.false_eq_true,ite_false,mul_neg,neg_mul]
  rw [neg_pow]
  ring

theorem full_split (b : ℝ) (n : ℕ) :
    fullMoment b n=(-1:ℝ)^n*(∫y in (0:ℝ)..12,moment false b n y)+
      ∫y in (0:ℝ)..3,moment true b n y := by
  have hc:=moment_continuous true b n
  have hr:(∫y in (0:ℝ)..12,moment true b n (-y))=
      ∫y in (-12:ℝ)..0,moment true b n y := by
    simpa using (intervalIntegral.integral_comp_neg (f:=moment true b n) (a:=(0:ℝ)) (b:=(12:ℝ)))
  have hi:(∫y in (-12:ℝ)..0,moment true b n y)=
      (-1:ℝ)^n*(∫y in (0:ℝ)..12,moment false b n y) := by
    rw [←hr]
    simp only [moment_reflect,intervalIntegral.integral_const_mul]
  have ha:=intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ:=volume) (-12) 0) (hc.intervalIntegrable (μ:=volume) 0 3)
  have hf:fullMoment b n=∫y in (-12:ℝ)..3,moment true b n y := by
    simp only [fullMoment,moment,ite_true]
  rw [hf,←ha,hi]

#print axioms full_split
end WinnerRivalMoments
