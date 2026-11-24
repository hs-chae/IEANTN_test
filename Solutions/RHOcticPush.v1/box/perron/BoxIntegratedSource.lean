import BoxIntegratedDefs
import BoxCDFConstruction

/-! Published general integrated explicit formula, with its actual source constant.
Hildebrand, Introduction to Analytic Number Theory (2013.01.07), Theorem5.18,
equation(5.32), printed166: this source has no Box kernel or smoothing parameter.
The additive constant is deliberately existential because transport cancels it.
The source theorem itself is an explicit literature input, not a new Lean axiom. -/
namespace RHOcticPush.BoxPerron
open Real Set MeasureTheory

/-- The recoverable general source contract, before the proved log-constant
normalization. Multiplicity is encoded by the existing `zetaOrder` convention. -/
def SourceIntegratedPsiRaw : Prop := ∃ C : ℂ, ∀ x : ℝ, 1 < x →
  Summable (zeroPrimitive x) ∧
  (psi1 x : ℂ) = (x : ℂ)^2 / 2 - (∑' ρ, zeroPrimitive x ρ) -
    (x : ℂ) * (deriv riemannZeta 0 / riemannZeta 0) + C -
      ((∑' n : ℕ, trivialPrimitive n x) : ℝ)

theorem integrated_source_normalized (h : SourceIntegratedPsiRaw) :
    SourceIntegratedPsi := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, ?_⟩
  intro x hx
  simpa only [RHOcticPush.BoxCDF.box_log_constant] using hC x hx

/-- The source's lower endpoint0 and our primitive's lower endpoint1 agree
exactly, since the actual Chebyshev function vanishes throughout[0,1]. -/
theorem psi1_integral_from_zero (x : ℝ) : psi1 x = ∫ t in (0:ℝ)..x, Chebyshev.psi t := by
  have hz : (∫ t in (0:ℝ)..1, Chebyshev.psi t) = 0 := by
    calc
      _ = ∫ _t in (0:ℝ)..1, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact Chebyshev.psi_eq_zero_of_le_one (by
          simpa only [max_eq_right (by norm_num : (0:ℝ) ≤ 1)] using ht.2)
      _ = 0 := intervalIntegral.integral_zero
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (Chebyshev.psi_mono.intervalIntegrable (a := 0) (b := 1))
    (Chebyshev.psi_mono.intervalIntegrable (a := 1) (b := x))
  simpa only [hz,zero_add,psi1] using he

#print axioms integrated_source_normalized
#print axioms psi1_integral_from_zero
end RHOcticPush.BoxPerron
