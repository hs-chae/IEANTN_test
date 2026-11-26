/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AnalyticFlatFamilyNodes
import AnalyticFlatFamilyIntegral
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real MeasureTheory RH080Next.Explicit Filter
namespace RH080Next.AnalyticFlatFamily

def normCap (m : ℕ) : ℝ := 2/Real.pi*(1+log (4*(m:ℝ)-2))
def width (m : ℕ) (α : ℝ) : ℝ :=
  (2*(m:ℝ)/order m)*(α+(1+log (4*(m:ℝ)-2))/Real.pi)

theorem actual_norm_le (hNorm : SourceBRFourierNormFive) (m : ℕ) (hm : 0<m) :
    brAmplitudeMass (nodes m) m≤normCap m := by
  have heq:=hNorm (nodes m) m hm (nodes_length m) (terminal_zero m)
  unfold brAmplitudeMass normCap
  rw [heq]
  simp_rw [polynomial_identity m hm]
  exact periodic_norm_bound m hm

theorem width_positive (m : ℕ) (hm : 0<m) (α : ℝ) (hα : 0≤α) : 0<width m α := by
  have hmR:0<(m:ℝ):=by exact_mod_cast hm
  have hr:=order_ge_one m hm
  have hr0:0<order m:=by linarith
  have harg:1≤4*(m:ℝ)-2:=by unfold order at hr;linarith
  have hlog:0≤log (4*(m:ℝ)-2):=Real.log_nonneg harg
  unfold width
  positivity

theorem width_mass_identity (m : ℕ) (hm : 0<m) (α : ℝ) :
    width m α*(order m/(m:ℝ))-normCap m=2*α := by
  have hmR:0<(m:ℝ):=by exact_mod_cast hm
  have hr0:0<order m:=lt_of_lt_of_le (by norm_num) (order_ge_one m hm)
  unfold width normCap
  field_simp
  <;> ring

/-- Arbitrary flat mesh, with a strictly positive coefficient allowance.
No endpoint attainment is inferred from the weak analytic norm bound.
This route is kernel-only analytic and is not program verification. -/
theorem actual_population_curve (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1) (hRH : RiemannHypothesis)
    (m : ℕ) (hm : 0<m) (α ε : ℝ) (hα : 0≤α) (hε : 0<ε) :
    IEANTN.CMSFunctional.GoodCoefficient α (width m α+ε) := by
  have hmR:0<(m:ℝ):=by exact_mod_cast hm
  have hr0:0<order m:=lt_of_lt_of_le (by norm_num) (order_ge_one m hm)
  have hD:0<order m/(m:ℝ):=div_pos hr0 hmR
  apply source_BR_population_goodCoefficient hUniform (nodes m) m hm
    (by rw [nodes_length]; omega) (by rw [nodes_length])
    (by rw [nodes_length]; exact terminal_zero m)
    1 (by norm_num) (window_bound m hm) (attained_maximum m hm)
    (by rw [denominator m hm]; exact hD)
    (width m α+ε) α (by linarith [width_positive m hm α hα]) _ hRH
  rw [denominator m hm]
  have hn:=actual_norm_le hNorm m hm
  have hid:=width_mass_identity m hm α
  have hεD:=mul_pos hε hD
  apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2*1)).mpr
  nlinarith

/-- Genuine population infimum consequence with nonempty and bounded-below
set proved from actual positive-margin coefficients. The coefficient itself
is not asserted to be attained at the analytic endpoint. -/
theorem actual_population_infimum (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1) (hRH : RiemannHypothesis)
    (m : ℕ) (hm : 0<m) (α : ℝ) (hα : 0≤α) :
    (IEANTN.CMSFunctional.goodCoefficients α).Nonempty ∧
      sInf (IEANTN.CMSFunctional.goodCoefficients α)≤width m α := by
  have hne:(IEANTN.CMSFunctional.goodCoefficients α).Nonempty:=
    ⟨width m α+1,actual_population_curve hNorm hUniform hRH m hm α 1 hα (by norm_num)⟩
  refine ⟨hne,?_⟩
  have hb:BddBelow (IEANTN.CMSFunctional.goodCoefficients α):=by
    refine ⟨0,?_⟩
    intro c hc
    exact hc.1.le
  apply le_of_forall_pos_le_add
  intro ε hε
  exact csInf_le hb (actual_population_curve hNorm hUniform hRH m hm α ε hα hε)

#print axioms actual_norm_le
#print axioms actual_population_curve
#print axioms actual_population_infimum
end RH080Next.AnalyticFlatFamily
