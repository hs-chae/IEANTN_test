/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteWideExpLinked
import RamanujanPV.WindowCells

namespace RamanujanPV.FiniteWideExpEnclosures
open FiniteScalarMachine WindowCells
set_option autoImplicit false

/-- Real enclosure of arbitrary completed source outputs, in the SAME typed
machine as the logarithm/row checker. Outputs are identified by actual source
execution determinism, not by an assumed output equation. -/
theorem source_outputs_enclose_e {p : Prototypes} {c : Service}
    {s t : State} {low high : Value}
    (lower : Run p c FiniteExpSource.lowFunction.body empty (.returned s low))
    (upper : FiniteWideExpLinked.LinkedHighRun t high) :
    (low.number:ℝ)/(2:ℝ)^60 ≤ Real.exp 1 ∧
      Real.exp 1 ≤ (high.number:ℝ)/(2:ℝ)^60 := by
  rw [FiniteWideExpLinked.low_completed_correct lower,FiniteWideExpLinked.high_completed_correct upper]
  simpa [word64,AnalyticTransition.finiteELow_value] using AnalyticTransition.finite_e_enclosure

def SourceEOutputs : Prop := ∃s t,
  Run FiniteWideExpExecute.noPrototypes FiniteWideExpExecute.noCalls FiniteExpSource.lowFunction.body
    empty (.returned s (word64 eLo)) ∧
  FiniteWideExpLinked.LinkedHighRun t (word64 eHi)

theorem actual_source_e_outputs : SourceEOutputs := by
  obtain ⟨s,lower⟩ := FiniteWideExpExecute.low_source_run
  obtain ⟨t,upper⟩ := FiniteWideExpLinked.linked_high_source
  exact ⟨s,t,by simpa [eLo] using lower,by simpa [eLo,eHi] using upper⟩

theorem source_e_scaled (outputs : SourceEOutputs) :
    (eLo:ℝ) ≤ Real.exp 1*(2:ℝ)^60 ∧ Real.exp 1*(2:ℝ)^60 ≤ (eHi:ℝ) := by
  obtain ⟨s,t,lower,upper⟩ := outputs
  have enclosed := source_outputs_enclose_e lower upper
  simp only [word64,Int.cast_natCast] at enclosed
  exact ⟨(div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^60)).mp enclosed.1,
    (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^60)).mp enclosed.2⟩

#print axioms source_outputs_enclose_e
#print axioms actual_source_e_outputs
#print axioms source_e_scaled
end RamanujanPV.FiniteWideExpEnclosures
