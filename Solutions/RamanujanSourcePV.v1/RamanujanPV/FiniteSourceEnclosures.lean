/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteExpLinked
import RamanujanPV.WindowCells

/-! Actual source e outputs on the finite-cell enclosure path. The log-source
adapter is deliberately separate until its actual execution proof is complete.
No unimplemented log source interface is assumed or imported here. -/
namespace RamanujanPV.FiniteSourceEnclosures
open QuotientCMachine WindowCells
set_option autoImplicit false

/-- Both actual source executions, with the upper function's only call closed
by the executed lower source body. The heap is explicit and unmodified. -/
def SourceEOutputs : Prop :=
  ∃heap lowState highState,
    Run FiniteExpExecute.noCalls FiniteExpSource.lowFunction.body
      (FiniteExpExecute.initial heap) (.returned lowState (.u64 eLo)) ∧
    FiniteExpLinked.LinkedHighRun heap (.returned highState (.u64 eHi))

theorem actual_source_e_outputs : SourceEOutputs := by
  refine ⟨QuotientDriverInit.emptyHeap,FiniteExpExecute.finalState QuotientDriverInit.emptyHeap,
    FiniteExpExecute.initial QuotientDriverInit.emptyHeap,?_,?_⟩
  · simpa [eLo] using FiniteExpExecute.low_function_executes QuotientDriverInit.emptyHeap
  · simpa [eLo,eHi] using FiniteExpLinked.linked_high_executes QuotientDriverInit.emptyHeap

/-- The scaling bounds come from actual C program outputs and their proved
real enclosure, not from an independent hardcoded-constant premise. -/
theorem source_e_scaled (outputs : SourceEOutputs) :
    (eLo:ℝ) ≤ Real.exp 1*(2:ℝ)^60 ∧ Real.exp 1*(2:ℝ)^60 ≤ (eHi:ℝ) := by
  obtain ⟨heap,lowState,highState,low,high⟩ := outputs
  have enclosed := FiniteExpLinked.source_outputs_enclose_e low high
  change (eLo:ℝ)/(2:ℝ)^60 ≤ Real.exp 1 ∧ Real.exp 1 ≤ (eHi:ℝ)/(2:ℝ)^60 at enclosed
  exact ⟨(div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^60)).mp enclosed.1,
    (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^60)).mp enclosed.2⟩

/-- A pure adapter for the separate source-log result. Supplying its explicit
real upper bound here does not itself claim that a source-log program is proved. -/
theorem row_enclosures_of_log_upper {pBase qBase pCount qCount pValue qValue : Nat}
    {pEntries qEntries : Lean.RArray PrimeWindow.Entry} {r : RawFactoredCell}
    (spec : RowSpec pBase qBase pCount qCount pValue qValue pEntries qEntries r)
    (outputs : SourceEOutputs)
    (logUpper : Real.log (r.n:ℝ) ≤ (r.Lu:ℝ)/(2:ℝ)^40) :
    (r.toCell eLo eHi).Enclosures := by
  obtain ⟨pn,step,pend,qn,qend,pval,qval,lu,je,ac,strict,lo,hi,logval,m2,mhi,j2,jhi⟩ := spec
  have sourceE := source_e_scaled outputs
  have hlog : Real.log (r.n:ℝ)*(2:ℝ)^40 ≤ (r.Lu:ℝ) :=
    (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^40)).mp logUpper
  have hexp : Real.exp 1 ≤ (r.n:ℝ) := by
    have lower : (2:ℝ)^35 ≤ (r.n:ℝ) := by exact_mod_cast lo
    linarith [Real.exp_one_lt_d9]
  exact r.toCell_enclosures eLo eHi hexp sourceE.1 sourceE.2 hlog

#print axioms actual_source_e_outputs
#print axioms source_e_scaled
#print axioms row_enclosures_of_log_upper
end RamanujanPV.FiniteSourceEnclosures
