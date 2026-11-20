/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteCellSound
import RamanujanPV.FiniteCellProtected

/-! Actual positive source execution discharges its own input-domain guards.
Only C-argument representability is an applicability assumption. No strict
inequality, successful-effect or prevalidated guard is assumed. -/
namespace RamanujanPV.FiniteCellInverse
open FiniteScalarMachine FiniteCellTrace FiniteCellProtected FiniteCellSound
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

structure Prefix (r : RawFactoredCell) extends WordFits r : Prop where
  nLower : 38358837683 ≤ r.n
  advance : r.n < r.next
  upper : r.next ≤ 2000000000001
  jBound : r.j ≤ r.n
  qBound : r.Q ≤ r.j
  pBound : r.P ≤ r.next-1
  logPositive : 0 < r.Lu

/-- The first seven actual tests cannot be bypassed by a positive return;
all their evaluations preserve the input environment. -/
theorem trace_prefix {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    (fits : WordFits r) (fields : Inputs r s.env) (tr : Trace p c s) :
    tr.s7=s ∧ Prefix r := by
  have h0 := false_test (n_eval fields fits) tr.guard0
  have g1 := tr.guard1
  rw [h0.1] at g1
  have h1 := false_test (advance_eval fields fits) g1
  have g2 := tr.guard2
  rw [h1.1] at g2
  have h2 := false_test (upper_eval fields fits) g2
  have g3 := tr.guard3
  rw [h2.1] at g3
  have h3 := false_test (j_eval fields fits) g3
  have g4 := tr.guard4
  rw [h3.1] at g4
  have h4 := false_test (q_eval fields fits) g4
  have positive : 0<r.next := by omega
  have g5 := tr.guard5
  rw [h4.1] at g5
  have h5 := false_test (p_eval fields fits positive) g5
  have g6 := tr.guard6
  rw [h5.1] at g6
  have h6 := false_test (log_positive_eval fields fits) g6
  exact ⟨h6.1,⟨fits,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩⟩

theorem positive_prefix {r : RawFactoredCell} {s : State}
    (fits : WordFits r)
    (actual : Run FiniteCellExecution.prototypes FiniteCellExecution.service
      FiniteCellSource.cellFunction.body (FiniteCellExecution.input r) (.returned s (i32 1))) :
    Prefix r := by
  obtain ⟨tr⟩ := positive_trace actual
  exact (trace_prefix fits (input_fields r) tr).2

#print axioms trace_prefix
#print axioms positive_prefix
end RamanujanPV.FiniteCellInverse
