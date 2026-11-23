import RamanujanPV.FiniteLogUpperExecute

/-! Reuse of the existing generic, source-closed C logarithm proof at actual
RH frontier inputs. This is not a prime-count proof or a new C algorithm. -/
namespace RHOcticPush.HighLog
open RamanujanPV RamanujanPV.AnalyticTransition
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem source_610 : FiniteLogUpperExecute.SourceExecution 610000000000 29837144450886 := by
  apply FiniteLogUpperExecute.source_execution_from_math
    (two := 549755813888) (k := 39)
  all_goals decide +kernel

theorem log_610 : Real.log (610000000000 : ℝ) ≤ (29837144450886 : ℝ) / (2 : ℝ)^40 :=
  FiniteLogUpperExecute.source_log_upper_sound source_610

theorem source_619 : FiniteLogUpperExecute.SourceExecution 619000000000 29853248245101 := by
  apply FiniteLogUpperExecute.source_execution_from_math
    (two := 549755813888) (k := 39)
  all_goals decide +kernel

theorem log_619 : Real.log (619000000000 : ℝ) ≤ (29853248245101 : ℝ) / (2 : ℝ)^40 :=
  FiniteLogUpperExecute.source_log_upper_sound source_619

theorem source_620 : FiniteLogUpperExecute.SourceExecution 620000000000 29855023082658 := by
  apply FiniteLogUpperExecute.source_execution_from_math
    (two := 549755813888) (k := 39)
  all_goals decide +kernel

theorem log_620 : Real.log (620000000000 : ℝ) ≤ (29855023082658 : ℝ) / (2 : ℝ)^40 :=
  FiniteLogUpperExecute.source_log_upper_sound source_620

theorem source_640 : FiniteLogUpperExecute.SourceExecution 640000000000 29889931145622 := by
  apply FiniteLogUpperExecute.source_execution_from_math
    (two := 549755813888) (k := 39)
  all_goals decide +kernel

theorem log_640 : Real.log (640000000000 : ℝ) ≤ (29889931145622 : ℝ) / (2 : ℝ)^40 :=
  FiniteLogUpperExecute.source_log_upper_sound source_640

/-- A source-executed bound supplies an entire real interval's upper log
endpoint by mathematical monotonicity, not by sampling that interval. -/
theorem covered_upper620 {x : ℝ} (hx : 0 < x) (hcap : x ≤ 620000000000) :
    Real.log x ≤ (29855023082658 : ℝ) / (2 : ℝ)^40 :=
  (Real.log_le_log hx hcap).trans log_620

#print axioms source_610
#print axioms log_610
#print axioms covered_upper620
end RHOcticPush.HighLog
