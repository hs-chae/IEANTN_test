/- Reuse each accepted exact source equality; no arithmetic is reexecuted here. -/
import SourceMomentBudgetsV1.Block15
import SynergyMomentCHi.FamilyAPI
import Mathlib.Tactic.IntervalCases
namespace SourceMomentFamilyV1.Block15
open ScopedNumerical SynergyMomentC SynergyMomentCHi
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
theorem rows (kind : Kind) (i : Nat) (lower : 120 ≤ i) (upper : i < 128) :
 FamilyAPI.ExactRow kind i := by
 interval_cases i
 · cases kind with
   | mass=>exact SourceMomentBudgetsV1.Block15.mass_execution0
   | firstMoment=>exact SourceMomentBudgetsV1.Block15.first_moment_execution0
 · cases kind with
   | mass=>exact SourceMomentBudgetsV1.Block15.mass_execution1
   | firstMoment=>exact SourceMomentBudgetsV1.Block15.first_moment_execution1
 · cases kind with
   | mass=>exact SourceMomentBudgetsV1.Block15.mass_execution2
   | firstMoment=>exact SourceMomentBudgetsV1.Block15.first_moment_execution2
 · cases kind with
   | mass=>exact SourceMomentBudgetsV1.Block15.mass_execution3
   | firstMoment=>exact SourceMomentBudgetsV1.Block15.first_moment_execution3
 · cases kind with
   | mass=>exact SourceMomentBudgetsV1.Block15.mass_execution4
   | firstMoment=>exact SourceMomentBudgetsV1.Block15.first_moment_execution4
 · cases kind with
   | mass=>exact SourceMomentBudgetsV1.Block15.mass_execution5
   | firstMoment=>exact SourceMomentBudgetsV1.Block15.first_moment_execution5
 · cases kind with
   | mass=>exact SourceMomentBudgetsV1.Block15.mass_execution6
   | firstMoment=>exact SourceMomentBudgetsV1.Block15.first_moment_execution6
 · cases kind with
   | mass=>exact SourceMomentBudgetsV1.Block15.mass_execution7
   | firstMoment=>exact SourceMomentBudgetsV1.Block15.first_moment_execution7
#print axioms rows
end SourceMomentFamilyV1.Block15
