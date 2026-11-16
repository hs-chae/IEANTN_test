/- Exact high-only C suffix executions, for arbitrary initialized low fields.
Every guard/operation is checked in the actual existing source execution semantics. -/
import SynergyMomentCHi.BudgetProposed
import SourceMomentSumsV1.Block65
import Lean.Util.CollectAxioms
open Lean Meta Elab Tactic
namespace SourceMomentBudgetsV1.Block65
open ScopedC ScopedC.Machine ScopedNumerical SynergyMomentC
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
def c (j : Nat) (lo : Int) : ProofBox :=
 ⟨lo,(SourceMomentWordsV1.All.word (520+j)).1-21600*ProofBox.scale 128⟩
def d (j : Nat) (lo : Int) : ProofBox :=
 ⟨lo,(SourceMomentWordsV1.All.word (520+j)).2⟩
def massRow (j : Nat) : SynergyMomentMath.Cells.Row :=
 (SourceMomentSumsV1.Block65.mass[j]?).getD ⟨0,⟨0,0⟩,⟨0,0⟩⟩
theorem mass_execution0 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .mass (massRow 0).before 520
   (c 0 cLo) (d 0 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (massRow 0).before (massRow 0).after 520 (c 0 cLo) (d 0 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms mass_execution0
theorem mass_execution1 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .mass (massRow 1).before 521
   (c 1 cLo) (d 1 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (massRow 1).before (massRow 1).after 521 (c 1 cLo) (d 1 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms mass_execution1
theorem mass_execution2 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .mass (massRow 2).before 522
   (c 2 cLo) (d 2 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (massRow 2).before (massRow 2).after 522 (c 2 cLo) (d 2 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms mass_execution2
theorem mass_execution3 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .mass (massRow 3).before 523
   (c 3 cLo) (d 3 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (massRow 3).before (massRow 3).after 523 (c 3 cLo) (d 3 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms mass_execution3
theorem mass_execution4 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .mass (massRow 4).before 524
   (c 4 cLo) (d 4 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (massRow 4).before (massRow 4).after 524 (c 4 cLo) (d 4 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms mass_execution4
theorem mass_execution5 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .mass (massRow 5).before 525
   (c 5 cLo) (d 5 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (massRow 5).before (massRow 5).after 525 (c 5 cLo) (d 5 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms mass_execution5
theorem mass_execution6 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .mass (massRow 6).before 526
   (c 6 cLo) (d 6 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (massRow 6).before (massRow 6).after 526 (c 6 cLo) (d 6 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms mass_execution6
theorem mass_execution7 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .mass (massRow 7).before 527
   (c 7 cLo) (d 7 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (massRow 7).before (massRow 7).after 527 (c 7 cLo) (d 7 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms mass_execution7
def first_momentRow (j : Nat) : SynergyMomentMath.Cells.Row :=
 (SourceMomentSumsV1.Block65.first_moment[j]?).getD ⟨0,⟨0,0⟩,⟨0,0⟩⟩
theorem first_moment_execution0 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .firstMoment (first_momentRow 0).before 520
   (c 0 cLo) (d 0 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (first_momentRow 0).before (first_momentRow 0).after 520 (c 0 cLo) (d 0 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms first_moment_execution0
theorem first_moment_execution1 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .firstMoment (first_momentRow 1).before 521
   (c 1 cLo) (d 1 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (first_momentRow 1).before (first_momentRow 1).after 521 (c 1 cLo) (d 1 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms first_moment_execution1
theorem first_moment_execution2 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .firstMoment (first_momentRow 2).before 522
   (c 2 cLo) (d 2 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (first_momentRow 2).before (first_momentRow 2).after 522 (c 2 cLo) (d 2 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms first_moment_execution2
theorem first_moment_execution3 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .firstMoment (first_momentRow 3).before 523
   (c 3 cLo) (d 3 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (first_momentRow 3).before (first_momentRow 3).after 523 (c 3 cLo) (d 3 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms first_moment_execution3
theorem first_moment_execution4 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .firstMoment (first_momentRow 4).before 524
   (c 4 cLo) (d 4 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (first_momentRow 4).before (first_momentRow 4).after 524 (c 4 cLo) (d 4 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms first_moment_execution4
theorem first_moment_execution5 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .firstMoment (first_momentRow 5).before 525
   (c 5 cLo) (d 5 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (first_momentRow 5).before (first_momentRow 5).after 525 (c 5 cLo) (d 5 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms first_moment_execution5
theorem first_moment_execution6 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .firstMoment (first_momentRow 6).before 526
   (c 6 cLo) (d 6 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (first_momentRow 6).before (first_momentRow 6).after 526 (c 6 cLo) (d 6 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms first_moment_execution6
theorem first_moment_execution7 (cLo dLo : Int) :
 SynergyMomentCHi.Budget.run .firstMoment (first_momentRow 7).before 527
   (c 7 cLo) (d 7 dLo)=some
   (.continuing (SynergyMomentCHi.BudgetProposed.afterProposed
     (first_momentRow 7).before (first_momentRow 7).after 527 (c 7 cLo) (d 7 dLo))) := by
 unfold SynergyMomentCHi.Budget.run
 run_tac do
  let goal←getMainGoal
  let target←goal.getType
  let args:=target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected exact high-only source-state equality"
  goal.assign (←mkEqRefl args[1]!)
#print axioms first_moment_execution7
end
end SourceMomentBudgetsV1.Block65
