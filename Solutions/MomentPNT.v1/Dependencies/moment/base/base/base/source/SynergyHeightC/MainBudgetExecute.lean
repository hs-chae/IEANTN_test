/- The actual main source's five arithmetic statements after pointHeight.
This interface provides no successful execution until its exact equality is proved. -/
import SynergyHeightC.MainWeightModel
import ScopedC.ArraySourceExecute
namespace SynergyHeightC.MainBudgetExecute
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def before (total : ProofBox) (i : Nat) (c d : ProofBox) : State :=
  PointExecuteAPI.filled (FullMainFrame.base total i) c d

def storeInterval (s : State) (slot : Nat) (value : ProofBox) : State :=
  {s with heap := (s.heap.set slot
    ({type := "I", cells := [some (SynergyC.SourceIntervalMath.represented value)]} : Object))}

def left (i : Nat) : ProofBox := (SynergyAnalytic.HeightPoint.logCell i).getD ⟨0,0⟩
def right (i : Nat) : ProofBox := (SynergyAnalytic.HeightPoint.logCell (i+1)).getD ⟨0,0⟩

def afterC (total : ProofBox) (i : Nat) (c d : ProofBox) : State :=
  storeInterval (before total i c d) 21 (MainWeightModel.adjustedC c)

def afterFC (total : ProofBox) (i : Nat) (c d : ProofBox) : State :=
  allocate (afterC total i c d) "I" "fc"
    (some (SynergyC.SourceIntervalMath.represented (MainWeightModel.fc c)))

def afterFD (total : ProofBox) (i : Nat) (c d : ProofBox) : State :=
  allocate (afterFC total i c d) "I" "fd"
    (some (SynergyC.SourceIntervalMath.represented (MainWeightModel.fd d)))

def afterW (total : ProofBox) (i : Nat) (c d : ProofBox) : State :=
  allocate (afterFD total i c d) "I" "w"
    (some (SynergyC.SourceIntervalMath.represented
      (MainWeightModel.weight (left i) (right i))))

def afterBudget (total : ProofBox) (i : Nat) (c d : ProofBox) : State :=
  storeInterval (afterW total i c d) 17
    (ProofBox.add total (MainWeightModel.term (left i) (right i) c d))

def statements : List Stmt := (PointExecuteAPI.loopStatements.drop 4).take 5

@[irreducible] def run (total : ProofBox) (i : Nat) (c d : ProofBox) :
    Option ArraySourceExecute.Outcome :=
  ArraySourceExecute.statements SynergyC.Header.layout FullMainPrefix.service 128 2048
    statements (before total i c d)

theorem source_of_execution {total c d : ProofBox} {i : Nat}
    (execution : run total i c d=some (.continuing (afterBudget total i c d))) :
    Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout FullMainPrefix.service)
      (ArraySourceCalls.Declare SynergyC.Header.layout FullMainPrefix.service)
      truth ArraySourceCalls.Scope statements (before total i c d)
      (.continuing (afterBudget total i c d)) := by
  have eq : run total i c d=ArraySourceExecute.statements SynergyC.Header.layout
      FullMainPrefix.service 128 2048 statements (before total i c d) := by
    unfold run
    rfl
  have actual := Eq.mp (congrArg (fun result=>result=some
    (.continuing (afterBudget total i c d))) eq) execution
  exact (ArraySourceExecute.sound SynergyC.Header.layout FullMainPrefix.service 128 2048).2.1
    statements (before total i c d) (.continuing (afterBudget total i c d)) actual

#print axioms source_of_execution
end SynergyHeightC.MainBudgetExecute
