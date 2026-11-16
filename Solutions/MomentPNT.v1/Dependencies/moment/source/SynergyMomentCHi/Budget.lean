/- Exact high-only source arithmetic suffix. Lo fields remain initialized and opaque.
No execution is assumed: each subsequent concrete family must prove run equality. -/
import SynergyMomentCHi.Bindings
import SynergyHeightC.MainBudgetExecute
namespace SynergyMomentCHi.Budget
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical SynergyMomentC
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def before := SynergyHeightC.MainBudgetExecute.before
def storeInterval := SynergyHeightC.MainBudgetExecute.storeInterval
def left := SynergyHeightC.MainBudgetExecute.left
def right := SynergyHeightC.MainBudgetExecute.right

def afterC (total : ProofBox) (i : Nat) (c d : ProofBox) : State :=
  storeInterval (before total i c d) 21 (patched c)
def afterFC (total : ProofBox) (i : Nat) (c d : ProofBox) : State :=
  allocate (afterC total i c d) "I" "fc"
    (some (SynergyC.SourceIntervalMath.represented (SynergyHeightC.MainWeightModel.fc c)))
def afterFD (total : ProofBox) (i : Nat) (c d : ProofBox) : State :=
  allocate (afterFC total i c d) "I" "fd"
    (some (SynergyC.SourceIntervalMath.represented (SynergyHeightC.MainWeightModel.fd d)))
def afterW (total : ProofBox) (i : Nat) (c d : ProofBox) : State :=
  allocate (afterFD total i c d) "I" "w"
    (some (SynergyC.SourceIntervalMath.represented
      (SynergyHeightC.MainWeightModel.weight (left i) (right i))))
def afterBudget (kind : Kind) (total : ProofBox) (i : Nat) (c d : ProofBox) : State :=
  storeInterval (afterW total i c d) 17
    (ProofBox.add total (Model.term kind (left i) (right i) c d))
def statements (kind : Kind) : List Stmt := (loopStatements kind).drop 4 |>.take 5
@[irreducible] def run (kind : Kind) (total : ProofBox) (i : Nat) (c d : ProofBox) :
    Option ArraySourceExecute.Outcome :=
  ArraySourceExecute.statements SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service
    128 2048 (statements kind) (before total i c d)

theorem source_of_execution {kind : Kind} {total c d : ProofBox} {i : Nat}
    (execution : run kind total i c d=some
      (.continuing (afterBudget kind total i c d))) :
    Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
      (ArraySourceCalls.Declare SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
      truth ArraySourceCalls.Scope (statements kind) (before total i c d)
      (.continuing (afterBudget kind total i c d)) := by
  have eq : run kind total i c d=ArraySourceExecute.statements SynergyC.Header.layout
      SynergyHeightC.FullMainPrefix.service 128 2048 (statements kind) (before total i c d) := by
    unfold run
    rfl
  have actual := Eq.mp (congrArg (fun result=>result=some
    (.continuing (afterBudget kind total i c d))) eq) execution
  exact (ArraySourceExecute.sound SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service
    128 2048).2.1 (statements kind) (before total i c d)
      (.continuing (afterBudget kind total i c d)) actual

#print axioms source_of_execution
end SynergyMomentCHi.Budget
