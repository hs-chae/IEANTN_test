/- Actual loop input construction at the first main iteration. The same
source pointEdge function computes both endpoints; no external input table. -/
import SynergyHeightC.FullMainInitialization
namespace SynergyHeightC.FullMainEdge
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def statements : List Stmt := PointExecuteAPI.loopStatements.take 2

theorem actual_edge_statements : statements = [
    .declare [{type:="I",name:="left",value:=some (.call (.var "pointEdge")
      [.var "h",.var "span",.var "i",.var "cells"])}],
    .declare [{type:="I",name:="right",value:=some (.call (.var "pointEdge")
      [.var "h",.var "span",.binary "+" (.var "i") (.nat 1),.var "cells"])}]] := by rfl

def left : ProofBox := (SynergyAnalytic.HeightPoint.logCell 0).getD ⟨0,0⟩
def right : ProofBox := (SynergyAnalytic.HeightPoint.logCell 1).getD ⟨0,0⟩
def afterLeft : State := allocate FullMainPrefix.prefixState "I" "left"
  (some (SynergyC.SourceIntervalMath.represented left))
def afterRight : State := allocate afterLeft "I" "right"
  (some (SynergyC.SourceIntervalMath.represented right))
@[irreducible] def run : Option ArraySourceExecute.Outcome :=
  ArraySourceExecute.statements SynergyC.Header.layout FullMainPrefix.service 128 2048
    statements FullMainPrefix.prefixState

def checked : Bool := ArrayStages.hasNext run afterRight

theorem edges_of_checked (h : checked=true) :
    Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout FullMainPrefix.service)
      (ArraySourceCalls.Declare SynergyC.Header.layout FullMainPrefix.service) truth ArraySourceCalls.Scope
      statements FullMainPrefix.prefixState (.continuing afterRight) := by
  obtain ⟨arena,he⟩ := ArrayStages.hasNext_sound h
  have run_eq : run = ArraySourceExecute.statements SynergyC.Header.layout FullMainPrefix.service
      128 2048 statements FullMainPrefix.prefixState := by unfold run; rfl
  have exec := Eq.mp (congrArg (fun result => result=some
    (.continuing (ArrayStages.withArena afterRight arena))) run_eq) he
  have arena_eq := (NatEffects.statements_effect SynergyC.Header.layout FullMainPrefix.service
    FullMainPrefix.service_keeps 128 2048).2.1 statements FullMainPrefix.prefixState
      (.continuing (ArrayStages.withArena afterRight arena)) exec
  have empty : arena = NatArena.empty := arena_eq
  have same : ArrayStages.withArena afterRight arena = afterRight := by rw [empty]; rfl
  rw [same] at exec
  exact (ArraySourceExecute.sound SynergyC.Header.layout FullMainPrefix.service 128 2048).2.1
    statements FullMainPrefix.prefixState (.continuing afterRight) exec

#print axioms actual_edge_statements
#print axioms edges_of_checked
end SynergyHeightC.FullMainEdge
