/- Actual source point-function execution and the mathematical meaning of its
   actual output buffers. No computed result or caller representation is assumed. -/
import ScopedC.ArraySourceCallExecute
import ScopedC.ArrayDeclarations
import ScopedC.StateWordEquality
import SynergyHeightC.Bundle
import SynergyHeightC.InitCacheProposal
import SynergyC.ExecutePilot
import SynergyAnalytic.HeightPointConstants

namespace SynergyHeightC.PointExecuteAPI
open ScopedC ScopedC.Syntax ScopedC.Machine
open ScopedNumerical ScopedNumerical.ProofBox
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def declarations : List Decl := [
  {type:="I",name:="c",value:=none}, {type:="I",name:="D",value:=none}]
def mainStatements : List Stmt :=
  match Generated.f_main.body with | .sequence ss => ss | _ => []
def loopStatements : List Stmt :=
  match (mainStatements[6]? : Option Stmt) with
  | some (Stmt.whileLoop _ body) =>
      match body with | Stmt.sequence ss => ss | _ => []
  | _ => []

theorem actual_buffer_declaration : loopStatements[2]? = some (.declare declarations) := by rfl

def cAddress (base : State) : Address := ⟨base.heap.length,0,[]⟩
def dAddress (base : State) : Address := ⟨base.heap.length+1,0,[]⟩
def buffers (base : State) : State :=
  allocate (allocate base "I" "c" (some (uninitializedValue SynergyC.Header.layout 100 "I")))
    "I" "D" (some (uninitializedValue SynergyC.Header.layout 100 "I"))

theorem buffers_from_actual_declaration (call : Call) (base : State) :
    ArrayDeclarations.declarations SynergyC.Header.layout call declarations base =
      some (buffers base) := by rfl

def args (base : State) (input : ProofBox) : List Value :=
  [SynergyC.SourceIntervalMath.represented input,.pointer (cAddress base) true,
    .pointer (dAddress base) true]
def filled (base : State) (c d : ProofBox) : State :=
  allocate (allocate base "I" "c" (some (SynergyC.SourceIntervalMath.represented c)))
    "I" "D" (some (SynergyC.SourceIntervalMath.represented d))

@[irreducible] def run (base : State) (input : ProofBox) : Option (Value × State) :=
  ArraySourceCallExecute.execute SynergyC.Header.layout Bundle.code 128 2048 16
    "pointHeight" (args base input) (buffers base)

def readHasBox (after : State) (address : Address) (box : ProofBox) : Bool :=
  match Machine.read SynergyC.Header.layout after address with
  | none => false
  | some value => SynergyC.ExecutePilot.hasBox value box

def checked (base : State) (input c d : ProofBox) : Bool :=
  match run base input with
  | none => false
  | some (value,after) =>
      StateWordEquality.valueEq 4 value .unit &&
        (readHasBox after (cAddress base) c &&
          (readHasBox after (dAddress base) d &&
            StateWordEquality.stateEq 16 after (filled base c d)))

def modelOutputs (input : ProofBox) : Option (ProofBox × ProofBox) := do
  let values ← SynergyAnalytic.HeightPoint.point SynergyAnalytic.HeightPoint.constantValues input
  let c ← values[SynergyAnalytic.HeightPoint.mainIndex]?
  let d ← values[SynergyAnalytic.HeightPoint.slopeIndex]?
  pure (c,d)

def checkedModel (base : State) (input : ProofBox) : Bool :=
  match modelOutputs input with
  | none => false
  | some (c,d) => checked base input c d

end SynergyHeightC.PointExecuteAPI
