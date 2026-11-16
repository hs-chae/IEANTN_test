/- Actual emitI composes two executions of the proved source emitU.
The successful service premises are later discharged by its constructive caller. -/
import SynergyHeightC.EmitUService
import SynergyC.IntervalValues
import SynergyC.SourceIntervalMath
namespace SynergyHeightC.EmitISource
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

def frame (caller : State) (box : ProofBox) : State :=
  allocate {caller with env:=[]} "I" "x"
    (some (SynergyC.SourceIntervalMath.represented box))

theorem argument (caller : State) (box : ProofBox)
    (lo : SynergyC.Word512.Range box.lo) (hi : SynergyC.Word512.Range box.hi) :
    bindArgs SynergyC.Header.layout Generated.f_emitI.parameters
      [SynergyC.SourceIntervalMath.represented box] caller=some (frame caller box) :=
  TypedFrames.bind_one SynergyC.Header.layout caller "I" "x" _ _
    (SynergyC.IntervalValues.cast_record _ 98 lo hi)

theorem read_record (pure : Machine.Call) (caller : State) (box : ProofBox) :
    evalExpr SynergyC.Header.layout pure 1 (frame caller box) (.var "x")=
      some (SynergyC.SourceIntervalMath.represented box,frame caller box) :=
  TypedFrames.allocate_eval SynergyC.Header.layout pure 0 {caller with env:=[]}
    "I" "x" _ rfl (by decide) (by decide) (by decide) (by decide)

theorem read_lo (pure : Machine.Call) (caller : State) (box : ProofBox) :
    evalExpr SynergyC.Header.layout pure 2 (frame caller box) (.field "." (.var "x") "lo")=
      some (SynergyC.Word512.value box.lo,frame caller box) :=
  ExpressionTemplates.field SynergyC.Header.layout pure (read_record pure caller box) rfl

theorem read_hi (pure : Machine.Call) (caller : State) (box : ProofBox) :
    evalExpr SynergyC.Header.layout pure 2 (frame caller box) (.field "." (.var "x") "hi")=
      some (SynergyC.Word512.value box.hi,frame caller box) :=
  ExpressionTemplates.field SynergyC.Header.layout pure (read_record pure caller box) rfl

theorem call_word (platform : ScopedIO.WorldIO.Platform) (fault : ScopedIO.WorldIO.FaultPolicy)
    (x : Int) (hx : SynergyC.Word512.Range x) (world : ScopedIO.WorldIO.World) :
    EmitUService.call platform fault "emitU" [SynergyC.Word512.value x] world=
      EmitUService.invoke platform fault x world := by
  have range : 0≤x ∧ x<2^512 := hx
  simp [EmitUService.call,SynergyC.Word512.value,SynergyC.Word512.word,range]

theorem pop_frame (caller : State) (box : ProofBox) :
    Machine.popScope caller (frame caller box)=caller := by
  simp [Machine.popScope,frame,Machine.allocate]

theorem world_hi (pure : Machine.Call) (service : ScopedIO.WorldIO.Call)
    (platform : ScopedIO.WorldIO.Platform) (world : ScopedIO.WorldIO.World)
    (caller : State) (box : ProofBox) (same : world.app=frame caller box) :
    ScopedIO.WorldSource.Eval SynergyC.Header.layout pure service platform
      (.field "." (.var "x") "hi") world world (SynergyC.Word512.value box.hi) := by
  cases world with
  | mk app stream =>
      change app=frame caller box at same
      subst app
      exact .pure (read_hi pure caller box)

theorem installed : Generated.f_emitI∈Bundle.code := by
  rw [Bundle.code_exact]
  exact List.mem_of_getElem? (show Generated.functions[26]?=some Generated.f_emitI by rfl)


#print axioms argument
#print axioms call_word
end SynergyHeightC.EmitISource
