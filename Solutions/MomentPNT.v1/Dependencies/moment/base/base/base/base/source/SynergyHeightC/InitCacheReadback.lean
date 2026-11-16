/- Conditional readback from an untrusted state proposal.
   Source execution must separately prove that the returned state equals it. -/
import SynergyHeightC.InitCacheModelIdentity
import SynergyC.UnitBody

namespace SynergyHeightC.InitCacheReadback
open ScopedC ScopedC.Machine
open SynergyC.Word512 SynergyC.WordFrames
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024

def maxContext (arena : NatArena.Arena) : MaxContext (InitCacheProposal.postState arena) := {
  address:=⟨1,0,[]⟩
  located:=by rfl
  allocated:=by change (1:Nat)<14; decide +kernel
  object:={type:="const U",cells:=[some (value maxWord)]}
  heap_entry:=by rfl
  scalar:=by rfl
  contents:=by rfl}

def scaleContext (arena : NatArena.Arena) :
    SynergyC.UnitBody.ScaleContext (InitCacheProposal.postState arena) := {
  address:=⟨0,0,[]⟩
  located:=by rfl
  allocated:=by change (0:Nat)<14; decide +kernel
  object:={type:="const U",cells:=[some (value (2^128))]}
  heap_entry:=by rfl
  scalar:=by rfl
  contents:=by rfl}

theorem constant_read {arena : NatArena.Arena} {i : Nat}
    {a : ScopedNumerical.ProofBox}
    (ha : SynergyAnalytic.HeightPoint.constantValues[i]? = some a) :
    Machine.read SynergyC.Header.layout (InitCacheProposal.postState arena)
      ⟨13,i,[]⟩ = some (SynergyC.SourceIntervalMath.represented a) := by
  unfold Machine.read
  rw [InitCacheModelIdentity.proposed_constant_array]
  simp only [List.getElem?_map,ha,Option.map_some,Bind.bind,Option.bind]
  rfl

theorem actual_constant_read {after : State}
    (actual : after = InitCacheProposal.postState after.nats) {i : Nat}
    {a : ScopedNumerical.ProofBox}
    (ha : SynergyAnalytic.HeightPoint.constantValues[i]? = some a) :
    Machine.read SynergyC.Header.layout after ⟨13,i,[]⟩ =
      some (SynergyC.SourceIntervalMath.represented a) := by
  rw [actual]
  exact constant_read ha

#print axioms maxContext
#print axioms scaleContext
#print axioms constant_read
#print axioms actual_constant_read
end SynergyHeightC.InitCacheReadback
