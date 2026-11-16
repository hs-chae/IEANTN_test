/- Constructive source-verified emitI summary, composed from two actual emitU calls. -/
import SynergyHeightC.EmitISource
import SynergyC.ComputableIntervalInput
namespace SynergyHeightC.EmitIService
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

def unitResult : Option (Value × ScopedIO.WorldIO.World) → Option ScopedIO.WorldIO.World
  | none => none
  | some (v,after) => if StateWordEquality.valueEq 2 v .unit then some after else none

theorem unitResult_sound {result : Option (Value × ScopedIO.WorldIO.World)}
    {after : ScopedIO.WorldIO.World} (accepted : unitResult result=some after) :
    result=some (.unit,after) := by
  cases result with
  | none => contradiction
  | some answer =>
      rcases answer with ⟨v,final⟩
      simp only [unitResult] at accepted
      split at accepted
      · rename_i check
        have same := StateWordEquality.valueEq_sound 2 check
        have state := Option.some.inj accepted
        cases same
        cases state
        rfl
      · contradiction

def invoke (platform : ScopedIO.WorldIO.Platform) (fault : ScopedIO.WorldIO.FaultPolicy)
    (box : ProofBox) (world : ScopedIO.WorldIO.World) : Option (Value × ScopedIO.WorldIO.World) := do
  let middle ← unitResult (EmitUService.call platform fault "emitU" [SynergyC.Word512.value box.lo]
    ⟨EmitISource.frame world.app box,world.stream⟩)
  let after ← unitResult (EmitUService.call platform fault "emitU" [SynergyC.Word512.value box.hi] middle)
  pure (.unit,⟨world.app,after.stream⟩)

def call (platform : ScopedIO.WorldIO.Platform) (fault : ScopedIO.WorldIO.FaultPolicy) :
    ScopedIO.WorldIO.Call := fun name args world=>
  if name="emitI" then
    match args with
    | [input] => do
        let decoded ← SynergyC.ComputableIntervalInput.interval? input
        let box : ProofBox := ⟨decoded.val.lo,decoded.val.hi⟩
        if 0≤box.lo ∧ box.lo<2^512 ∧ 0≤box.hi ∧ box.hi<2^512 then
          invoke platform fault box world
        else none
    | _ => none
  else none

theorem invoke_closed (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) {box : ProofBox}
    (lo : SynergyC.Word512.Range box.lo) (hi : SynergyC.Word512.Range box.hi)
    {world after : ScopedIO.WorldIO.World} {v : Value}
    (accepted : invoke platform fault box world=some (v,after)) :
    ScopedIO.WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform fault 2
      "emitI" [SynergyC.SourceIntervalMath.represented box] world v after := by
  unfold invoke at accepted
  cases first : unitResult (EmitUService.call platform fault "emitU" [SynergyC.Word512.value box.lo]
      ⟨EmitISource.frame world.app box,world.stream⟩) with
  | none => simp [first] at accepted
  | some middle =>
      simp only [first,Bind.bind,Option.bind] at accepted
      cases second : unitResult (EmitUService.call platform fault "emitU"
          [SynergyC.Word512.value box.hi] middle) with
      | none => simp [second] at accepted
      | some final =>
          simp only [second,Bind.bind,Option.bind,Pure.pure] at accepted
          have pair := Option.some.inj accepted
          have value : Value.unit=v := congrArg Prod.fst pair
          have state : (⟨world.app,final.stream⟩ : ScopedIO.WorldIO.World)=after :=
            congrArg Prod.snd pair
          subst v
          subst after
          exact (EmitISource.source_of_calls platform fault world.app box lo hi
            world.stream middle final (unitResult_sound first) (unitResult_sound second)).1

theorem invoke_output (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) {box : ProofBox}
    (lo : SynergyC.Word512.Range box.lo) (hi : SynergyC.Word512.Range box.hi)
    {world after : ScopedIO.WorldIO.World} {v : Value}
    (accepted : invoke platform fault box world=some (v,after)) :
    after.app=world.app ∧ after.stream.accepted=
      world.stream.accepted++EmitUBuffer.bytes box.lo++EmitUBuffer.bytes box.hi := by
  unfold invoke at accepted
  cases first : unitResult (EmitUService.call platform fault "emitU" [SynergyC.Word512.value box.lo]
      ⟨EmitISource.frame world.app box,world.stream⟩) with
  | none => simp [first] at accepted
  | some middle =>
      simp only [first,Bind.bind,Option.bind] at accepted
      cases second : unitResult (EmitUService.call platform fault "emitU"
          [SynergyC.Word512.value box.hi] middle) with
      | none => simp [second] at accepted
      | some final =>
          simp only [second,Bind.bind,Option.bind,Pure.pure] at accepted
          have pair := Option.some.inj accepted
          have state : (⟨world.app,final.stream⟩ : ScopedIO.WorldIO.World)=after :=
            congrArg Prod.snd pair
          subst after
          exact ⟨rfl,(EmitISource.source_of_calls platform fault world.app box lo hi
            world.stream middle final (unitResult_sound first) (unitResult_sound second)).2⟩

theorem closed (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) {name : String} {args : List Value}
    {world after : ScopedIO.WorldIO.World} {v : Value}
    (accepted : call platform fault name args world=some (v,after)) :
    ScopedIO.WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform fault 2
      name args world v after := by
  unfold call at accepted
  by_cases named : name="emitI"
  · subst name
    simp only [↓reduceIte] at accepted
    split at accepted
    · rename_i input
      cases decoded : SynergyC.ComputableIntervalInput.interval? input with
      | none => simp [decoded] at accepted
      | some bounds =>
          simp only [decoded,Bind.bind,Option.bind] at accepted
          split at accepted
          · rename_i valid
            have lo : SynergyC.Word512.Range bounds.val.lo := ⟨valid.1,valid.2.1⟩
            have hi : SynergyC.Word512.Range bounds.val.hi := valid.2.2
            have source := invoke_closed platform fault lo hi accepted
            rw [bounds.property]
            exact source
          · contradiction
    · contradiction
  · simp [named] at accepted

#print axioms unitResult_sound
#print axioms invoke_closed
#print axioms invoke_output
#print axioms closed
end SynergyHeightC.EmitIService
