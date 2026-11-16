/- Constructive summary of the proved actual emitU source body.
Every successful answer carries a complete actual-source execution proof;
failed/partial I/O returns none. No application output/success oracle is used. -/
import SynergyHeightC.EmitUSource
import ScopedC.StateWordEquality
namespace SynergyHeightC.EmitUService
open ScopedC ScopedC.Machine
open SynergyHeightC.EmitUStorage
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def arguments (platform : ScopedIO.WorldIO.Platform) (caller : State) : List Value :=
  [.pointer (wordsAddress caller) true,.integer ⟨⟨true,32⟩,8⟩,
    .integer ⟨⟨true,32⟩,8⟩,ScopedIO.WorldIO.stdoutValue platform]

def invoke (platform : ScopedIO.WorldIO.Platform) (fault : ScopedIO.WorldIO.FaultPolicy)
    (x : Int) (world : ScopedIO.WorldIO.World) : Option (Value × ScopedIO.WorldIO.World) := do
  if Machine.getVar (frame world.app x 8) "stdout"≠none then none else
  let (ret,after) ← ScopedIO.WorldIO.stdio platform fault "fwrite"
    (arguments platform world.app) ⟨frame world.app x 8,world.stream⟩
  if StateWordEquality.valueEq 2 ret (ScopedIO.WorldIO.unsigned64 8) then
    pure (.unit,⟨world.app,after.stream⟩)
  else none

def call (platform : ScopedIO.WorldIO.Platform) (fault : ScopedIO.WorldIO.FaultPolicy) :
    ScopedIO.WorldIO.Call := fun name args world=>
  if name="emitU" then
    match args with
    | [.integer v] => if v.type=SynergyC.Word512.type ∧ 0≤v.number ∧ v.number<2^512 then
        invoke platform fault v.number world
      else none
    | _ => none
  else none

theorem invoke_closed (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) {x : Int} (hx : SynergyC.Word512.Range x)
    {world after : ScopedIO.WorldIO.World} {v : Value}
    (accepted : invoke platform fault x world=some (v,after)) :
    ScopedIO.WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform fault 1
      "emitU" [SynergyC.Word512.value x] world v after := by
  unfold invoke at accepted
  by_cases shadow : Machine.getVar (frame world.app x 8) "stdout"≠none
  · simp [shadow] at accepted
  · simp only [shadow,↓reduceIte] at accepted
    have unshadowed : Machine.getVar (frame world.app x 8) "stdout"=none := by
      simpa only [ne_eq,not_not] using shadow
    cases io : ScopedIO.WorldIO.stdio platform fault "fwrite"
        (arguments platform world.app) ⟨frame world.app x 8,world.stream⟩ with
    | none => simp [io] at accepted
    | some result =>
        rcases result with ⟨ret,output⟩
        simp only [io,Bind.bind,Option.bind] at accepted
        by_cases check : StateWordEquality.valueEq 2 ret (ScopedIO.WorldIO.unsigned64 8)=true
        · simp only [check,↓reduceIte] at accepted
          have equal := StateWordEquality.valueEq_sound 2 check
          rw [equal] at io
          have pair := Option.some.inj accepted
          have first : Value.unit=v := congrArg Prod.fst pair
          have second : (⟨world.app,output.stream⟩ : ScopedIO.WorldIO.World)=after :=
            congrArg Prod.snd pair
          subst v
          subst after
          exact (EmitUSource.source_of_checked_return platform fault world.app x hx
            world.stream output unshadowed io).1
        · simp [check] at accepted

theorem closed (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) {name : String} {args : List Value}
    {world after : ScopedIO.WorldIO.World} {v : Value}
    (accepted : call platform fault name args world=some (v,after)) :
    ScopedIO.WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform fault 1
      name args world v after := by
  unfold call at accepted
  by_cases named : name="emitU"
  · subst name
    simp only [↓reduceIte] at accepted
    split at accepted
    · rename_i value
      by_cases valid : value.type=SynergyC.Word512.type ∧
          0≤value.number ∧ value.number<2^512
      · simp only [valid,↓reduceIte] at accepted
        have source := invoke_closed platform fault valid.2 accepted
        have same : .integer value=SynergyC.Word512.value value.number := by
          cases value
          simp only [SynergyC.Word512.value,SynergyC.Word512.word]
          cases valid.1
          rfl
        rw [same]
        exact source
      · simp [valid] at accepted
    · contradiction
  · simp [named] at accepted

theorem output_correct (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) {x : Int}
    {world after : ScopedIO.WorldIO.World} {v : Value}
    (accepted : invoke platform fault x world=some (v,after)) :
    after.app=world.app ∧ after.stream.accepted=world.stream.accepted++EmitUBuffer.bytes x := by
  unfold invoke at accepted
  by_cases shadow : Machine.getVar (frame world.app x 8) "stdout"≠none
  · simp [shadow] at accepted
  · simp only [shadow,↓reduceIte] at accepted
    have unshadowed : Machine.getVar (frame world.app x 8) "stdout"=none := by
      simpa only [ne_eq,not_not] using shadow
    cases io : ScopedIO.WorldIO.stdio platform fault "fwrite"
        (arguments platform world.app) ⟨frame world.app x 8,world.stream⟩ with
    | none => simp [io] at accepted
    | some result =>
        rcases result with ⟨ret,output⟩
        simp only [io,Bind.bind,Option.bind] at accepted
        by_cases check : StateWordEquality.valueEq 2 ret (ScopedIO.WorldIO.unsigned64 8)=true
        · simp only [check,↓reduceIte] at accepted
          have equal := StateWordEquality.valueEq_sound 2 check
          rw [equal] at io
          have pair := Option.some.inj accepted
          have second : (⟨world.app,output.stream⟩ : ScopedIO.WorldIO.World)=after :=
            congrArg Prod.snd pair
          subst after
          exact ⟨rfl,(EmitUBuffer.accepted_output_of_full_return
            platform fault world.stream world.app x output io).2⟩
        · simp [check] at accepted

#print axioms invoke_closed
#print axioms closed
#print axioms output_correct
end SynergyHeightC.EmitUService
