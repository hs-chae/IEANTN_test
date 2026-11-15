/- One constructive callback dispatcher for the unchanged complete main.
Only proved emitters and the existing generic external runtime/stdio are used. -/
import SynergyHeightC.WorldServiceMap
import SynergyHeightC.EmitIService
namespace SynergyHeightC.MainWorldService
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedIO
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

theorem source_one_more {cfg : Layout} {code : List Function}
    {platform : WorldIO.Platform} {fault : WorldIO.FaultPolicy} {rank : Nat}
    {name : String} {args : List Value} {s t : WorldIO.World} {v : Value}
    (source : WorldSource.SourceCall cfg code platform fault rank name args s v t) :
    WorldSource.SourceCall cfg code platform fault (rank+1) name args s v t := by
  induction rank generalizing name args s v t with
  | zero => exact Or.inl source
  | succ rank ih =>
      rcases source with external | pure | ⟨f,installed,named,pure,pureClosed,service,
        serviceClosed,frame,bound,outcome,body,finish⟩
      · exact Or.inl external
      · exact Or.inr (Or.inl pure)
      · exact Or.inr (Or.inr ⟨f,installed,named,pure,pureClosed,service,
          (fun called actual start value final accepted=>
            ih (serviceClosed called actual start value final accepted)),
          frame,bound,outcome,body,finish⟩)

def call (platform : WorldIO.Platform) (fault : WorldIO.FaultPolicy) : WorldIO.Call :=
  fun name args world=>
    if name="emitU" then EmitUService.call platform fault name args world
    else if name="emitI" then EmitIService.call platform fault name args world
    else WorldIO.external platform fault name args world

theorem emitU_included (platform : WorldIO.Platform) (fault : WorldIO.FaultPolicy) :
    WorldServiceMap.Included (EmitUService.call platform fault) (call platform fault) := by
  intro name args s v t accepted
  by_cases named : name="emitU"
  · subst name
    exact accepted
  · simp [EmitUService.call,named] at accepted

theorem emitI_included (platform : WorldIO.Platform) (fault : WorldIO.FaultPolicy) :
    WorldServiceMap.Included (EmitIService.call platform fault) (call platform fault) := by
  intro name args s v t accepted
  by_cases named : name="emitI"
  · subst name
    exact accepted
  · simp [EmitIService.call,named] at accepted

theorem closed (platform : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    {name : String} {args : List Value} {s t : WorldIO.World} {v : Value}
    (accepted : call platform fault name args s=some (v,t)) :
    WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform fault 2 name args s v t := by
  unfold call at accepted
  split at accepted
  · exact source_one_more (EmitUService.closed platform fault accepted)
  · split at accepted
    · exact EmitIService.closed platform fault accepted
    · exact WorldSource.external_call accepted

#print axioms source_one_more
#print axioms emitU_included
#print axioms emitI_included
#print axioms closed
end SynergyHeightC.MainWorldService
