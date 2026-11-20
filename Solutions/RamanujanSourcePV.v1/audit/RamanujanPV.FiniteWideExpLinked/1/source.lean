/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteWideExpExecute

/-! Source-closed e helper calls in the same width-generic machine as the log
and row checker. A selected function name cannot supply an unproved output:
every accepted low-helper response is justified by its actual20-step source. -/
namespace RamanujanPV.FiniteWideExpLinked
open FiniteScalarMachine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def prototypes : Prototypes := fun name=>
  if name="rpc_e_low" then some ⟨u64,[]⟩ else none

def service : Service := fun name arguments=>
  if name="rpc_e_low" then match arguments with
    | [] => some (word64 3133965575612453533)
    | _ => none
  else none

theorem low_evaluated (p : Prototypes) (c : Service) :
    FiniteScalarEval.returnedValue p c 200 FiniteExpSource.lowFunction.body empty=
      some (word64 3133965575612453533) := by
  decide +kernel

theorem low_source_run (p : Prototypes) (c : Service) :
    ∃t,Run p c FiniteExpSource.lowFunction.body empty
      (.returned t (word64 3133965575612453533)) :=
  FiniteScalarEval.returned_value_sound (low_evaluated p c)

theorem service_closed {name : String} {arguments : List Value} {result : Value}
    (response : service name arguments=some result) :
    name="rpc_e_low" ∧ arguments=[] ∧
      ∃t,Run FiniteWideExpExecute.noPrototypes FiniteWideExpExecute.noCalls
        FiniteExpSource.lowFunction.body empty (.returned t result) := by
  by_cases selected : name="rpc_e_low"
  · subst name
    cases arguments with
    | nil =>
        have equal : word64 3133965575612453533=result := by simpa [service] using response
        subst result
        exact ⟨rfl,rfl,FiniteWideExpExecute.low_source_run⟩
    | cons a rest => simp [service] at response
  · simp [service,selected] at response

theorem high_evaluated : FiniteScalarEval.returnedValue prototypes service 20
    FiniteExpSource.highFunction.body empty=some (word64 3133965575612453555) := by
  decide +kernel

theorem high_source_run : ∃t,Run prototypes service FiniteExpSource.highFunction.body empty
    (.returned t (word64 3133965575612453555)) :=
  FiniteScalarEval.returned_value_sound high_evaluated

def LinkedHighRun (t : State) (result : Value) : Prop :=
  Run prototypes service FiniteExpSource.highFunction.body empty (.returned t result) ∧
  (∀name arguments value,service name arguments=some value→
    name="rpc_e_low" ∧ arguments=[] ∧
      ∃s,Run FiniteWideExpExecute.noPrototypes FiniteWideExpExecute.noCalls
        FiniteExpSource.lowFunction.body empty (.returned s value))

theorem linked_high_source : ∃t,LinkedHighRun t (word64 3133965575612453555) := by
  obtain ⟨t,run⟩ := high_source_run
  exact ⟨t,run,fun _ _ _ response=>service_closed response⟩

theorem low_completed_correct {p : Prototypes} {c : Service} {t : State} {result : Value}
    (run : Run p c FiniteExpSource.lowFunction.body empty (.returned t result)) :
    result=word64 3133965575612453533 := by
  obtain ⟨expected,reference⟩ := low_source_run p c
  exact (LCMSourcePV.ASTLoops.Flow.returned.inj (run_unique run reference)).2

theorem high_completed_correct {t : State} {result : Value} (run : LinkedHighRun t result) :
    result=word64 3133965575612453555 := by
  obtain ⟨expected,reference⟩ := high_source_run
  exact (LCMSourcePV.ASTLoops.Flow.returned.inj (run_unique run.1 reference)).2

#print axioms low_evaluated
#print axioms service_closed
#print axioms high_evaluated
#print axioms linked_high_source
#print axioms low_completed_correct
#print axioms high_completed_correct
end RamanujanPV.FiniteWideExpLinked
