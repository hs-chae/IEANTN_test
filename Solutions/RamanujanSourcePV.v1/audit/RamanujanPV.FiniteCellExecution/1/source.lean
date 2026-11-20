import RamanujanPV.FiniteCellSource
import RamanujanPV.FiniteLogExecution
import RamanujanPV.FiniteWideExpLinked
import RamanujanPV.WindowCells
namespace RamanujanPV.FiniteCellExecution
open FiniteScalarMachine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

def prototypes : Prototypes := fun name=>
  if name="rpc_e_low" then some ⟨u64,[]⟩
  else if name="rpc_e_high" then some ⟨u64,[]⟩
  else if name="rpc_log_upper" then some ⟨u64,[u64]⟩ else none

/-- Actual source callee execution supplies the logarithm response. The two e
responses are the separately executed complete source functions, not premises. -/
def service : Service := fun name args=>
  if name="rpc_e_low" then match args with
    | []=>some (word64 3133965575612453533)
    | _=>none
  else if name="rpc_e_high" then match args with
    | []=>some (word64 3133965575612453555)
    | _=>none
  else if name="rpc_log_upper" then match args with
    | [n]=>if n.type=u64 then FiniteScalarEval.returnedValue FiniteLogCeil.prototypes
        FiniteLogExecution.service 128 FiniteLogSource.upperFunction.body
        ⟨fun key=>if key="n" then some n else none⟩
      else none
    | _=>none
  else none

def CalleeExecution (name : String) (args : List Value) (answer : Value) : Prop :=
  (name="rpc_e_low" ∧args=[] ∧∃t,
    Run FiniteWideExpExecute.noPrototypes FiniteWideExpExecute.noCalls
      FiniteExpSource.lowFunction.body empty (.returned t answer)) ∨
  (name="rpc_e_high" ∧args=[] ∧∃t,
    FiniteWideExpLinked.LinkedHighRun t answer) ∨
  (name="rpc_log_upper" ∧∃n,args=[n] ∧∃t,
    Run FiniteLogCeil.prototypes FiniteLogExecution.service FiniteLogSource.upperFunction.body
      ⟨fun key=>if key="n" then some n else none⟩ (.returned t answer))

theorem service_closed {name : String} {args : List Value} {answer : Value}
    (response:service name args=some answer) : CalleeExecution name args answer := by
  unfold service at response
  by_cases low:name="rpc_e_low"
  · subst name
    cases args with
    | nil=>
      have equal:word64 3133965575612453533=answer := by simpa only [↓reduceIte,Option.some.injEq] using response
      subst answer
      exact Or.inl ⟨rfl,rfl,FiniteWideExpExecute.low_source_run⟩
    | cons a rest=>simp at response
  · by_cases high:name="rpc_e_high"
    · subst name
      cases args with
      | nil=>
        have equal:word64 3133965575612453555=answer := by simpa only [low,↓reduceIte,Option.some.injEq] using response
        subst answer
        exact Or.inr (Or.inl ⟨rfl,rfl,FiniteWideExpLinked.linked_high_source⟩)
      | cons a rest=>simp [low] at response
    · by_cases logarithm:name="rpc_log_upper"
      · subst name
        simp only [low,high,↓reduceIte] at response
        cases args with
        | nil=>simp at response
        | cons n rest=>
          cases rest with
          | cons a rest=>simp at response
          | nil=>
            simp only at response
            split at response
            next h=>
              refine Or.inr (Or.inr ⟨rfl,n,rfl,?_⟩)
              exact FiniteScalarEval.returned_value_sound
                (p:=FiniteLogCeil.prototypes) (c:=FiniteLogExecution.service) (fuel:=128)
                (body:=FiniteLogSource.upperFunction.body)
                (s:=⟨fun key=>if key="n" then some n else none⟩) response
            next h=>contradiction
      · simp only [low,high,logarithm,↓reduceIte] at response
        contradiction

attribute [irreducible] service

def input (r : RawFactoredCell) : State := ⟨fun name=>
  if name="n" then some (word64 r.n) else
  if name="next" then some (word64 r.next) else
  if name="j" then some (word64 r.j) else
  if name="P" then some (word64 r.P) else
  if name="Q" then some (word64 r.Q) else
  if name="Lu" then some (word64 r.Lu) else
  if name="A" then some (word64 r.A) else none⟩

/-- This object establishes a complete positive execution of the actual source
on the ORIGINAL row. Its numerical/mathematical postcondition is additionally
proved for every selected row by the original row theorem and source e/log
consumers; no all-input positive-output theorem is asserted by this definition. -/
structure SourceExecution (r : RawFactoredCell) : Prop where
  actual : ∃t,Run prototypes service FiniteCellSource.cellFunction.body (input r)
    (.returned t (i32 1))
  source : LCMSourcePV.RestrictedC.SourceCorresponds FiniteCellSource.render
    FiniteCellSource.actualSource ()
  helpers : ∀name args answer,service name args=some answer→CalleeExecution name args answer

def check (r : RawFactoredCell) : Bool :=
  FiniteScalarEval.returnedValue prototypes service 128 FiniteCellSource.cellFunction.body (input r)==some (i32 1)

theorem source_execution_of_checked {r : RawFactoredCell} (checked:check r=true) : SourceExecution r := by
  have accepted : FiniteScalarEval.returnedValue prototypes service 128
      FiniteCellSource.cellFunction.body (input r)=some (i32 1) := beq_iff_eq.mp checked
  exact ⟨FiniteScalarEval.returned_value_sound (p:=prototypes) (c:=service) (fuel:=128)
      (body:=FiniteCellSource.cellFunction.body) (s:=input r) accepted,
    FiniteCellSource.actual_source_checked,fun _ _ _ response=>service_closed response⟩

#print axioms service_closed
#print axioms source_execution_of_checked
end RamanujanPV.FiniteCellExecution
