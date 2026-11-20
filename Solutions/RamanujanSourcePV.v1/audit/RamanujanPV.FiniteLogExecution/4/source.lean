import RamanujanPV.FiniteScalarEval
import RamanujanPV.FiniteLogServices
namespace RamanujanPV.FiniteLogExecution
open FiniteScalarMachine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

/-- The20-term callee's actual converted parameter environment. -/
def seriesInput (args : List Value) : State := match args with
  | [a,b]=>⟨fun name=>if name="num" then some a else if name="den" then some b else none⟩
  | _=>empty

/-- No series output oracle: this response is computed by executing the
complete source-bound20-term AST with the source-proved ceil helper. -/
def service : Service := fun name args=>
  if name="rpc_log_series_upper" then match args with
    | [a,b]=>if a.type=u64 ∧b.type=u64 then
        FiniteScalarEval.returnedValue FiniteLogCeil.prototypes FiniteLogServices.ceilService 128
          FiniteLogSource.seriesFunction.body (seriesInput args)
      else none
    | _=>none
  else FiniteLogServices.ceilService name args

attribute [irreducible] service

def CalleeExecution (name : String) (args : List Value) (answer : Value) : Prop :=
  (name="rpc_log_ceildiv" ∧∃t,Run FiniteLogCeil.prototypes FiniteLogCeil.noCalls
    FiniteLogSource.ceilFunction.body (FiniteLogServices.sourceInput args) (.returned t answer)) ∨
  (name="rpc_log_series_upper" ∧∃t,Run FiniteLogCeil.prototypes FiniteLogServices.ceilService
    FiniteLogSource.seriesFunction.body (seriesInput args) (.returned t answer))

theorem service_closed {name : String} {args : List Value} {answer : Value}
    (response:service name args=some answer) : CalleeExecution name args answer := by
  unfold service at response
  by_cases nameIsSeries:name="rpc_log_series_upper"
  · subst name
    right
    refine ⟨rfl,?_⟩
    cases args with
    | nil=>simp [service] at response
    | cons a rest=>
      cases rest with
      | nil=>simp [service] at response
      | cons b tail=>
        cases tail with
        | cons c tail=>simp [service] at response
        | nil=>
          simp only [↓reduceIte] at response
          split at response
          next h=>
            exact FiniteScalarEval.returned_value_sound
              (p:=FiniteLogCeil.prototypes) (c:=FiniteLogServices.ceilService) (fuel:=128)
              (body:=FiniteLogSource.seriesFunction.body) (s:=seriesInput [a,b]) response
          next h=>contradiction
  · left
    exact FiniteLogServices.ceil_service_closed (by simpa only [nameIsSeries,↓reduceIte] using response)

def input (n : Nat) : State :=⟨fun name=>if name="n" then some (word64 n) else none⟩

/-- A verified instance is a complete source reference execution on an input,
with the original normalized mathematical value as its returned word. This
object must be constructed by kernel execution, never assumed from native C. -/
def VerifiedInput (n : Nat) : Prop := ∃two k : Nat,
  2≤n ∧n≤2000000000000 ∧two=2^k ∧two≤n ∧n<2*two ∧
  ∃t,Run FiniteLogCeil.prototypes service FiniteLogSource.upperFunction.body
    (input n) (.returned t (word64 (AnalyticTransition.binaryLogUpper n two k)))

/-- Both the actual source run and the independently kernel-verified reference
are retained. Correctness below compares arbitrary completed source outputs. -/
structure SourceExecution (n output : Nat) : Prop where
  verified : VerifiedInput n
  actual : ∃t,Run FiniteLogCeil.prototypes service FiniteLogSource.upperFunction.body
    (input n) (.returned t (word64 output))
  source : LCMSourcePV.RestrictedC.SourceCorresponds FiniteLogSource.render
    FiniteLogSource.actualSource ()
  helpers : ∀name args answer,service name args=some answer → CalleeExecution name args answer
  leafHelpers : ∀name args answer,FiniteLogServices.ceilService name args=some answer →
    name="rpc_log_ceildiv" ∧∃t,Run FiniteLogCeil.prototypes FiniteLogCeil.noCalls
      FiniteLogSource.ceilFunction.body (FiniteLogServices.sourceInput args) (.returned t answer)

/-- Full selected-input program correctness: actual returned words, rather
than an expected-output premise, are transported to the mathematical bound. -/
theorem source_log_upper_sound {n output : Nat} (run:SourceExecution n output) :
    Real.log (n:ℝ)≤(output:ℝ)/(2:ℝ)^40 := by
  rcases run.actual with ⟨actualState,actualRun⟩
  rcases run.verified with ⟨two,k,lower,upper,power,floor,ceiling,referenceState,referenceRun⟩
  have flows:=run_unique (prototypes:=FiniteLogCeil.prototypes) (service:=service)
    (body:=FiniteLogSource.upperFunction.body) (s:=input n) actualRun referenceRun
  have values : word64 output=word64 (AnalyticTransition.binaryLogUpper n two k) := by
    have extracted:=congrArg (fun f : Flow=>match f with
      | .returned _ value=>some value
      | .continuing _=>none) flows
    exact Option.some.inj extracted
  have equal : output=AnalyticTransition.binaryLogUpper n two k := by
    have numbers:=congrArg WideScalar.Value.number values
    exact_mod_cast numbers
  rw [equal]
  exact AnalyticTransition.binaryLogUpper_sound power floor ceiling

def check (n two k output : Nat) : Bool :=
  decide (2≤n ∧n≤2000000000000 ∧two=2^k ∧two≤n ∧n<2*two ∧
    output=AnalyticTransition.binaryLogUpper n two k) &&
  (FiniteScalarEval.returnedValue FiniteLogCeil.prototypes service 128
    FiniteLogSource.upperFunction.body (input n)==some (word64 output))

theorem source_execution_of_checked {n two k output : Nat} (checked:check n two k output=true) :
    SourceExecution n output := by
  have clauses : decide (2≤n ∧n≤2000000000000 ∧two=2^k ∧two≤n ∧n<2*two ∧
      output=AnalyticTransition.binaryLogUpper n two k)=true ∧
    (FiniteScalarEval.returnedValue FiniteLogCeil.prototypes service 128
      FiniteLogSource.upperFunction.body (input n)==some (word64 output))=true :=
    by simpa only [check,Bool.and_eq_true] using checked
  rcases of_decide_eq_true clauses.1 with ⟨lower,upper,power,floor,ceiling,value⟩
  have acceptedEquality : FiniteScalarEval.returnedValue FiniteLogCeil.prototypes service 128
      FiniteLogSource.upperFunction.body (input n)=some (word64 output) := beq_iff_eq.mp clauses.2
  have accepted : ∃t,Run FiniteLogCeil.prototypes service FiniteLogSource.upperFunction.body
      (input n) (.returned t (word64 output)) :=
    FiniteScalarEval.returned_value_sound (p:=FiniteLogCeil.prototypes) (c:=service) (fuel:=128)
      (body:=FiniteLogSource.upperFunction.body) (s:=input n) acceptedEquality
  refine ⟨⟨two,k,lower,upper,power,floor,ceiling,?_⟩,accepted,
    FiniteLogSource.actual_source_checked,fun _ _ _ response=>service_closed response,
    fun _ _ _ response=>FiniteLogServices.ceil_service_closed response⟩
  simpa only [←value] using accepted

#print axioms service_closed
#print axioms source_log_upper_sound
#print axioms source_execution_of_checked
end RamanujanPV.FiniteLogExecution
