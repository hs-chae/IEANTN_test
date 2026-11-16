/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.SourceIntervalMath

namespace SynergyC.ArithmeticService
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

inductive Operation where | add | mul | ceil
  deriving DecidableEq

def operation : String → Option Operation
  | "addU" => some .add
  | "mulU" => some .mul
  | "ceilDiv" => some .ceil
  | _ => none
def name : Operation → String | .add => "addU" | .mul => "mulU" | .ceil => "ceilDiv"
theorem operation_name {called : String} {op : Operation} (h : operation called = some op) :
    called = name op := by
  cases op <;> unfold operation at h <;> split at h <;> simp_all [name]

def result : Operation → Int → Int → Int
  | .add,a,b => a+b
  | .mul,a,b => a*b
  | .ceil,a,b => CeilDivBody.result a b
def permitted (op : Operation) (s : State) (a b : Int) : Prop :=
  Range a ∧ Range b ∧ Nonempty (MaxContext s) ∧
    match op with
    | .add | .mul => Range (result op a b)
    | .ceil => 0 < b

def parameters (code : List Function) : Bool := code.all fun f =>
  (f.name != "addU" && f.name != "mulU" && f.name != "ceilDiv") ||
    decide (f.parameters = [("U","a"),("U","b")])

theorem generated_parameters : parameters Generated.functions = true := by decide +kernel

theorem parameter_of_check (code : List Function) (checked : parameters code = true)
    (f : Function) (mem : f ∈ code) (op : Operation) (named : f.name = name op) :
    f.parameters = [("U","a"),("U","b")] := by
  have h := (List.all_eq_true.mp checked) f mem
  cases op <;> simpa [named,name] using h

theorem add_parameter_check (code : List Function) (checked : parameters code = true) :
    CeilDivBody.addParameters code = true := by
  apply List.all_eq_true.mpr
  intro f mem
  by_cases h : f.name = "addU"
  · simp [h,parameter_of_check code checked f mem .add h]
  · simp [h]

theorem cast_integer (s : State) (a : Scalar.Value) (ha : Range a.number) :
    castValue Header.layout s 100 "U" (.integer a) = some (value a.number) := by
  change (do let x ← Scalar.make type a.number; pure (Value.integer x)) = _
  rw [Scalar.make_exact (range_scalar ha)]
  rfl

noncomputable section

/-- A proof-only arithmetic service. All admitted results are consequences
of actual installed C bodies (theorem closed below), never trusted program
answers. Raw scalar arguments receive the actual U parameter conversion. -/
def call : Call := fun called args s => by
  classical
  exact do
    let op ← operation called
    let [.integer a,.integer b] := args | none
    if permitted op s a.number b.number then some (value (result op a.number b.number),s) else none

theorem complete {op : Operation} {s : State} (a b : Scalar.Value)
    (good : permitted op s a.number b.number) :
    call (name op) [.integer a,.integer b] s = some (value (result op a.number b.number),s) := by
  classical
  cases op <;> simp [call,name,operation,good]

theorem closed (code : List Function)
    (addInstalled : Generated.f_addU ∈ code) (mulInstalled : Generated.f_mulU ∈ code)
    (ceilInstalled : Generated.f_ceilDiv ∈ code) (checked : parameters code = true)
    {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s = some (v,t)) :
    SourceCall Header.layout code 2 called args s v t := by
  classical
  unfold call at h
  cases ho : operation called with
  | none => simp [ho] at h
  | some op =>
    simp only [ho,Bind.bind,Option.bind] at h
    split at h
    · rename_i a b
      split_ifs at h with good
      · rcases good with ⟨ha,hb,⟨ctx⟩,domain⟩
        have hn : called = name op := operation_name ho
        subst called
        simp only [Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        have canonical : SourceCall Header.layout code 2 (name op)
            [value a.number,value b.number] s (value (result op a.number b.number)) s := by
          cases op with
          | add => exact raise_once (AddBody.source_addU code addInstalled ctx ha hb domain)
          | mul => exact raise_once (MulBody.source_mulU code mulInstalled ctx ha hb domain)
          | ceil =>
            exact CeilDivBody.source_ceilDiv_total code ceilInstalled addInstalled
              (add_parameter_check code checked) ctx ha hb domain
        apply ArgumentConversion.replace_arguments canonical
        · cases op <;> rfl
        · intro f mem named
          rw [parameter_of_check code checked f mem op named]
          have raw := TypedFrames.bind_two Header.layout s "U" "a" "U" "b"
            (.integer a) (.integer b) (value a.number) (value b.number)
            (cast_integer _ a ha) (cast_integer _ b hb)
          rw [raw,WordFrames.bind s ha hb]
          rfl
    · contradiction

end
end SynergyC.ArithmeticService
