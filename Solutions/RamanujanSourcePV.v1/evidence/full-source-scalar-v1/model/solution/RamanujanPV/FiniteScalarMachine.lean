/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.WideScalar
import LCMSourcePV.ASTLoops
import LCMSourcePV.ASTDeterminism

/-! Selected scalar C adapter. Integer types, promotions, casts, overflow and
arithmetic are reused from the existing width-generic source-PV Scalar module.
The existing structural ASTLoops supplies all statement/loop rules. There is no
heap, allocator, arbitrary program-result interpretation or logarithm oracle. -/
namespace RamanujanPV.FiniteScalarMachine
open LCMSourcePV.Witness.C
abbrev Value := WideScalar.Value
abbrev CIntType := WideScalar.IntType
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

def u64 : CIntType := ⟨false,64⟩
def u128 : CIntType := ⟨false,128⟩
def word64 (n : Nat) : Value := ⟨u64,n⟩
def word128 (n : Nat) : Value := ⟨u128,n⟩
def i32 (n : Nat) : Value := ⟨⟨true,32⟩,n⟩
def literal (n : Nat) : Option Value :=
  if n<2^31 then some (i32 n)
  else if n<2^63 then some ⟨⟨true,64⟩,n⟩ else none

def namedType (name : String) : Option CIntType :=
  if name="uint64_t" then some u64
  else if name="__uint128_t" then some u128
  else if name="int" then some ⟨true,32⟩ else none

abbrev Env := String → Option Value
structure State where
  env : Env

def bind (env : Env) (name : String) (v : Value) : Env := Function.update env name (some v)
def empty : State := ⟨fun _=>none⟩

structure Prototype where
  result : CIntType
  arguments : List CIntType
abbrev Prototypes := String → Option Prototype
abbrev Service := String → List Value → Option Value

def convertArguments : List CIntType → List Value → Option (List Value)
  | [],[] => some []
  | type::types,value::values => do
      let word ← WideScalar.cast type value
      return word::(←convertArguments types values)
  | _,_ => none

/-- C function prototypes perform the actual argument and return conversions.
The response contract still has to be realized by the corresponding source body. -/
def invoke (prototypes : Prototypes) (service : Service) (name : String)
    (arguments : List Value) : Option Value := do
  let prototype ← prototypes name
  let converted ← convertArguments prototype.arguments arguments
  let result ← service name converted
  WideScalar.cast prototype.result result

def pure (prototypes : Prototypes) (service : Service) (env : Env) : Nat → Expr → Option Value
  | 0,_ => none
  | fuel+1,.nat n => literal n
  | fuel+1,.var name => env name
  | fuel+1,.cast name e => do
      let type ← namedType name
      WideScalar.cast type (←pure prototypes service env fuel e)
  | fuel+1,.binary op a b => do
      WideScalar.binary op (←pure prototypes service env fuel a) (←pure prototypes service env fuel b)
  | fuel+1,.call (.var name) args => do
      invoke prototypes service name (←args.mapM (pure prototypes service env fuel))
  | _,_ => none

def eval (prototypes : Prototypes) (service : Service) (s : State) : Expr → Option (State × Value)
  | .binary "=" (.var name) rhs => do
      let old ← s.env name
      let value ← pure prototypes service s.env 8 rhs
      let converted ← WideScalar.cast old.type value
      return (⟨bind s.env name converted⟩,converted)
  | .unary "++" (.var name) => do
      let old ← s.env name
      let incremented ← WideScalar.binary "+" old (i32 1)
      let converted ← WideScalar.cast old.type incremented
      return (⟨bind s.env name converted⟩,converted)
  | e => do return (s,←pure prototypes service s.env 8 e)

def declare (prototypes : Prototypes) (service : Service) (decls : List Decl) (s : State) : Option State :=
  decls.foldlM (fun t d=>do
    let type ← namedType d.type
    if (t.env d.name).isSome then none else
      let expression ← d.value
      let value ← pure prototypes service t.env 8 expression
      let converted ← WideScalar.cast type value
      return ⟨bind t.env d.name converted⟩) s

def closeScope (before after : State) : State :=
  ⟨fun name=>if (before.env name).isSome then after.env name else none⟩
abbrev Flow := LCMSourcePV.ASTLoops.Flow State Value
def closeFlow (before : State) : Flow → Flow
  | .continuing after => .continuing (closeScope before after)
  | .returned after result => .returned (closeScope before after) result

def Scope (before : State) (inner outer : Flow) : Prop := outer=closeFlow before inner
def Eval (prototypes : Prototypes) (service : Service) (e : Expr) (s t : State) (v : Value) : Prop :=
  eval prototypes service s e=some (t,v)
def Declare (prototypes : Prototypes) (service : Service) (decls : List Decl) (s t : State) : Prop :=
  declare prototypes service decls s=some t
abbrev Run (prototypes : Prototypes) (service : Service) :=
  LCMSourcePV.ASTLoops.StmtRun (Eval prototypes service) (Declare prototypes service) WideScalar.truth Scope
abbrev SeqRun (prototypes : Prototypes) (service : Service) :=
  LCMSourcePV.ASTLoops.SeqRun (Eval prototypes service) (Declare prototypes service) WideScalar.truth Scope
abbrev ForRun (prototypes : Prototypes) (service : Service) :=
  LCMSourcePV.ASTLoops.ForRun (Eval prototypes service) (Declare prototypes service) WideScalar.truth Scope
abbrev WhileRun (prototypes : Prototypes) (service : Service) :=
  LCMSourcePV.ASTLoops.WhileRun (Eval prototypes service) (Declare prototypes service) WideScalar.truth Scope

theorem run_unique {prototypes : Prototypes} {service : Service} {body : Stmt}
    {s : State} {out out' : Flow} (first : Run prototypes service body s out)
    (second : Run prototypes service body s out') : out=out' := by
  apply LCMSourcePV.ASTLoops.stmt_deterministic (Eval:=Eval prototypes service)
    (Declare:=Declare prototypes service) (truth:=WideScalar.truth) (Scope:=Scope) ?_ ?_ ?_ first second
  · intro e s t value t' value' h h'
    exact Prod.mk.inj (Option.some.inj (h.symm.trans h'))
  · intro ds s t t' h h'
    exact Option.some.inj (h.symm.trans h')
  · intro s inner out out' h h'
    exact h.trans h'.symm

/-- Generic one-step rules avoid repeatedly unfolding the complete expression
interpreter while proving actual source compound arithmetic. -/
theorem pure_binary {p : Prototypes} {c : Service} {env : Env} {fuel : Nat}
    {op : String} {a b : Expr} {x y result : Value}
    (left : pure p c env fuel a=some x) (right : pure p c env fuel b=some y)
    (answer : WideScalar.binary op x y=some result) :
    pure p c env (fuel+1) (.binary op a b)=some result := by
  simp only [pure,left,right,Option.bind]
  exact answer

#print axioms run_unique
end RamanujanPV.FiniteScalarMachine
