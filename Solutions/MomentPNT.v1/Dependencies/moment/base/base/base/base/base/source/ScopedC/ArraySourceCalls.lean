/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import ScopedC.ArrayDeclarations
import ScopedC.RuntimeCore

namespace ScopedC.ArraySourceCalls
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0

def Eval (cfg : Layout) (service : Call) (e : Expr)
    (s t : State) (v : Value) : Prop :=
  ∃ fuel, evalExpr cfg service fuel s e = some (v,t)

def Declare (cfg : Layout) (service : Call) (ds : List Decl) (s t : State) : Prop :=
  ArrayDeclarations.declarations cfg service ds s = some t

def Scope (before : State) : Loops.Flow State Value → Loops.Flow State Value → Prop
  | .continuing inner,.continuing outer => outer = popScope before inner
  | .returned inner v,.returned outer w => w = v ∧ outer = popScope before inner
  | _,_ => False

abbrev Run (cfg : Layout) (service : Call) :=
  Loops.StmtRun (Eval cfg service) (Declare cfg service) truth Scope

def Finish (cfg : Layout) (f : Function) (caller : State)
    (inner : Loops.Flow State Value) (v : Value) (after : State) : Prop :=
  match inner with
  | .returned final value =>
    castValue cfg final 100 f.returnType value = some v ∧ after = popScope caller final
  | .continuing final =>
    normalizeType f.returnType = "void" ∧ v = .unit ∧ after = popScope caller final

/-- A finite tree of executions of the *actual installed statement bodies*.
The intermediate expression service is not an oracle: every returned call
must itself have a strictly lower actual execution tree. The only leaves are
the explicitly enumerated pinned generic runtime contracts. No constructor
mentions an expected application output, whole function name, or mathematical
success proposition. Initialized full integer arrays use the fixed ArrayDeclarations rule.
Historical SourceCalls remains unchanged; this is an additive execution model.
-/
def SourceCall (cfg : Layout) (code : List Function) :
    Nat → String → List Value → State → Value → State → Prop
  | 0,name,args,s,v,t => RuntimeCore.call name args s = some (v,t)
  | rank+1,name,args,s,v,t =>
    RuntimeCore.call name args s = some (v,t) ∨
    ∃ f, f ∈ code ∧ f.name = name ∧
      ∃ service : Call,
        (∀ called actual start value final,
          service called actual start = some (value,final) →
          SourceCall cfg code rank called actual start value final) ∧
        ∃ frame, bindArgs cfg f.parameters args s = some frame ∧
          ∃ outcome, Run cfg service f.body frame outcome ∧ Finish cfg f s outcome v t

theorem runtime_leaf {cfg : Layout} {code : List Function} {rank : Nat}
    {name : String} {args : List Value} {s t : State} {v : Value}
    (h : RuntimeCore.call name args s = some (v,t)) :
    SourceCall cfg code rank name args s v t := by
  cases rank with
  | zero => exact h
  | succ rank => exact Or.inl h

theorem installed_body {cfg : Layout} {code : List Function} {rank : Nat}
    {f : Function} {args : List Value} {s frame t : State} {v : Value}
    {service : Call} {outcome : Loops.Flow State Value}
    (installed : f ∈ code)
    (closed : ∀ called actual start value final,
      service called actual start = some (value,final) →
      SourceCall cfg code rank called actual start value final)
    (arguments : bindArgs cfg f.parameters args s = some frame)
    (body : Run cfg service f.body frame outcome)
    (finish : Finish cfg f s outcome v t) :
    SourceCall cfg code (rank+1) f.name args s v t := by
  exact Or.inr ⟨f,installed,rfl,service,closed,frame,arguments,outcome,body,finish⟩

#print axioms installed_body
#print axioms runtime_leaf
end ScopedC.ArraySourceCalls
