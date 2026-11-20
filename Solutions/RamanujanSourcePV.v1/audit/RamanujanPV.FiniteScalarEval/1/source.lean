/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteScalarMachine

/-! Bounded execution of the ACTUAL scalar source AST. All four control routes
share one structurally decreasing fuel argument. Exhaustion or an invalid typed
operation returns none. Accepted values yield the existing ASTLoops Run; helper
prototypes and responses are supplied unchanged, never approximated here. Each
application must separately close those responses by its actual callee source.
This interpreter does not accept a separate numerical certificate. -/
namespace RamanujanPV.FiniteScalarEval
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops FiniteScalarMachine
set_option autoImplicit false
set_option maxHeartbeats 2000000

inductive Control where
  | statement (body : Stmt)
  | sequence (body : List Stmt)
  | forLoop (condition : Option Expr) (step : Expr) (body : Stmt)
  | whileLoop (condition : Expr) (body : Stmt)

def guard (p : Prototypes) (c : Service) (condition : Option Expr) (s : State) :
    Option (State × Bool) := match condition with
  | none => some (s,true)
  | some expression => do
      let (t,value) ← eval p c s expression
      return (t,WideScalar.truth value)

def execute (p : Prototypes) (c : Service) : Nat → Control → State → Option Flow
  | 0,_,_ => none
  | fuel+1,.statement .skip,s => some (.continuing s)
  | fuel+1,.statement (.eval expression),s => do
      let (t,_) ← eval p c s expression
      return .continuing t
  | fuel+1,.statement (.declare declarations),s => do
      return .continuing (←declare p c declarations s)
  | fuel+1,.statement (.returnStmt expression),s => do
      let (t,value) ← eval p c s expression
      return .returned t value
  | fuel+1,.statement (.branch expression yes no),s => do
      let (t,value) ← eval p c s expression
      execute p c fuel (.statement (if WideScalar.truth value then yes else no)) t
  | fuel+1,.statement (.sequence body),s => do
      return closeFlow s (←execute p c fuel (.sequence body) s)
  | fuel+1,.statement (.forLoop initial condition step body),s => do
      let first ← execute p c fuel (.statement initial) s
      match first with
      | .returned t value => return closeFlow s (.returned t value)
      | .continuing t =>
          return closeFlow s (←execute p c fuel (.forLoop condition step body) t)
  | fuel+1,.statement (.whileLoop condition body),s =>
      execute p c fuel (.whileLoop condition body) s
  | fuel+1,.sequence [],s => some (.continuing s)
  | fuel+1,.sequence (head::tail),s => do
      let first ← execute p c fuel (.statement head) s
      match first with
      | .returned t value => return .returned t value
      | .continuing t => execute p c fuel (.sequence tail) t
  | fuel+1,.forLoop condition step body,s => do
      let (t,keepGoing) ← guard p c condition s
      if keepGoing then
        let result ← execute p c fuel (.statement body) t
        match result with
        | .returned b value => return .returned b value
        | .continuing b =>
            let (next,_) ← eval p c b step
            execute p c fuel (.forLoop condition step body) next
      else return .continuing t
  | fuel+1,.whileLoop condition body,s => do
      let (t,value) ← eval p c s condition
      if WideScalar.truth value then
        let result ← execute p c fuel (.statement body) t
        match result with
        | .returned b value => return .returned b value
        | .continuing b => execute p c fuel (.whileLoop condition body) b
      else return .continuing t

def Judgment (p : Prototypes) (c : Service) : Control → State → Flow → Prop
  | .statement body => Run p c body
  | .sequence body => SeqRun p c body
  | .forLoop condition step body => ForRun p c condition step body
  | .whileLoop condition body => WhileRun p c condition body

theorem guard_sound {p : Prototypes} {c : Service} {condition : Option Expr}
    {s t : State} {keep : Bool} (accepted : guard p c condition s=some (t,keep)) :
    GuardRun (Eval p c) WideScalar.truth condition s t keep := by
  cases condition with
  | none => simp only [guard,Option.some.injEq,Prod.mk.injEq] at accepted
            obtain ⟨rfl,rfl⟩ := accepted
            exact GuardRun.omitted s
  | some expression =>
      cases evaluated : eval p c s expression with
      | none => simp [guard,evaluated] at accepted
      | some pair =>
          rcases pair with ⟨next,value⟩
          simp only [guard,evaluated,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at accepted
          obtain ⟨rfl,rfl⟩ := accepted
          exact GuardRun.present evaluated

/-- Sound for every source tree and supplied call registry, including all
early-return and block/for-scope cases. There is no function-name result rule. -/
theorem sound {p : Prototypes} {c : Service} (fuel : Nat) :
    ∀control s result,execute p c fuel control s=some result→Judgment p c control s result := by
  induction fuel with
  | zero => intro control s result accepted; simp [execute] at accepted
  | succ fuel ih =>
    intro control s result accepted
    cases control with
    | statement body =>
      cases body with
      | skip =>
          simp only [execute,Option.some.injEq] at accepted
          subst result
          exact StmtRun.skip s
      | eval expression =>
          cases evaluated : eval p c s expression with
          | none => simp [execute,evaluated] at accepted
          | some pair =>
              rcases pair with ⟨t,value⟩
              simp only [execute,evaluated,Option.bind_some,Option.some.injEq] at accepted
              subst result
              exact StmtRun.evaluate evaluated
      | declare declarations =>
          cases declared : declare p c declarations s with
          | none => simp [execute,declared] at accepted
          | some t =>
              simp only [execute,declared,Option.bind_some,Option.some.injEq] at accepted
              subst result
              exact StmtRun.declare declared
      | returnStmt expression =>
          cases evaluated : eval p c s expression with
          | none => simp [execute,evaluated] at accepted
          | some pair =>
              rcases pair with ⟨t,value⟩
              simp only [execute,evaluated,Option.bind_some,Option.some.injEq] at accepted
              subst result
              exact StmtRun.returnValue evaluated
      | branch expression yes no =>
          cases evaluated : eval p c s expression with
          | none => simp [execute,evaluated] at accepted
          | some pair =>
              rcases pair with ⟨t,value⟩
              simp only [execute,evaluated,Option.bind_some] at accepted
              exact StmtRun.branch evaluated (ih _ _ _ accepted)
      | sequence body =>
          cases inner : execute p c fuel (.sequence body) s with
          | none => simp [execute,inner] at accepted
          | some out =>
              simp only [execute,inner,Option.bind_some,Option.some.injEq] at accepted
              subst result
              exact StmtRun.sequence (ih _ _ _ inner) rfl
      | forLoop initial condition step body =>
          cases first : execute p c fuel (.statement initial) s with
          | none => simp [execute,first] at accepted
          | some out =>
            cases out with
            | returned t value =>
                simp only [execute,first,Option.bind_some,Option.some.injEq] at accepted
                subst result
                exact StmtRun.forInitialReturn (ih _ _ _ first) rfl
            | continuing t =>
                cases loop : execute p c fuel (.forLoop condition step body) t with
                | none => simp [execute,first,loop] at accepted
                | some out =>
                    simp only [execute,first,loop,Option.bind_some,Option.some.injEq] at accepted
                    subst result
                    exact StmtRun.forLoop (ih _ _ _ first) (ih _ _ _ loop) rfl
      | whileLoop condition body =>
          exact StmtRun.whileLoop (ih _ _ _ accepted)
    | sequence body =>
      cases body with
      | nil =>
          simp only [execute,Option.some.injEq] at accepted
          subst result
          exact SeqRun.nil s
      | cons head tail =>
          cases first : execute p c fuel (.statement head) s with
          | none => simp [execute,first] at accepted
          | some out =>
            cases out with
            | returned t value =>
                simp only [execute,first,Option.bind_some,Option.some.injEq] at accepted
                subst result
                exact SeqRun.returned (ih _ _ _ first)
            | continuing t =>
                simp only [execute,first,Option.bind_some] at accepted
                exact SeqRun.next (ih _ _ _ first) (ih _ _ _ accepted)
    | forLoop condition step body =>
        cases tested : guard p c condition s with
        | none => simp [execute,tested] at accepted
        | some pair =>
          rcases pair with ⟨t,keep⟩
          cases keep with
          | false =>
              simp only [execute,tested,Option.bind_some,Bool.false_eq_true,ite_false,Option.some.injEq] at accepted
              subst result
              exact ForRun.done (guard_sound tested)
          | true =>
              cases iteration : execute p c fuel (.statement body) t with
              | none => simp [execute,tested,iteration] at accepted
              | some out =>
                cases out with
                | returned b value =>
                    simp only [execute,tested,iteration,Option.bind_some,ite_true,Option.some.injEq] at accepted
                    subst result
                    exact ForRun.returned (guard_sound tested) (ih _ _ _ iteration)
                | continuing b =>
                    cases increment : eval p c b step with
                    | none => simp [execute,tested,iteration,increment] at accepted
                    | some pair =>
                        rcases pair with ⟨next,value⟩
                        simp only [execute,tested,iteration,increment,Option.bind_some,ite_true] at accepted
                        exact ForRun.next (guard_sound tested) (ih _ _ _ iteration) increment (ih _ _ _ accepted)
    | whileLoop condition body =>
        cases tested : eval p c s condition with
        | none => simp [execute,tested] at accepted
        | some pair =>
          rcases pair with ⟨t,value⟩
          cases keep : WideScalar.truth value with
          | false =>
              simp only [execute,tested,keep,Option.bind_some,Bool.false_eq_true,ite_false,Option.some.injEq] at accepted
              subst result
              exact WhileRun.done tested keep
          | true =>
              cases iteration : execute p c fuel (.statement body) t with
              | none => simp [execute,tested,keep,iteration] at accepted
              | some out =>
                cases out with
                | returned b answer =>
                    simp only [execute,tested,keep,iteration,Option.bind_some,ite_true,Option.some.injEq] at accepted
                    subst result
                    exact WhileRun.returned tested keep (ih _ _ _ iteration)
                | continuing b =>
                    simp only [execute,tested,keep,iteration,Option.bind_some,ite_true] at accepted
                    exact WhileRun.next tested keep (ih _ _ _ iteration) (ih _ _ _ accepted)

def statement (p : Prototypes) (c : Service) (fuel : Nat) (body : Stmt) (s : State) : Option Flow :=
  execute p c fuel (.statement body) s

theorem statement_sound {p : Prototypes} {c : Service} {fuel : Nat} {body : Stmt}
    {s : State} {out : Flow} (accepted : statement p c fuel body s=some out) : Run p c body s out :=
  sound fuel _ _ _ accepted

/-- Only the returned scalar value is compared during kernel execution, avoiding
undecidable extensional equality of the environment function in a final state. -/
def returnedValue (p : Prototypes) (c : Service) (fuel : Nat) (body : Stmt) (s : State) : Option Value := do
  match ←statement p c fuel body s with
  | .returned _ value => some value
  | .continuing _ => none

theorem returned_value_sound {p : Prototypes} {c : Service} {fuel : Nat} {body : Stmt}
    {s : State} {value : Value} (accepted : returnedValue p c fuel body s=some value) :
    ∃t,Run p c body s (.returned t value) := by
  cases actual : statement p c fuel body s with
  | none => simp [returnedValue,actual] at accepted
  | some out =>
      cases out with
      | continuing t => simp [returnedValue,actual] at accepted
      | returned t answer =>
          simp only [returnedValue,actual,Option.bind_some,Option.some.injEq] at accepted
          subst value
          exact ⟨t,statement_sound actual⟩

#print axioms sound
#print axioms returned_value_sound
end RamanujanPV.FiniteScalarEval
