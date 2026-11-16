/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedC.ArraySourceCalls

namespace ScopedC.ArrayLegacyLift
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
universe u v

/-- An old successful declaration necessarily avoids the newly supported
initialized-array case, regardless of what other declarations exist in code. -/
theorem one_success {cfg : Layout} {service : Call} {d : Decl} {s t : State}
    (old : Machine.declarations cfg service [d] s=some t) :
    ArrayDeclarations.one cfg service d s=some t := by
  cases ha : d.arrayExtent with
  | none =>
    rw [ArrayDeclarations.one_legacy (cfg:=cfg) (service:=service) (d:=d) (s:=s) (Or.inl (by simp [ha]))]
    exact old
  | some extent =>
    cases hv : d.value with
    | none =>
      rw [ArrayDeclarations.one_legacy (cfg:=cfg) (service:=service) (d:=d) (s:=s) (Or.inr (by simp [hv]))]
      exact old
    | some value =>
      simp [Machine.declarations,List.foldlM,ha,hv] at old

/-- Success refinement for arbitrary lists. No all-code-legacy predicate is
needed: an initialized array anywhere on the executed old path would fail. -/
theorem declarations_success {cfg : Layout} {service : Call} {ds : List Decl} {s t : State}
    (old : Machine.declarations cfg service ds s=some t) :
    ArrayDeclarations.declarations cfg service ds s=some t := by
  induction ds generalizing s with
  | nil => exact old
  | cons d ds ih =>
    have old_cons : Machine.declarations cfg service (d::ds) s=
        (Machine.declarations cfg service [d] s).bind (fun u=>Machine.declarations cfg service ds u) := by
      simp [Machine.declarations,List.foldlM_cons]
    cases head : Machine.declarations cfg service [d] s with
    | none => simp only [old_cons,head,Option.bind_none] at old;contradiction
    | some middle =>
      have tail : Machine.declarations cfg service ds middle=some t := by
        simpa only [old_cons,head,Option.bind_some] using old
      have first := one_success head
      change (ArrayDeclarations.one cfg service d s).bind (fun u=>ArrayDeclarations.declarations cfg service ds u)=some t
      rw [first]
      exact ih tail

/-- Generic declaration-monotone map. The four simultaneous recursor motives
cover statements, sequences, for-loops and while-loops, including early returns.
Expression, truth and scope relations are unchanged. -/
theorem statement_map {State : Type u} {Value : Type v}
    {Eval : Expr→State→State→Value→Prop} {Old New : List Decl→State→State→Prop}
    {truth : Value→Bool} {Scope : State→Loops.Flow State Value→Loops.Flow State Value→Prop}
    (lift : ∀ds s t,Old ds s t→New ds s t)
    {st : Stmt} {s : State} {out : Loops.Flow State Value}
    (old : Loops.StmtRun Eval Old truth Scope st s out) : Loops.StmtRun Eval New truth Scope st s out := by
  exact Loops.StmtRun.rec
    (motive_1:=fun st s out _=>Loops.StmtRun Eval New truth Scope st s out)
    (motive_2:=fun ss s out _=>Loops.SeqRun Eval New truth Scope ss s out)
    (motive_3:=fun cond step body s out _=>Loops.ForRun Eval New truth Scope cond step body s out)
    (motive_4:=fun cond body s out _=>Loops.WhileRun Eval New truth Scope cond body s out)
    (fun s=>Loops.StmtRun.skip s)
    (fun run=>Loops.StmtRun.evaluate run)
    (fun run=>Loops.StmtRun.declare (lift _ _ _ run))
    (fun run=>Loops.StmtRun.returnValue run)
    (fun test _ mapped=>Loops.StmtRun.branch test mapped)
    (fun _ exit mapped=>Loops.StmtRun.sequence mapped exit)
    (fun _ _ exit initial loop=>Loops.StmtRun.forLoop initial loop exit)
    (fun _ exit initial=>Loops.StmtRun.forInitialReturn initial exit)
    (fun _ mapped=>Loops.StmtRun.whileLoop mapped)
    (fun s=>Loops.SeqRun.nil s)
    (fun _ _ first rest=>Loops.SeqRun.next first rest)
    (fun _ mapped=>Loops.SeqRun.returned mapped)
    (fun test=>Loops.ForRun.done test)
    (fun test _ step _ iteration rest=>Loops.ForRun.next test iteration step rest)
    (fun test _ iteration=>Loops.ForRun.returned test iteration)
    (fun test stop=>Loops.WhileRun.done test stop)
    (fun test keep _ _ iteration rest=>Loops.WhileRun.next test keep iteration rest)
    (fun test keep _ iteration=>Loops.WhileRun.returned test keep iteration)
    old

/-- Every old successful complete statement execution is valid in the additive
array model, without restricting unexecuted branches or other installed code. -/
theorem run_success {cfg : Layout} {service : Call} {st : Stmt} {s : State} {out : Loops.Flow State Value}
    (old : SourceCalls.Run cfg service st s out) : ArraySourceCalls.Run cfg service st s out :=
  statement_map (fun _ _ _ h=>declarations_success h) old

/-- Finite-rank lift of existing actual-body proofs. The same function, arguments,
full states, result, expression service and runtime boundary are retained. -/
theorem source_call {cfg : Layout} {code : List Function} {rank : Nat}
    {name : String} {args : List Value} {s t : State} {value : Value}
    (old : SourceCalls.SourceCall cfg code rank name args s value t) :
    ArraySourceCalls.SourceCall cfg code rank name args s value t := by
  induction rank generalizing name args s value t with
  | zero => exact old
  | succ rank ih =>
    rcases old with runtime | ⟨f,installed,named,service,closed,frame,args,outcome,body,finish⟩
    · exact ArraySourceCalls.runtime_leaf runtime
    · exact Or.inr ⟨f,installed,named,service,
        (fun _ _ _ _ _ h=>ih (closed _ _ _ _ _ h)),frame,args,outcome,run_success body,finish⟩

end ScopedC.ArrayLegacyLift
