/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.PrimeCount

set_option autoImplicit false
set_option maxHeartbeats 0
namespace RamanujanPV.AST.C
open LCMSourcePV.Witness.C

def trialCondition : Expr := .binary "<=" (.var "d") (.binary "/" (.var "n") (.var "d"))
def trialStep : Expr := .unary "++" (.var "d")
def remainderCondition : Expr := .binary "==" (.binary "%" (.var "n") (.var "d")) (.nat 0)
def trialBody : Stmt := .sequence [.branch remainderCondition (.returnStmt (.nat 0)) .skip,.skip]
def trialOutcome (result : Nat) (s : State) : Flow :=
  if result=0 then .returned s 0 else .continuing s

theorem literal_zero (call : Service) (s : State) : Eval call (.nat 0) s s 0 := by
  simp [Eval,eval,evalPure]
theorem literal_one (call : Service) (s : State) : Eval call (.nat 1) s s 1 := by
  simp [Eval,eval,evalPure,wordMod]

theorem trial_condition_eval {call : Service} {s : State} {n d : Nat}
    (hn : s.env "n"=some n) (hd : s.env "d"=some d) (hd2 : 2≤d) :
    Eval call trialCondition s s (bool (d≤n/d)) := by
  have hd0 : d≠0 := by omega
  simp [Eval,eval,evalPure,trialCondition,hn,hd,binary,hd0]

theorem remainder_condition_eval {call : Service} {s : State} {n d : Nat}
    (hn : s.env "n"=some n) (hd : s.env "d"=some d) (hd2 : 2≤d) :
    Eval call remainderCondition s s (bool (n%d=0)) := by
  have hd0 : d≠0 := by omega
  simp [Eval,eval,evalPure,remainderCondition,hn,hd,binary,hd0]

theorem trial_body_continue {call : Service} {s : State} {n d : Nat}
    (hn : s.env "n"=some n) (hd : s.env "d"=some d) (hd2 : 2≤d)
    (nonzero : n%d≠0) : Run call trialBody s (.continuing s) := by
  apply sequence2
  · apply LCMSourcePV.ASTLoops.StmtRun.branch (remainder_condition_eval hn hd hd2)
    simpa [truth,bool,nonzero] using LCMSourcePV.ASTLoops.StmtRun.skip s
  · exact LCMSourcePV.ASTLoops.StmtRun.skip s

theorem trial_body_return {call : Service} {s : State} {n d : Nat}
    (hn : s.env "n"=some n) (hd : s.env "d"=some d) (hd2 : 2≤d)
    (zero : n%d=0) : Run call trialBody s (.returned s 0) := by
  apply sequence2_returned
  apply LCMSourcePV.ASTLoops.StmtRun.branch (remainder_condition_eval hn hd hd2)
  simpa [truth,bool,zero] using LCMSourcePV.ASTLoops.StmtRun.returnValue (literal_zero call s)

/-- Node-by-node refinement of the actual C for-loop. The generic control
rules execute the guard, source remainder branch, increment and recursive
iteration. No complete-body interpretation constructor is used. -/
theorem trial_for_refines {n d result : Nat} (execution : TrialExec n d result)
    (word : n<wordMod) (hd2 : 2≤d) :
    ∀(call : Service) (s : State), s.env "n"=some n → s.env "d"=some d →
      ∃t, ForRun call (some trialCondition) trialStep trialBody s (trialOutcome result t) ∧
        t.heap=s.heap := by
  revert hd2
  induction execution with
  | done d guard =>
    intro hd2 call s hn hd
    refine ⟨s,?_,rfl⟩
    change ForRun call (some trialCondition) trialStep trialBody s (.continuing s)
    apply LCMSourcePV.ASTLoops.ForRun.done
    simpa [truth,bool,guard] using
      LCMSourcePV.ASTLoops.GuardRun.present (truth:=truth) (trial_condition_eval (call:=call) hn hd hd2)
  | found d guard zero =>
    intro hd2 call s hn hd
    refine ⟨s,?_,rfl⟩
    change ForRun call (some trialCondition) trialStep trialBody s (.returned s 0)
    apply LCMSourcePV.ASTLoops.ForRun.returned
    · simpa [truth,bool,guard] using
        LCMSourcePV.ASTLoops.GuardRun.present (truth:=truth) (trial_condition_eval (call:=call) hn hd hd2)
    · exact trial_body_return hn hd hd2 zero
  | step d result guard nonzero rest ih =>
    intro hd2 call s hn hd
    let next : State := {s with env:=bind s.env "d" (bump d)}
    have hb := bump_exact word hd2 guard
    obtain ⟨t,run,heap⟩ := ih (by omega) call next
      (by simp [next,bind,hn]) (by simp [next,bind])
    refine ⟨t,?_,heap⟩
    apply LCMSourcePV.ASTLoops.ForRun.next
    · simpa [truth,bool,guard] using
        LCMSourcePV.ASTLoops.GuardRun.present (truth:=truth) (trial_condition_eval (call:=call) hn hd hd2)
    · exact trial_body_continue hn hd hd2 nonzero
    · change eval call s (.unary "++" (.var "d"))=some (next,bump d)
      simp [eval,next,hd,bump]
    · exact run

def primeInput (n : Nat) (heap : Heap) : State := ⟨bind emptyEnv "n" n,heap⟩
def primeSmall : Stmt := .branch (.binary "<" (.var "n") (.nat 2)) (.returnStmt (.nat 0)) .skip
def primeFor : Stmt := .forLoop (.declare [⟨"uint64_t","d",some (.nat 2)⟩])
  (some trialCondition) trialStep trialBody
def primeTail : Stmt := .sequence [primeFor,.sequence [.returnStmt (.nat 1),.skip]]

theorem prime_source_shape : stmt Source.primeFunction.body =
    .sequence [primeSmall,primeTail] := rfl

theorem prime_small_eval {call : Service} {s : State} {n : Nat}
    (hn : s.env "n"=some n) :
    Eval call (.binary "<" (.var "n") (.nat 2)) s s (bool (n<2)) := by
  simp [Eval,eval,evalPure,hn,binary,wordMod]

/-- Actual bound source AST execution for every PrimeExec, independently of
the modular call service. Thus the trial-division helper is not a name oracle. -/
theorem prime_function_refines {n result : Nat} (execution : PrimeExec n result)
    (call : Service) (heap : Heap) :
    ∃t, Run call (stmt Source.primeFunction.body) (primeInput n heap) (.returned t result) ∧
      t.heap=heap := by
  rcases execution with ⟨word,execution⟩
  rw [prime_source_shape]
  have hn : (primeInput n heap).env "n"=some n := by simp [primeInput,bind]
  by_cases small : n<2
  · have hr : result=0 := by simpa [small] using execution
    subst result
    refine ⟨primeInput n heap,?_,rfl⟩
    apply sequence2_returned
    apply LCMSourcePV.ASTLoops.StmtRun.branch (prime_small_eval hn)
    simpa [truth,bool,small] using LCMSourcePV.ASTLoops.StmtRun.returnValue (literal_zero call (primeInput n heap))
  · have trial : TrialExec n 2 result := by simpa [small] using execution
    let initial := primeInput n heap
    let start : State := {initial with env:=bind initial.env "d" 2}
    have declaration : Declare call [⟨"uint64_t","d",some (.nat 2)⟩] initial start := by
      simp [Declare,declare,List.foldlM,evalPure,start,wordMod]
    obtain ⟨t,loop,hheap⟩ := trial_for_refines trial word (by omega) call start
      (by simp [start,initial,primeInput,bind]) (by simp [start,bind])
    have first : Run call primeSmall initial (.continuing initial) := by
      apply LCMSourcePV.ASTLoops.StmtRun.branch (prime_small_eval hn)
      simpa [truth,bool,small] using LCMSourcePV.ASTLoops.StmtRun.skip initial
    rcases trial_values trial with hr|hr
    · subst result
      refine ⟨t,sequence2 first ?_,hheap⟩
      apply sequence2_returned
      exact LCMSourcePV.ASTLoops.StmtRun.forLoop (LCMSourcePV.ASTLoops.StmtRun.declare declaration) loop rfl
    · subst result
      refine ⟨t,sequence2 first ?_,hheap⟩
      apply sequence2
      · exact LCMSourcePV.ASTLoops.StmtRun.forLoop (LCMSourcePV.ASTLoops.StmtRun.declare declaration) loop rfl
      · exact sequence2_returned (LCMSourcePV.ASTLoops.StmtRun.returnValue (literal_one call t))

#print axioms prime_function_refines

/-- Only this installed source helper is a service. Its complete source body
has an execution for every supported call; see service_closed below. -/
def service : Service := fun name args =>
  if name="rpc_is_prime" then match args with
    | [n] => if n<wordMod then some (if Nat.Prime n then 1 else 0) else none
    | _ => none
  else none

theorem service_on_exec {n bit : Nat} (run : PrimeExec n bit) :
    service "rpc_is_prime" [n]=some bit := by
  have word := run.1
  by_cases prime : Nat.Prime n
  · have b := (prime_exec_correct run).2.mpr prime
    simp [service,word,prime,b]
  · rcases (prime_exec_correct run).1 with b|b
    · simp [service,word,prime,b]
    · exact False.elim (prime ((prime_exec_correct run).2.mp b))

theorem service_closed {name : String} {args : List Nat} {bit : Nat}
    (call : service name args=some bit) (heap : Heap) :
    ∃n, name="rpc_is_prime" ∧ args=[n] ∧
      ∃t, Run service (stmt Source.primeFunction.body) (primeInput n heap) (.returned t bit) ∧
        t.heap=heap := by
  by_cases nameEq : name="rpc_is_prime"
  · subst name
    cases args with
    | nil => simp [service] at call
    | cons n rest =>
      cases rest with
      | cons a as => simp [service] at call
      | nil =>
        by_cases word : n<wordMod
        · have bitEq : (if Nat.Prime n then 1 else 0)=bit := by simpa [service,word] using call
          obtain ⟨result,run⟩ := prime_exec_terminates n word
          have equal : result=bit := by
            have source := service_on_exec run
            rw [call] at source
            exact (Option.some.inj source).symm
          subst result
          exact ⟨n,rfl,rfl,prime_function_refines run service heap⟩
        · simp [service,word] at call
  · simp [service,nameEq] at call

def countCondition : Expr := .binary "<" (.var "n") (.var "bound")
def countIncrement : Expr := .unary "++" (.var "n")
def countAdd : Expr := .binary "=" (.var "count")
  (.binary "+" (.var "count") (.call (.var "rpc_is_prime") [.var "n"]))
def countBody : Stmt := .sequence [.eval countIncrement,.sequence [.eval countAdd,.skip]]

theorem count_body_shape : stmt Source.countFunction.body =
    .sequence [.declare [⟨"uint64_t","n",some (.nat 0)⟩],
      .sequence [.declare [⟨"uint64_t","count",some (.nat 0)⟩],
        .sequence [.whileLoop countCondition countBody,
          .sequence [.returnStmt (.var "count"),.skip]]]] := rfl

theorem count_condition_eval {s : State} {bound n : Nat}
    (hb : s.env "bound"=some bound) (hn : s.env "n"=some n) :
    Eval service countCondition s s (bool (n<bound)) := by
  simp [Eval,eval,evalPure,countCondition,hb,hn,binary]

theorem count_loop_refines {bound n count result : Nat}
    (execution : CountExec bound n count result) (word : bound<wordMod)
    (before : n≤bound) (countBound : count≤n) :
    ∀s : State, s.env "bound"=some bound → s.env "n"=some n →
      s.env "count"=some count →
      ∃t, WhileRun service countCondition countBody s (.continuing t) ∧
        t.env "count"=some result ∧ t.heap=s.heap := by
  induction execution with
  | done stop =>
    intro s hb hn hc
    refine ⟨s,?_,hc,rfl⟩
    apply LCMSourcePV.ASTLoops.WhileRun.done (count_condition_eval hb hn)
    simp [truth,bool,stop]
  | @step n count bit result guard prime rest ih =>
    intro s hb hn hc
    have nextWord : n+1<wordMod := by omega
    have nextEq : (n+1)%wordMod=n+1 := Nat.mod_eq_of_lt nextWord
    have bitBound : bit≤1 := by rcases (prime_exec_correct prime).1 with h|h <;> omega
    have newBound : (count+bit)%wordMod≤(n+1)%wordMod := by
      rw [nextEq,Nat.mod_eq_of_lt (show count+bit<wordMod by omega)]
      omega
    let advanced : State := {s with env:=bind s.env "n" ((n+1)%wordMod)}
    let counted : State := {advanced with env:=bind advanced.env "count" ((count+bit)%wordMod)}
    have primeCall : service "rpc_is_prime" [(n+1)%wordMod]=some bit := service_on_exec prime
    have increment : Eval service countIncrement s advanced ((n+1)%wordMod) := by
      simp [Eval,eval,countIncrement,hn,advanced]
    have add : Eval service countAdd advanced counted ((count+bit)%wordMod) := by
      change eval service advanced countAdd=some (counted,(count+bit)%wordMod)
      simp [eval,evalPure,countAdd,advanced,counted,bind,hc,binary,primeCall]
    obtain ⟨t,loop,last,heap⟩ := ih (by rw [nextEq];omega) newBound counted
      (by simp [counted,advanced,bind,hb])
      (by simp [counted,advanced,bind]) (by simp [counted,bind])
    refine ⟨t,?_,last,heap⟩
    apply LCMSourcePV.ASTLoops.WhileRun.next (count_condition_eval hb hn)
    · simp [truth,bool,guard]
    · apply sequence2 (LCMSourcePV.ASTLoops.StmtRun.evaluate increment)
      exact sequence2 (LCMSourcePV.ASTLoops.StmtRun.evaluate add) (LCMSourcePV.ASTLoops.StmtRun.skip counted)
    · exact loop

def countInput (bound : Nat) (heap : Heap) : State := ⟨bind emptyEnv "bound" bound,heap⟩

/-- Actual source function execution, including both local initializations,
every count-loop update and the final return expression. -/
theorem count_function_refines {bound result : Nat}
    (execution : CountExec bound 0 0 result) (word : bound<wordMod) (heap : Heap) :
    ∃t, Run service (stmt Source.countFunction.body) (countInput bound heap) (.returned t result) ∧
      t.heap=heap := by
  let initial := countInput bound heap
  let started : State := {initial with env:=bind initial.env "n" 0}
  let counted : State := {started with env:=bind started.env "count" 0}
  have declareN : Declare service [⟨"uint64_t","n",some (.nat 0)⟩] initial started := by
    simp [Declare,declare,List.foldlM,evalPure,started]
  have declareCount : Declare service [⟨"uint64_t","count",some (.nat 0)⟩] started counted := by
    simp [Declare,declare,List.foldlM,evalPure,counted]
  obtain ⟨t,loop,last,unchanged⟩ := count_loop_refines execution word (by omega) (by omega) counted
    (by simp [counted,started,initial,countInput,bind])
    (by simp [counted,started,bind]) (by simp [counted,bind])
  refine ⟨t,?_,unchanged⟩
  rw [count_body_shape]
  apply sequence2 (LCMSourcePV.ASTLoops.StmtRun.declare declareN)
  apply sequence2 (LCMSourcePV.ASTLoops.StmtRun.declare declareCount)
  apply sequence2 (LCMSourcePV.ASTLoops.StmtRun.whileLoop loop)
  apply sequence2_returned
  apply LCMSourcePV.ASTLoops.StmtRun.returnValue
  simp [Eval,eval,evalPure,last]

/-- The source-bound trial-count program computes the actual Mathlib pi for
all represented bounds. This is a generic source correctness theorem; it
has not replaced any large finite numerical leaf by itself. -/
theorem source_count_is_primeCounting (bound : Nat) (word : bound<wordMod) (heap : Heap) :
    LCMSourcePV.RestrictedC.SourceCorresponds Source.render Source.actualSource Source.selectedProgram ∧
    (∃t, Run service (stmt Source.countFunction.body) (countInput bound heap)
      (.returned t (Nat.primeCounting bound)) ∧ t.heap=heap) ∧
    (∀name args bit, service name args=some bit →
      ∃n, name="rpc_is_prime" ∧ args=[n] ∧
        ∃t, Run service (stmt Source.primeFunction.body) (primeInput n heap) (.returned t bit) ∧
          t.heap=heap) := by
  exact ⟨Source.actual_source_checked,
    count_function_refines (count_exec_complete bound word) word heap,
    fun _ _ _ run=>service_closed run heap⟩

#print axioms count_function_refines
#print axioms source_count_is_primeCounting
#print axioms service_closed
#print axioms count_loop_refines
end RamanujanPV.AST.C
