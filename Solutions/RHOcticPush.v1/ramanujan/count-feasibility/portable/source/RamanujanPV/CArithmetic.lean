/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.CSource
import LCMSourcePV.ASTLoops
import Mathlib.NumberTheory.PrimeCounting

set_option autoImplicit false
set_option maxHeartbeats 0

namespace RamanujanPV

def wordMod : Nat := 2^64
def bump (d : Nat) : Nat := (d+1) % wordMod

/-- Big-step execution of the actual C `for(d=2;d<=n/d;++d)` body.
The condition, remainder test, early return and uint64 increment are explicit.
This relation performs no primality oracle call. -/
inductive TrialExec (n : Nat) : Nat → Nat → Prop
  | done (d : Nat) (guard : ¬ d ≤ n/d) : TrialExec n d 1
  | found (d : Nat) (guard : d ≤ n/d) (divides : n%d=0) : TrialExec n d 0
  | step (d result : Nat) (guard : d ≤ n/d) (nonzero : n%d≠0)
      (rest : TrialExec n (bump d) result) : TrialExec n d result

/-- Execution of the complete source function: the small-input branch,
initial divisor and returned scalar. Its input is a represented uint64 word. -/
def PrimeExec (n result : Nat) : Prop :=
  n < wordMod ∧ if n < 2 then result=0 else TrialExec n 2 result

theorem bump_exact {n d : Nat} (hn : n < wordMod)
    (hd : 2 ≤ d) (hg : d ≤ n/d) : bump d = d+1 := by
  have hn0 : 0<n := by
    have hdn := hg.trans (Nat.div_le_self n d)
    omega
  have hdn : d<n := hg.trans_lt (Nat.div_lt_self hn0 (by omega))
  unfold bump
  exact Nat.mod_eq_of_lt (by omega)

theorem trial_values {n d result : Nat} (run : TrialExec n d result) :
    result=0 ∨ result=1 := by
  induction run with
  | done => exact Or.inr rfl
  | found => exact Or.inl rfl
  | step _ _ _ _ _ ih => exact ih

theorem trial_success_sound {n d result : Nat} (run : TrialExec n d result)
    (hn : n < wordMod) (hn2 : 2 ≤ n) (hd : 2 ≤ d)
    (prior : ∀ m, 2 ≤ m → m < d → ¬ m ∣ n) :
    result=1 → Nat.Prime n := by
  induction run with
  | done d hg =>
    intro _
    apply Nat.prime_def_le_sqrt.mpr
    refine ⟨hn2,?_⟩
    intro m hm hmS hdvd
    have hmSq : m*m ≤ n := Nat.le_sqrt.mp hmS
    have hmd : m < d := by
      by_contra h
      have hdm : d ≤ m := by omega
      have hdd : d*d ≤ n := (Nat.mul_le_mul hdm hdm).trans hmSq
      have hdiv : d ≤ n/d := (Nat.le_div_iff_mul_le (by omega : 0<d)).mpr hdd
      exact hg hdiv
    exact prior m hm hmd hdvd
  | found d hg hzero => intro h; omega
  | step d result hg hnzero rest ih =>
    intro hr
    have hb := bump_exact hn hd hg
    apply ih (by omega) ?_ hr
    intro m hm hmd hdvd
    rw [hb] at hmd
    by_cases he : m=d
    · subst m
      exact hnzero (Nat.mod_eq_zero_of_dvd hdvd)
    · exact prior m hm (by omega) hdvd

theorem trial_failure_sound {n d result : Nat} (run : TrialExec n d result)
    (hn : n < wordMod) (hd : 2 ≤ d) : result=0 → ¬ Nat.Prime n := by
  induction run with
  | done => intro h; omega
  | found d hg hzero =>
    intro _ hp
    have hdn : d<n := hg.trans_lt (Nat.div_lt_self hp.pos (by omega))
    exact (Nat.prime_def_lt'.mp hp).2 d hd hdn (Nat.dvd_of_mod_eq_zero hzero)
  | step d result hg hnzero rest ih =>
    have hb := bump_exact hn hd hg
    exact ih (by omega)

/-- Source-loop termination with enough finite C iterations. No execution
success or mathematical primality fact is a premise. -/
theorem trial_terminates (n : Nat) (hn : n < wordMod) :
    ∀ fuel d, 2 ≤ d → n < d+fuel → ∃ result, TrialExec n d result := by
  intro fuel
  induction fuel with
  | zero =>
    intro d hd hbound
    refine ⟨1,TrialExec.done d ?_⟩
    intro hg
    have hdn := hg.trans (Nat.div_le_self n d)
    omega
  | succ fuel ih =>
    intro d hd hbound
    by_cases hg : d ≤ n/d
    · by_cases hz : n%d=0
      · exact ⟨0,TrialExec.found d hg hz⟩
      · have hb := bump_exact hn hd hg
        obtain ⟨result,rest⟩ := ih (bump d) (by omega) (by omega)
        exact ⟨result,TrialExec.step d result hg hz rest⟩
    · exact ⟨1,TrialExec.done d hg⟩

theorem prime_exec_terminates (n : Nat) (hn : n < wordMod) :
    ∃ result, PrimeExec n result := by
  by_cases hsmall : n<2
  · exact ⟨0,hn,by simp [hsmall]⟩
  · obtain ⟨result,run⟩ := trial_terminates n hn (n+1) 2 (by omega) (by omega)
    exact ⟨result,hn,by simpa [hsmall] using run⟩

theorem prime_exec_correct {n result : Nat} (run : PrimeExec n result) :
    (result=0 ∨ result=1) ∧ (result=1 ↔ Nat.Prime n) := by
  rcases run with ⟨hn,run⟩
  by_cases hsmall : n<2
  · have hr : result=0 := by simpa [hsmall] using run
    refine ⟨Or.inl hr,?_⟩
    constructor
    · intro h; omega
    · intro hp; have := hp.two_le; omega
  · have hrun : TrialExec n 2 result := by simpa [hsmall] using run
    refine ⟨trial_values hrun,?_⟩
    constructor
    · exact trial_success_sound hrun hn (by omega) (by omega)
        (by intro m hm hlt; omega)
    · intro hp
      rcases trial_values hrun with hz | ho
      · exact False.elim (trial_failure_sound hrun hn (by omega) hz hp)
      · exact ho

theorem prime_exec_of_prime {n : Nat} (hn : n < wordMod) (hp : Nat.Prime n) :
    PrimeExec n 1 := by
  obtain ⟨result,run⟩ := prime_exec_terminates n hn
  have hr := (prime_exec_correct run).2.mpr hp
  simpa only [hr] using run

theorem prime_exec_of_not_prime {n : Nat} (hn : n < wordMod) (hp : ¬ Nat.Prime n) :
    PrimeExec n 0 := by
  obtain ⟨result,run⟩ := prime_exec_terminates n hn
  rcases (prime_exec_correct run).1 with hz | ho
  · simpa only [hz] using run
  · exact False.elim (hp ((prime_exec_correct run).2.mp ho))

#print axioms prime_exec_correct
#print axioms prime_exec_of_prime
#print axioms prime_exec_of_not_prime

end RamanujanPV

set_option autoImplicit false
set_option maxHeartbeats 0
namespace RamanujanPV.AST
namespace C
open LCMSourcePV.Witness.C

/-- Structural translation of the already source-bound tree. All source
operations, expressions and control statements are translated individually. -/
def expr : Source.Expr → Expr
  | .lit n => .nat n
  | .var v => .var (Source.varText v)
  | .maxWord => .var "UINT64_MAX"
  | .binary op a b => .binary (Source.binText op) (expr a) (expr b)
  | .call1 f a => .call (.var (Source.fnText f)) [expr a]
  | .call2 f a b => .call (.var (Source.fnText f)) [expr a,expr b]

def update : Source.Update → Expr
  | .increment v => .unary "++" (.var (Source.varText v))
  | .decrement v => .unary "--" (.var (Source.varText v))

def stmt : Source.Stmt → Stmt
  | .empty => .skip
  | .sequence a b => .sequence [stmt a,stmt b]
  | .declare v e => .declare [⟨"uint64_t",Source.varText v,some (expr e)⟩]
  | .assign v e => .eval (.binary "=" (.var (Source.varText v)) (expr e))
  | .store base index value => .eval (.binary "=" (.index (expr base) (expr index)) (expr value))
  | .update op => .eval (update op)
  | .returnValue e => .returnStmt (expr e)
  | .ifReturn condition value => .branch (expr condition) (.returnStmt (expr value)) .skip
  | .whileLoop condition body => .whileLoop (expr condition) (stmt body)
  | .forLoop v init condition step body =>
      .forLoop (.declare [⟨"uint64_t",Source.varText v,some (expr init)⟩])
        (some (expr condition)) (update step) (stmt body)

abbrev Env := String → Option Nat
abbrev Service := String → List Nat → Option Nat

def bind (env : Env) (key : String) (value : Nat) : Env :=
  fun name => if name == key then some value else env name
def emptyEnv : Env := fun _ => none

structure Heap where
  base : Nat
  extent : Nat
  words : Nat → Nat

structure State where
  env : Env
  heap : Heap


def truth (n : Nat) : Bool := n != 0
def bool (p : Prop) [Decidable p] : Nat := if p then 1 else 0

/-- Exact C uint64 operations; division and remainder reject zero. -/
def binary (op : String) (a b : Nat) : Option Nat :=
  if op == "+" then some ((a+b)%wordMod)
  else if op == "-" then some ((a+wordMod-b)%wordMod)
  else if op == "*" then some ((a*b)%wordMod)
  else if op == "/" then if b=0 then none else some (a/b)
  else if op == "%" then if b=0 then none else some (a%b)
  else if op == "<" then some (bool (a<b))
  else if op == "<=" then some (bool (a≤b))
  else if op == ">" then some (bool (b<a))
  else if op == "==" then some (bool (a=b))
  else none

/-- Pure source expressions. Calls are modular and receive actual evaluated
arguments; each selected service is separately refined to its real AST body. -/
def evalPure (call : Service) (env : Env) : Nat → Expr → Option Nat
  | 0,_ => none
  | fuel+1,.nat n => some (n%wordMod)
  | fuel+1,.var name => if name == "UINT64_MAX" then some (wordMod-1) else env name
  | fuel+1,.binary "&&" a b => do
      let x ← evalPure call env fuel a
      if truth x then pure (bool ((←evalPure call env fuel b)≠0)) else pure 0
  | fuel+1,.binary "||" a b => do
      let x ← evalPure call env fuel a
      if truth x then pure 1 else pure (bool ((←evalPure call env fuel b)≠0))
  | fuel+1,.binary op a b => do
      binary op (←evalPure call env fuel a) (←evalPure call env fuel b)
  | fuel+1,.call (.var name) args => do
      call name (←args.mapM (evalPure call env fuel))
  | _,_ => none

def store (heap : Heap) (base index value : Nat) : Option Heap :=
  if base=heap.base ∧ index<heap.extent ∧ base+8*index<wordMod ∧ value<wordMod then
    some {heap with words:=fun i=>if i=index then value else heap.words i}
  else none

/-- Standalone C assignment, checked indexed store, preincrement/decrement,
and pure expression evaluation. Locals are scalar registers: the selected
functions take no local address and have no observable shadowed local. -/
def eval (call : Service) (s : State) : Expr → Option (State × Nat)
  | .binary "=" (.var name) rhs => do
      let _ ← s.env name
      let value ← evalPure call s.env 100 rhs
      pure ({s with env:=bind s.env name value},value)
  | .binary "=" (.index base index) rhs => do
      let b ← evalPure call s.env 100 base
      let i ← evalPure call s.env 100 index
      let value ← evalPure call s.env 100 rhs
      let heap ← store s.heap b i value
      pure ({s with heap:=heap},value)
  | .unary "++" (.var name) => do
      let old ← s.env name
      let value := (old+1)%wordMod
      pure ({s with env:=bind s.env name value},value)
  | .unary "--" (.var name) => do
      let old ← s.env name
      let value := (old+wordMod-1)%wordMod
      pure ({s with env:=bind s.env name value},value)
  | e => do pure (s,←evalPure call s.env 100 e)

def declare (call : Service) (ds : List Decl) (s : State) : Option State :=
  ds.foldlM (fun state d => do
    if d.type != "uint64_t" then none else
      let initial ← d.value
      let value ← evalPure call state.env 100 initial
      pure {state with env:=bind state.env d.name value}) s

def Eval (call : Service) (e : Expr) (s t : State) (value : Nat) : Prop :=
  eval call s e=some (t,value)
def Declare (call : Service) (ds : List Decl) (s t : State) : Prop :=
  declare call ds s=some t
def Scope (_ : State) (inner outer : LCMSourcePV.ASTLoops.Flow State Nat) : Prop := outer=inner
abbrev Flow := LCMSourcePV.ASTLoops.Flow State Nat
abbrev Run (call : Service) := LCMSourcePV.ASTLoops.StmtRun (Eval call) (Declare call) truth Scope
abbrev SeqRun (call : Service) := LCMSourcePV.ASTLoops.SeqRun (Eval call) (Declare call) truth Scope
abbrev ForRun (call : Service) := LCMSourcePV.ASTLoops.ForRun (Eval call) (Declare call) truth Scope
abbrev WhileRun (call : Service) := LCMSourcePV.ASTLoops.WhileRun (Eval call) (Declare call) truth Scope

theorem bind_same (env : Env) (key : String) (x y : Nat) :
    bind (bind env key x) key y=bind env key y := by
  funext name
  by_cases h : name=key <;> simp [bind,h]

theorem singleton {call : Service} {body : Stmt} {s : State} {out : Flow}
    (run : Run call body s out) : SeqRun call [body] s out := by
  cases out with
  | continuing t => exact LCMSourcePV.ASTLoops.SeqRun.next run (LCMSourcePV.ASTLoops.SeqRun.nil t)
  | returned t value => exact LCMSourcePV.ASTLoops.SeqRun.returned run

theorem sequence2 {call : Service} {a b : Stmt} {s t : State} {out : Flow}
    (first : Run call a s (.continuing t)) (second : Run call b t out) :
    Run call (.sequence [a,b]) s out :=
  LCMSourcePV.ASTLoops.StmtRun.sequence (LCMSourcePV.ASTLoops.SeqRun.next first (singleton second)) rfl

theorem sequence2_returned {call : Service} {a b : Stmt} {s t : State} {value : Nat}
    (first : Run call a s (.returned t value)) :
    Run call (.sequence [a,b]) s (.returned t value) :=
  LCMSourcePV.ASTLoops.StmtRun.sequence (LCMSourcePV.ASTLoops.SeqRun.returned first) rfl

#print axioms bind_same
end C
end RamanujanPV.AST
