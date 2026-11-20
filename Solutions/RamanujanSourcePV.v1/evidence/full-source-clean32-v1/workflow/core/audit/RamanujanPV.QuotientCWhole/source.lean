/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCRound
import RamanujanPV.QuotientCLarge

/-! The actual outer prime-stage loop. Its invariant is derived through the
source-bound round body; no prime list or desired numerical result is supplied. -/
namespace RamanujanPV.QuotientCWhole
open LCMSourcePV.Witness.C
open LCMSourcePV.ASTLoops
open QuotientCMachine QuotientTables QuotientCExecute QuotientCRound
set_option autoImplicit false
set_option maxHeartbeats 0

def outerGuard : Expr := .binary "<=" (.var "p") (.var "r")
def outerIncrement : Expr := .unary "++" (.var "p")
def outerDeclaration : Stmt := .declare [⟨"uint64_t","p",some (.nat 2)⟩]
def outerFor : Stmt := .forLoop outerDeclaration (some outerGuard) outerIncrement roundBody

theorem actual_outer_for :
    (match QuotientCSourceV2.countFunction.body with
      | .sequence xs => xs[5]? | _ => none)=some outerFor := rfl

lemma outer_guard_eval {call : Service} {s : State} {p r : Nat}
    (hp : s.env "p"=some (.u64 p)) (hr : s.env "r"=some (.u64 r)) :
    Eval call outerGuard s s (.i32 (if p≤r then 1 else 0)) :=
  eval_le_of ((pure_var call s.heap s.env 6 "p").trans hp)
    ((pure_var call s.heap s.env 6 "r").trans hr)

lemma outer_increment_eval {call : Service} {s : State} {p : Nat}
    (hp : s.env "p"=some (.u64 p)) (hword : p+1 < modulus) :
    Eval call outerIncrement s {s with env:=bind s.env "p" (.u64 (p+1))} (.u64 (p+1)) := by
  simp [Eval,outerIncrement,eval_increment,hp,Nat.mod_eq_of_lt hword]

lemma bind_existing (env : Env) (name : String) (value : Value)
    (h : env name=some value) : bind env name value=env := by
  funext key
  by_cases same : key=name
  · subst key
    simp [QuotientCMachine.bind,h]
  · simp [QuotientCMachine.bind,Function.update_of_ne same]

/-- Every finite suffix of the actual outer C loop reaches the final invariant.
The induction is on remaining iterations, not on any assumed successful output. -/
theorem outer_for_remaining {call : Service} {N r sb lb : Nat}
    (hN : N≤2000000000000) (hr : r=N.sqrt) (fuel : Nat)
    {p : Nat} {T : Tables} {s : State}
    (hp2 : 2≤p) (hpmax : p≤r+1) (budget : r<p+fuel)
    (invariant : Invariant N r p T)
    (owned : Owned s.heap) (rep : HeapRep s.heap sb lb r T)
    (env : RoundEnv sb lb N r p s.env) :
    ∃ t U, ForRun call (some outerGuard) outerIncrement roundBody s (.continuing t) ∧
      t.env=bind s.env "p" (.u64 (r+1)) ∧ Owned t.heap ∧
      HeapRep t.heap sb lb r U ∧ Invariant N r (r+1) U := by
  have hroot : N < (r+1)*(r+1) := by
    simpa [hr,Nat.succ_eq_add_one] using Nat.lt_succ_sqrt N
  induction fuel generalizing p T s with
  | zero =>
    have heq : p=r+1 := by omega
    have hstop : ¬p≤r := by omega
    refine ⟨s,T,?_,?_,owned,rep,?_⟩
    · apply ForRun.done
      simpa [truth,Value.bits,hstop] using
        GuardRun.present (truth:=truth) (outer_guard_eval env.pValue env.rValue)
    · exact (bind_existing s.env "p" (.u64 (r+1)) (by simpa [heq] using env.pValue)).symm
    · simpa [heq] using invariant
  | succ fuel ih =>
    by_cases hpr : p≤r
    · obtain ⟨stepped,body,envStep,ownedStep,repStep⟩ :=
        round_exec hN hr hp2 hpr invariant owned rep env
      have invNext := primeRound_correct hp2 hpr hroot invariant
      have hpword : p+1 < modulus := by
        have hrN : r ≤ N := by simpa [hr] using Nat.sqrt_le_self N
        norm_num [modulus]
        omega
      let advanced : State := {stepped with env:=bind stepped.env "p" (.u64 (p+1))}
      have envNext : RoundEnv sb lb N r (p+1) advanced.env := by
        change RoundEnv sb lb N r (p+1) (bind stepped.env "p" (.u64 (p+1)))
        rw [envStep]
        exact env.bind_p (p+1)
      obtain ⟨last,U,rest,envLast,ownedLast,repLast,invLast⟩ :=
        ih (p:=p+1) (T:=primeRound N r p T) (s:=advanced)
          (by omega) (by omega) (by omega) invNext ownedStep repStep envNext
      refine ⟨last,U,?_,?_,ownedLast,repLast,invLast⟩
      · apply ForRun.next
        · simpa [truth,Value.bits,hpr] using
            GuardRun.present (truth:=truth) (outer_guard_eval env.pValue env.rValue)
        · exact body
        · exact outer_increment_eval (by rw [envStep];exact env.pValue) hpword
        · exact rest
      · calc
          last.env=bind advanced.env "p" (.u64 (r+1)) := envLast
          _=bind s.env "p" (.u64 (r+1)) := by
            simp [advanced,envStep,QuotientCMachine.bind,Function.update_idem]
    · have heq : p=r+1 := by omega
      refine ⟨s,T,?_,?_,owned,rep,?_⟩
      · apply ForRun.done
        simpa [truth,Value.bits,hpr] using
          GuardRun.present (truth:=truth) (outer_guard_eval env.pValue env.rValue)
      · exact (bind_existing s.env "p" (.u64 (r+1)) (by simpa [heq] using env.pValue)).symm
      · simpa [heq] using invariant

/-- Actual source declaration, every outer iteration and lexical cleanup.
Both arrays begin with the already executed source initialization tables. -/
theorem outer_for_exec {call : Service} {N r sb lb : Nat} {s : State}
    (hN2 : 2≤N) (hN : N≤2000000000000) (hr : r=N.sqrt)
    (owned : Owned s.heap) (rep : HeapRep s.heap sb lb r (initial N))
    (env : RoundEnv sb lb N r 2 (bind s.env "p" (.u64 2)))
    (freshP : s.env "p"=none) :
    ∃ t U, Run call outerFor s (.continuing t) ∧ t.env=s.env ∧
      Owned t.heap ∧ HeapRep t.heap sb lb r U ∧ Invariant N r (r+1) U := by
  have hr1 : 1≤r := by
    rw [hr]
    exact Nat.sqrt_pos.mpr (by omega)
  let started : State := {s with env:=bind s.env "p" (.u64 2)}
  have declaration : Declare call [⟨"uint64_t","p",some (.nat 2)⟩] s started :=
    declare_singleton_of (raw:=.i32 2) freshP
      ((pure_literal call s.heap s.env 7 2).trans (by norm_num [literal]))
      (by norm_num [uint64,Value.scalar,modulus])
  obtain ⟨last,U,loop,envLast,ownedLast,repLast,invLast⟩ :=
    outer_for_remaining hN hr r (p:=2) (T:=initial N) (s:=started)
      (by omega) (by omega) (by omega) (initial_invariant N r) owned rep env
  let t := closeScope s last
  have sameEnv : t.env=s.env :=
    QuotientCLarge.close_two_fresh freshP freshP (by simpa [started] using envLast)
  refine ⟨t,U,?_,sameEnv,ownedLast,repLast,invLast⟩
  exact StmtRun.forLoop (StmtRun.declare declaration) loop rfl

#print axioms outer_for_remaining
#print axioms outer_for_exec
end RamanujanPV.QuotientCWhole
