/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.SegmentCMark

namespace RamanujanPV.SegmentCDivisors
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open QuotientCMachine SegmentCheckerMath SegmentMemory SegmentCMark
set_option autoImplicit false
set_option maxHeartbeats 4000000

def baseExpr : Expr := .binary "*" (.binary "/" (.var "lo") (.var "d")) (.var "d")
def squareExpr : Expr := .binary "*" (.var "d") (.var "d")
def addExpr : Expr := .binary "+" (.var "first") (.var "d")
def lowerBranch : Stmt := .branch (.binary "<" (.var "first") (.var "lo"))
  (.eval (.binary "=" (.var "first") addExpr)) .skip
def squareBranch : Stmt := .branch (.binary "<" (.var "first") squareExpr)
  (.eval (.binary "=" (.var "first") squareExpr)) .skip
def divisorBody : Stmt := .sequence [
  .declare [⟨"uint64_t","first",some baseExpr⟩], lowerBranch, squareBranch, markFor]
def divisorGuard : Expr := .binary "<=" (.var "d") (.binary "/" (.var "hi") (.var "d"))
def divisorIncrement : Expr := .unary "++" (.var "d")
def divisorFor : Stmt := .forLoop (.declare [⟨"uint64_t","d",some (.nat 2)⟩])
  (some divisorGuard) divisorIncrement divisorBody

def actualDivisorFor : Option Stmt := match SegmentCheckerSource.checkerFunction.body with
  | .sequence body => body[6]?
  | _ => none
theorem actual_divisor_for : actualDivisorFor = some divisorFor := rfl

structure DivisorEnv (lo hi d base : Nat) (env : Env) : Prop where
  loValue : env "lo" = some (.u64 lo)
  hiValue : env "hi" = some (.u64 hi)
  dValue : env "d" = some (.u64 d)
  flagsValue : env "flags" = some (.ptr base)
  firstFresh : env "first" = none
  mFresh : env "m" = none

lemma DivisorEnv.bind_d {lo hi d base : Nat} {env : Env}
    (h : DivisorEnv lo hi d base env) (next : Nat) :
    DivisorEnv lo hi next base (bind env "d" (.u64 next)) := by
  exact {
    loValue := by simpa using h.loValue
    hiValue := by simpa using h.hiValue
    dValue := by simp
    flagsValue := by simpa using h.flagsValue
    firstFresh := by simpa using h.firstFresh
    mFresh := by simpa using h.mFresh }

lemma pure_base (k : Nat) {call : Service} {heap : Heap} {env : Env} {lo d : Nat}
    (hlo : env "lo" = some (.u64 lo)) (hd : env "d" = some (.u64 d))
    (hd0 : 0 < d) (hlow : lo < modulus) :
    evalPure call heap env (k+3) baseExpr = some (.u64 (lo/d*d)) :=
  pure_binary_of (pure_binary_of ((pure_var call heap env k "lo").trans hlo)
      ((pure_var call heap env k "d").trans hd) (binary_u64_div hd0 hlow))
    ((pure_var call heap env (k+1) "d").trans hd)
    (binary_u64_mul ((Nat.div_mul_le_self lo d).trans_lt hlow))

lemma pure_square (k : Nat) {call : Service} {heap : Heap} {env : Env} {d : Nat}
    (hd : env "d" = some (.u64 d)) (hword : d*d < modulus) :
    evalPure call heap env (k+2) squareExpr = some (.u64 (d*d)) :=
  pure_binary_of ((pure_var call heap env k "d").trans hd)
    ((pure_var call heap env k "d").trans hd) (binary_u64_mul hword)

theorem lower_branch_exec {call : Service} {s : State} {lo d first : Nat}
    (hlo : s.env "lo" = some (.u64 lo)) (hd : s.env "d" = some (.u64 d))
    (hf : s.env "first" = some (.u64 first)) (hsum : first+d < modulus) :
    ∃ t, Run call lowerBranch s (.continuing t) ∧
      t.env = bind s.env "first" (.u64 (if first < lo then first+d else first)) ∧ t.heap=s.heap := by
  have test := eval_lt_of ((pure_var call s.heap s.env 6 "first").trans hf)
    ((pure_var call s.heap s.env 6 "lo").trans hlo)
  by_cases h : first < lo
  · let t : State := {s with env:=bind s.env "first" (.u64 (first+d))}
    have step : Eval call (.binary "=" (.var "first") addExpr) s t (.u64 (first+d)) :=
      eval_variable_assign_of hf
        (pure_binary_of ((pure_var call s.heap s.env 6 "first").trans hf)
          ((pure_var call s.heap s.env 6 "d").trans hd) (binary_u64_add hsum))
        (uint64_of_u64 hsum)
    refine ⟨t,?_,by simp [t,h],rfl⟩
    apply StmtRun.branch test
    simpa [truth,Value.bits,h] using StmtRun.evaluate step
  · refine ⟨s,?_,?_,rfl⟩
    · apply StmtRun.branch test
      simpa [truth,Value.bits,h] using StmtRun.skip (Eval:=Eval call)
        (Declare:=Declare call) (truth:=truth) (Scope:=Scope) s
    · simp only [h,ite_false]
      symm
      funext name
      by_cases hn : name="first"
      · subst name; simp [QuotientCMachine.bind,hf]
      · simp [QuotientCMachine.bind,Function.update_of_ne hn]

theorem square_branch_exec {call : Service} {s : State} {d first : Nat}
    (hd : s.env "d" = some (.u64 d)) (hf : s.env "first" = some (.u64 first))
    (hsquare : d*d < modulus) :
    ∃ t, Run call squareBranch s (.continuing t) ∧
      t.env = bind s.env "first" (.u64 (if first < d*d then d*d else first)) ∧ t.heap=s.heap := by
  have test := eval_lt_of ((pure_var call s.heap s.env 6 "first").trans hf)
    (pure_square 5 hd hsquare)
  by_cases h : first < d*d
  · let t : State := {s with env:=bind s.env "first" (.u64 (d*d))}
    have step : Eval call (.binary "=" (.var "first") squareExpr) s t (.u64 (d*d)) :=
      eval_variable_assign_of hf (pure_square 6 hd hsquare) (uint64_of_u64 hsquare)
    refine ⟨t,?_,by simp [t,h],rfl⟩
    apply StmtRun.branch test
    simpa [truth,Value.bits,h] using StmtRun.evaluate step
  · refine ⟨s,?_,?_,rfl⟩
    · apply StmtRun.branch test
      simpa [truth,Value.bits,h] using StmtRun.skip (Eval:=Eval call)
        (Declare:=Declare call) (truth:=truth) (Scope:=Scope) s
    · simp only [h,ite_false]
      symm
      funext name
      by_cases hn : name="first"
      · subst name; simp [QuotientCMachine.bind,hf]
      · simp [QuotientCMachine.bind,Function.update_of_ne hn]

theorem divisor_body_exec {call : Service} {s : State} {lo hi d base : Nat} {flags : Nat → Nat}
    (hd : 0 < d) (hlo : lo ≤ hi) (hsquare : d*d ≤ hi) (hhi : hi ≤ 2000000000000)
    (owned : Owned s.heap) (rep : FlagsRep s.heap base (hi-lo+1) flags)
    (env : DivisorEnv lo hi d base s.env) :
    ∃ t, Run call divisorBody s (.continuing t) ∧ t.env=s.env ∧ Owned t.heap ∧
      FlagsRep t.heap base (hi-lo+1) (sweep lo d flags) ∧
      (∀ other j, other≠base→QuotientCMachine.read t.heap other j=QuotientCMachine.read s.heap other j) := by
  have hdhi : d ≤ hi := by nlinarith
  have hhw : hi < modulus := by norm_num [modulus]; omega
  have hlw : lo < modulus := hlo.trans_lt hhw
  have hpp : d*d < modulus := hsquare.trans_lt hhw
  let initial := lo/d*d
  have hib : initial ≤ lo := Nat.div_mul_le_self lo d
  have hiss : initial+d < modulus := by norm_num [modulus]; omega
  let first : State := {s with env:=bind s.env "first" (.u64 initial)}
  have declaration : Declare call [⟨"uint64_t","first",some baseExpr⟩] s first :=
    declare_singleton_of env.firstFresh (pure_base 5 env.loValue env.dValue hd hlw)
      (uint64_of_u64 (hib.trans_lt hlw))
  obtain ⟨lower,hlower,heLower,hhLower⟩ := lower_branch_exec (call:=call) (s:=first)
    (first:=initial)
    (by simpa [first] using env.loValue) (by simpa [first] using env.dValue)
    (by simp [first]) hiss
  obtain ⟨square,hsquareRun,heSquare,hhSquare⟩ := square_branch_exec (call:=call) (s:=lower)
    (first:=if initial < lo then initial+d else initial)
    (by simp [heLower,first,QuotientCMachine.bind,env.dValue])
    (by simp [heLower]) hpp
  have squareEnv : MarkEnv lo hi d (firstMultiple lo d) base square.env := by
    constructor
    · simp [heSquare,heLower,first,QuotientCMachine.bind,env.loValue]
    · simp [heSquare,heLower,first,QuotientCMachine.bind,env.hiValue]
    · simp [heSquare,heLower,first,QuotientCMachine.bind,env.dValue]
    · have hf := sourceFirst_eq_first (lo:=lo) hd
      simpa [heSquare,sourceFirst,initial] using congrArg (fun n => some (Value.u64 n)) hf
    · simp [heSquare,heLower,first,QuotientCMachine.bind,env.flagsValue]
  obtain ⟨last,hmark,heLast,ownedLast,repLast,frameLast⟩ := mark_for_exec hd hlo hsquare hhi
    (by simpa [hhSquare,hhLower,first] using owned)
    (by simpa [hhSquare,hhLower,first] using rep) squareEnv
    (by simp [heSquare,heLower,first,QuotientCMachine.bind,env.mFresh])
  let t := closeScope s last
  have envt : t.env=s.env := by
    funext name
    by_cases hn : name="first"
    · subst name; simp [t,closeScope,env.firstFresh]
    · change (if (s.env name).isSome then last.env name else none) = s.env name
      rw [heLast,heSquare,heLower]
      simp only [first,QuotientCMachine.bind,Function.update_of_ne hn]
      cases h : s.env name <;> rfl
  refine ⟨t,?_,envt,ownedLast,repLast,?_⟩
  · apply StmtRun.sequence (inner:=.continuing last)
    · exact SeqRun.next (StmtRun.declare declaration)
        (SeqRun.next hlower (SeqRun.next hsquareRun (SeqRun.next hmark (SeqRun.nil last))))
    · rfl
  · intro other j hother
    simpa [t,closeScope,hhSquare,hhLower,first] using frameLast other j hother

lemma guard_eval {call : Service} {s : State} {hi d : Nat}
    (hhi : s.env "hi" = some (.u64 hi)) (hd : s.env "d" = some (.u64 d))
    (hd0 : 0 < d) (hword : hi < modulus) :
    Eval call divisorGuard s s (.i32 (if d ≤ hi/d then 1 else 0)) :=
  eval_le_of ((pure_var call s.heap s.env 6 "d").trans hd)
    (pure_binary_of ((pure_var call s.heap s.env 5 "hi").trans hhi)
      ((pure_var call s.heap s.env 5 "d").trans hd) (binary_u64_div hd0 hword))

theorem divisors_remaining (remaining : Nat) {call : Service} {s : State}
    {lo hi base processed : Nat}
    (hlo : 2 ≤ lo) (horder : lo ≤ hi) (hhi : hi ≤ 2000000000000)
    (owned : Owned s.heap) (rep : FlagsRep s.heap base (hi-lo+1) (passes lo processed))
    (env : DivisorEnv lo hi (processed+2) base s.env)
    (hcount : processed+remaining = hi.sqrt-1) :
    ∃ t, ForRun call (some divisorGuard) divisorIncrement divisorBody s (.continuing t) ∧
      t.env=bind s.env "d" (.u64 (hi.sqrt+1)) ∧ Owned t.heap ∧
      FlagsRep t.heap base (hi-lo+1) (finalFlags lo hi) ∧
      (∀ other j,other≠base→QuotientCMachine.read t.heap other j=QuotientCMachine.read s.heap other j) := by
  have hr1 : 1 ≤ hi.sqrt := Nat.sqrt_pos.mpr (by omega)
  have hhw : hi < modulus := by norm_num [modulus]; omega
  induction remaining generalizing s processed with
  | zero =>
      have hp : processed=hi.sqrt-1 := by omega
      have hdEq : processed+2=hi.sqrt+1 := by omega
      have hstop : ¬processed+2 ≤ hi/(processed+2) := by
        intro h
        have hsq := (Nat.le_div_iff_mul_le (by omega : 0<processed+2)).mp h
        have ht := Nat.lt_succ_sqrt hi
        rw [hdEq] at hsq
        nlinarith
      refine ⟨s,?_,?_,owned,?_,by simp⟩
      · apply ForRun.done
        have test := GuardRun.present (truth:=truth)
          (guard_eval (call:=call) env.hiValue env.dValue (by omega) hhw)
        simpa [truth,Value.bits,hstop] using test
      · rw [←hdEq]
        symm
        funext name
        by_cases hn : name="d"
        · subst name; simp [QuotientCMachine.bind,env.dValue]
        · simp [QuotientCMachine.bind,Function.update_of_ne hn]
      · simpa [hp,finalFlags] using rep
  | succ remaining ih =>
      have hdr : processed+2 ≤ hi.sqrt := by omega
      have hsquare : (processed+2)*(processed+2) ≤ hi := Nat.le_sqrt.mp hdr
      have hguard : processed+2 ≤ hi/(processed+2) :=
        (Nat.le_div_iff_mul_le (by omega : 0<processed+2)).mpr hsquare
      obtain ⟨body,hbody,henv,howned,hrep,hframe⟩ := divisor_body_exec
        (call:=call) (by omega : 0<processed+2) horder hsquare hhi owned rep env
      have hdhi : processed+2 ≤ hi := by nlinarith
      have hnextw : processed+2+1 < modulus := by norm_num [modulus]; omega
      let next : State := {body with env:=bind body.env "d" (.u64 (processed+2+1))}
      have increment : Eval call divisorIncrement body next (.u64 (processed+2+1)) := by
        simp [Eval,divisorIncrement,eval_increment,henv,env.dValue,Nat.mod_eq_of_lt hnextw,next]
      have envNext : DivisorEnv lo hi (processed+1+2) base next.env := by
        simpa [next,henv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using env.bind_d (processed+2+1)
      have repNext : FlagsRep next.heap base (hi-lo+1) (passes lo (processed+1)) := hrep
      obtain ⟨t,tail,htEnv,htOwned,htRep,htFrame⟩ := ih (s:=next) (processed:=processed+1)
        howned repNext envNext (by omega)
      refine ⟨t,?_,?_,htOwned,htRep,?_⟩
      · apply ForRun.next _ hbody increment tail
        have test := GuardRun.present (truth:=truth)
          (guard_eval (call:=call) env.hiValue env.dValue (by omega) hhw)
        simpa [truth,Value.bits,hguard] using test
      · simpa [next,henv,QuotientCMachine.bind,Function.update_idem] using htEnv
      · intro other j hother
        exact (htFrame other j hother).trans (hframe other j hother)

theorem divisor_for_exec {call : Service} {s : State} {lo hi base : Nat}
    (hlo : 2 ≤ lo) (horder : lo ≤ hi) (hhi : hi ≤ 2000000000000)
    (owned : Owned s.heap) (rep : FlagsRep s.heap base (hi-lo+1) (fun _=>1))
    (hloEnv : s.env "lo" = some (.u64 lo)) (hhiEnv : s.env "hi" = some (.u64 hi))
    (hflags : s.env "flags" = some (.ptr base))
    (freshD : s.env "d"=none) (freshFirst : s.env "first"=none) (freshM : s.env "m"=none) :
    ∃ t, Run call divisorFor s (.continuing t) ∧ t.env=s.env ∧ Owned t.heap ∧
      FlagsRep t.heap base (hi-lo+1) (finalFlags lo hi) ∧
      (∀ other j,other≠base→QuotientCMachine.read t.heap other j=QuotientCMachine.read s.heap other j) := by
  let first : State := {s with env:=bind s.env "d" (.u64 2)}
  have declaration : Declare call [⟨"uint64_t","d",some (.nat 2)⟩] s first :=
    declare_singleton_of (raw:=.i32 2) freshD
      ((pure_literal call s.heap s.env 7 2).trans (by norm_num [literal]))
      (by norm_num [uint64,Value.scalar,modulus])
  have envFirst : DivisorEnv lo hi 2 base first.env := by
    constructor <;> simp [first,QuotientCMachine.bind,hloEnv,hhiEnv,hflags,freshFirst,freshM]
  obtain ⟨inner,loop,henv,howned,hrep,hframe⟩ := divisors_remaining (hi.sqrt-1)
    (s:=first) (processed:=0) hlo horder hhi owned rep envFirst (by omega)
  let t := closeScope s inner
  refine ⟨t,StmtRun.forLoop (StmtRun.declare declaration) loop rfl,?_,howned,hrep,hframe⟩
  funext name
  by_cases hd : name="d"
  · subst name; simp [t,closeScope,freshD]
  · change (if (s.env name).isSome then inner.env name else none) = s.env name
    rw [henv]
    simp only [first,QuotientCMachine.bind,Function.update_of_ne hd]
    cases h : s.env name <;> rfl

#print axioms actual_divisor_for
#print axioms divisor_for_exec
end RamanujanPV.SegmentCDivisors
