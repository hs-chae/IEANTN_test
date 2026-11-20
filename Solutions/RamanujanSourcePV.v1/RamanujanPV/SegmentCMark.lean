/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.SegmentCheckerMath
import RamanujanPV.SegmentMemory

/-! Actual typed source execution of the segmented checker's stride loop.
All array writes and increments are tied to the byte-checked source subtree;
the divisibility sweep is proved from the actual finite progression of stores. -/
namespace RamanujanPV.SegmentCMark
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open QuotientCMachine SegmentCheckerMath SegmentMemory
set_option autoImplicit false
set_option maxHeartbeats 4000000

def markBody : Stmt := .eval (.binary "="
  (.index (.var "flags") (.binary "-" (.var "m") (.var "lo"))) (.nat 0))
def markGuard : Expr := .binary "<=" (.var "m") (.var "hi")
def markIncrement : Expr := .binary "=" (.var "m") (.binary "+" (.var "m") (.var "d"))
def markFor : Stmt := .forLoop (.declare [⟨"uint64_t","m",some (.var "first")⟩])
  (some markGuard) markIncrement markBody

def actualMarkFor : Option Stmt := do
  let .sequence all := SegmentCheckerSource.checkerFunction.body | none
  let .forLoop _ _ _ (.sequence inner) ← all[6]? | none
  inner[3]?

theorem actual_mark_for : actualMarkFor = some markFor := rfl

structure MarkEnv (lo hi d first base : Nat) (env : Env) : Prop where
  loValue : env "lo" = some (.u64 lo)
  hiValue : env "hi" = some (.u64 hi)
  dValue : env "d" = some (.u64 d)
  firstValue : env "first" = some (.u64 first)
  flagsValue : env "flags" = some (.ptr base)

lemma MarkEnv.bind_m {lo hi d first base : Nat} {env : Env}
    (h : MarkEnv lo hi d first base env) (value : Nat) :
    MarkEnv lo hi d first base (bind env "m" (.u64 value)) := by
  exact {
    loValue := by simpa using h.loValue
    hiValue := by simpa using h.hiValue
    dValue := by simpa using h.dValue
    firstValue := by simpa using h.firstValue
    flagsValue := by simpa using h.flagsValue }

theorem mark_body_exec {call : Service} {s : State} {base lo m length : Nat} {flags : Nat → Nat}
    (owned : Owned s.heap) (rep : FlagsRep s.heap base length flags)
    (hflags : s.env "flags" = some (.ptr base)) (hm : s.env "m" = some (.u64 m))
    (hlo : s.env "lo" = some (.u64 lo)) (hlower : lo ≤ m)
    (hindex : m-lo < length) (hword : m < modulus) :
    ∃ t, Run call markBody s (.continuing t) ∧ t.env = s.env ∧ Owned t.heap ∧
      FlagsRep t.heap base length (Function.update flags (m-lo) 0) ∧
      (∀ other j, other ≠ base → QuotientCMachine.read t.heap other j = QuotientCMachine.read s.heap other j) := by
  obtain ⟨after,written,ownedAfter,repAfter,shape,other⟩ :=
    write_flag owned rep hindex (by norm_num [modulus] : 0 < modulus)
  refine ⟨{s with heap:=after},?_,rfl,ownedAfter,repAfter,other⟩
  apply StmtRun.evaluate
  exact eval_index_store_of (raw := .i32 0) ((pure_var call s.heap s.env 7 "flags").trans hflags)
    (pure_binary_of ((pure_var call s.heap s.env 6 "m").trans hm)
      ((pure_var call s.heap s.env 6 "lo").trans hlo) (binary_u64_sub hlower hword))
    ((pure_literal call s.heap s.env 7 0).trans (by norm_num [literal]))
    (by norm_num [uint64,Value.scalar,modulus]) written

lemma guard_eval {call : Service} {s : State} {m hi : Nat}
    (hm : s.env "m" = some (.u64 m)) (hhi : s.env "hi" = some (.u64 hi)) :
    Eval call markGuard s s (.i32 (if m ≤ hi then 1 else 0)) :=
  eval_le_of ((pure_var call s.heap s.env 6 "m").trans hm)
    ((pure_var call s.heap s.env 6 "hi").trans hhi)

lemma increment_eval {call : Service} {s : State} {m d : Nat}
    (hm : s.env "m" = some (.u64 m)) (hd : s.env "d" = some (.u64 d))
    (hword : m+d < modulus) :
    Eval call markIncrement s {s with env:=bind s.env "m" (.u64 (m+d))} (.u64 (m+d)) :=
  eval_variable_assign_of hm
    (pure_binary_of ((pure_var call s.heap s.env 6 "m").trans hm)
      ((pure_var call s.heap s.env 6 "d").trans hd) (binary_u64_add hword))
    (uint64_of_u64 hword)

theorem mark_remaining (remaining : Nat) {call : Service} {s : State}
    {lo hi d base processed : Nat} {initialFlags : Nat → Nat}
    (hd : 0 < d) (hlo : lo ≤ hi) (hsquare : d*d ≤ hi) (hhi : hi ≤ 2000000000000)
    (owned : Owned s.heap)
    (rep : FlagsRep s.heap base (hi-lo+1)
      (erasePrefix lo (firstMultiple lo d) d processed initialFlags))
    (env : MarkEnv lo hi d (firstMultiple lo d) base s.env)
    (hm : s.env "m" = some (.u64 (firstMultiple lo d+processed*d)))
    (hcount : processed+remaining = markCount lo hi d) :
    ∃ t, ForRun call (some markGuard) markIncrement markBody s (.continuing t) ∧
      t.env = bind s.env "m" (.u64 (firstMultiple lo d+markCount lo hi d*d)) ∧ Owned t.heap ∧
      FlagsRep t.heap base (hi-lo+1)
        (erasePrefix lo (firstMultiple lo d) d (markCount lo hi d) initialFlags) ∧
      (∀ other j, other ≠ base → QuotientCMachine.read t.heap other j = QuotientCMachine.read s.heap other j) := by
  have hdhi : d ≤ hi := by nlinarith
  have hhw : hi < modulus := by norm_num [modulus]; omega
  induction remaining generalizing s processed with
  | zero =>
      have heq : processed = markCount lo hi d := by omega
      have hstop : ¬firstMultiple lo d+processed*d ≤ hi := by
        rw [heq]
        exact Nat.not_le.mpr (mark_end_gt hd)
      refine ⟨s,?_,?_,owned,?_,by simp⟩
      · apply ForRun.done
        have test := GuardRun.present (truth:=truth) (guard_eval (call:=call) hm env.hiValue)
        simpa [truth,Value.bits,hstop] using test
      · rw [←heq]
        symm
        funext name
        by_cases h : name="m"
        · subst name; simp [QuotientCMachine.bind,hm]
        · simp [QuotientCMachine.bind,Function.update_of_ne h]
      · simpa [heq] using rep
  | succ remaining ih =>
      have hp : processed < markCount lo hi d := by omega
      have hmhi := mark_member_upper hd hp
      have hmlow : lo ≤ firstMultiple lo d+processed*d :=
        (first_lower hd).1.trans (Nat.le_add_right _ _)
      have hindex : firstMultiple lo d+processed*d-lo < hi-lo+1 := by omega
      have hmw : firstMultiple lo d+processed*d < modulus := hmhi.trans_lt hhw
      obtain ⟨body,hbody,henv,howned,hrep,hframe⟩ :=
        mark_body_exec (call := call) owned rep env.flagsValue hm env.loValue hmlow hindex hmw
      have hnextw : firstMultiple lo d+processed*d+d < modulus := by norm_num [modulus]; omega
      let next : State := {body with env:=bind body.env "m" (.u64 (firstMultiple lo d+processed*d+d))}
      have step : Eval call markIncrement body next (.u64 (firstMultiple lo d+processed*d+d)) :=
        increment_eval (by simpa [henv] using hm) (by simpa [henv] using env.dValue) hnextw
      have repNext : FlagsRep next.heap base (hi-lo+1)
          (erasePrefix lo (firstMultiple lo d) d (processed+1) initialFlags) := hrep
      have envNext : MarkEnv lo hi d (firstMultiple lo d) base next.env := by
        simpa [next,henv] using env.bind_m (firstMultiple lo d+processed*d+d)
      have hmNext : next.env "m" = some (.u64 (firstMultiple lo d+(processed+1)*d)) := by
        simp [next,QuotientCMachine.bind,Nat.add_mul,Nat.add_assoc]
      obtain ⟨t,tail,htEnv,htOwned,htRep,htFrame⟩ := ih (s:=next) (processed:=processed+1)
        howned repNext envNext hmNext (by omega)
      refine ⟨t,?_,?_,htOwned,htRep,?_⟩
      · apply ForRun.next _ hbody step tail
        have test := GuardRun.present (truth:=truth) (guard_eval (call:=call) hm env.hiValue)
        simpa [truth,Value.bits,hmhi] using test
      · simpa [next,henv,QuotientCMachine.bind,Function.update_idem] using htEnv
      · intro other j hother
        exact (htFrame other j hother).trans (hframe other j hother)

/-- Complete actual source stride for-loop. The output sweep and all unaffected
arrays are proved; initial flags may hold any valid uint64 data. -/
theorem mark_for_exec {call : Service} {s : State} {lo hi d base : Nat} {flags : Nat → Nat}
    (hd : 0 < d) (hlo : lo ≤ hi) (hsquare : d*d ≤ hi) (hhi : hi ≤ 2000000000000)
    (owned : Owned s.heap) (rep : FlagsRep s.heap base (hi-lo+1) flags)
    (env : MarkEnv lo hi d (firstMultiple lo d) base s.env) (freshM : s.env "m" = none) :
    ∃ t, Run call markFor s (.continuing t) ∧ t.env = s.env ∧ Owned t.heap ∧
      FlagsRep t.heap base (hi-lo+1) (sweep lo d flags) ∧
      (∀ other j, other ≠ base → QuotientCMachine.read t.heap other j = QuotientCMachine.read s.heap other j) := by
  have hdhi : d ≤ hi := by nlinarith
  have hfirstw : firstMultiple lo d < modulus := by
    have h := first_upper hlo hsquare
    norm_num [modulus]
    omega
  let first : State := {s with env:=bind s.env "m" (.u64 (firstMultiple lo d))}
  have declaration : Declare call [⟨"uint64_t","m",some (.var "first")⟩] s first :=
    declare_singleton_of freshM ((pure_var call s.heap s.env 8 "first").trans env.firstValue)
      (uint64_of_u64 hfirstw)
  obtain ⟨inner,loop,henv,howned,hrep,hframe⟩ := mark_remaining (markCount lo hi d)
    (s:=first) (processed:=0) hd hlo hsquare hhi owned rep
    (by simpa [first] using env.bind_m (firstMultiple lo d))
    (by simp [first]) (by omega)
  let t := closeScope s inner
  refine ⟨t,StmtRun.forLoop (StmtRun.declare declaration) loop rfl,?_,howned,?_,hframe⟩
  · funext name
    by_cases h : name="m"
    · subst name; simp [t,closeScope,freshM]
    · change (if (s.env name).isSome then inner.env name else none) = s.env name
      rw [henv]
      simp only [first,QuotientCMachine.bind,Function.update_of_ne h]
      cases hvalue : s.env name <;> rfl
  · apply representation_ext hrep
    intro i hiIndex
    have hn : lo+i ≤ hi := by omega
    simpa using erased_segment_is_sweep hd (Nat.le_add_right lo i) hn flags

#print axioms actual_mark_for
#print axioms mark_for_exec
end RamanujanPV.SegmentCMark
