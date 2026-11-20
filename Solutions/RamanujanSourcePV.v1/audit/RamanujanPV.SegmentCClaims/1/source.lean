/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.SegmentMemory
import RamanujanPV.SegmentCInit

/-! The actual source claims comparison and counting loop. Matching input is
only a branch condition; the rejection theorem handles its negation. -/
namespace RamanujanPV.SegmentCClaims
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops QuotientCMachine SegmentMemory
set_option autoImplicit false
set_option maxHeartbeats 0

def prefixSum (F : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i+1 => prefixSum F i + F i

lemma prefixSum_eq_sum (F : Nat → Nat) (i : Nat) :
    prefixSum F i = ∑ j ∈ Finset.range i, F j := by
  induction i with
  | zero => simp [prefixSum]
  | succ i ih => simp [prefixSum, Finset.sum_range_succ, ih]

lemma prefixSum_bound {F : Nat → Nat} {length : Nat}
    (bits : ∀ j, j < length → F j ≤ 1) :
    ∀ i, i ≤ length → prefixSum F i ≤ i := by
  intro i
  induction i with
  | zero => intro _; simp [prefixSum]
  | succ i ih =>
    intro hi
    have hp := ih (by omega)
    have hb := bits i (by omega)
    simp only [prefixSum]
    omega

def test : Expr := .binary "==" (.index (.var "claims") (.var "i"))
  (.index (.var "flags") (.var "i"))
def testStmt : Stmt := .branch test .skip (.returnStmt (.nat 0))
def addExpr : Expr := .binary "+" (.var "count") (.index (.var "flags") (.var "i"))
def addStmt : Stmt := .eval (.binary "=" (.var "count") addExpr)
def body : Stmt := .sequence [testStmt, addStmt]
def claimsFor : Stmt := .forLoop SegmentCInit.initDeclaration
  (some SegmentCInit.initGuard) SegmentCInit.initIncrement body

def actualClaims : Option Stmt := match SegmentCheckerSource.checkerFunction.body with
  | .sequence source => source[8]?
  | _ => none

theorem actual_claims : actualClaims = some claimsFor := rfl

lemma index_pure {call : Service} {heap : Heap} {env : Env} {name : String}
    {base i word : Nat} (fuel : Nat)
    (ha : env name = some (.ptr base)) (hi : env "i" = some (.u64 i))
    (hr : QuotientCMachine.read heap base i = some (.u64 word)) :
    evalPure call heap env (fuel+2) (.index (.var name) (.var "i")) = some (.u64 word) := by
  apply pure_index_of
  · simpa only [pure_var] using ha
  · simpa only [pure_var] using hi
  · exact hr

lemma test_eval {call : Service} {s : State} {cb fb length i : Nat} {C F : Nat → Nat}
    (rc : FlagsRep s.heap cb length C) (rf : FlagsRep s.heap fb length F)
    (hc : s.env "claims" = some (.ptr cb)) (hf : s.env "flags" = some (.ptr fb))
    (hi : s.env "i" = some (.u64 i)) (hil : i < length) :
    Eval call test s s (.i32 (if C i = F i then 1 else 0)) := by
  have hp : evalPure call s.heap s.env 8 test = some (.i32 (if C i = F i then 1 else 0)) := by
    apply pure_binary_of
    · exact index_pure 5 hc hi (rc i hil)
    · exact index_pure 5 hf hi (rf i hil)
    · simp [binary, Value.scalar]
  change (do let value ← evalPure call s.heap s.env 8 test; pure (s, value)) = _
  rw [hp]
  rfl

lemma closeScope_count {s : State} {old value : Nat}
    (hc : s.env "count" = some (.u64 old)) :
    closeScope s {s with env := QuotientCMachine.bind s.env "count" (.u64 value)} =
      {s with env := QuotientCMachine.bind s.env "count" (.u64 value)} := by
  rcases s with ⟨env, heap⟩
  apply congrArg (fun e : Env => ({env:=e, heap:=heap} : State))
  funext name
  by_cases h : name = "count"
  · subst name
    simp [closeScope, QuotientCMachine.bind, hc]
  · simp only [closeScope, QuotientCMachine.bind, Function.update_of_ne h]
    cases he : env name <;> rfl

theorem body_pass {call : Service} {s : State} {cb fb length i : Nat} {C F : Nat → Nat}
    (rc : FlagsRep s.heap cb length C) (rf : FlagsRep s.heap fb length F)
    (hc : s.env "claims" = some (.ptr cb)) (hf : s.env "flags" = some (.ptr fb))
    (hi : s.env "i" = some (.u64 i)) (hcount : s.env "count" = some (.u64 (prefixSum F i)))
    (hil : i < length) (hword : length < modulus)
    (bits : ∀ j, j < length → F j ≤ 1) (same : C i = F i) :
    Run call body s (.continuing
      {s with env := QuotientCMachine.bind s.env "count" (.u64 (prefixSum F (i+1)))}) := by
  have hsum : prefixSum F i + F i < modulus := by
    have hp := prefixSum_bound bits (i+1) (by omega)
    simpa only [prefixSum] using hp.trans_lt (by omega : i+1 < modulus)
  have hplus : evalPure call s.heap s.env 8 addExpr = some (.u64 (prefixSum F (i+1))) := by
    apply pure_binary_of
    · simpa only [pure_var] using hcount
    · exact index_pure 5 hf hi (rf i hil)
    · exact binary_u64_add hsum
  have hassign := eval_variable_assign_of hcount hplus (uint64_of_u64 (by simpa only [prefixSum] using hsum))
  have htest : Run call testStmt s (.continuing s) := by
    apply StmtRun.branch (test_eval rc rf hc hf hi hil)
    simpa [truth, Value.bits, same] using (StmtRun.skip s)
  apply StmtRun.sequence
  · exact SeqRun.next htest (SeqRun.next (StmtRun.evaluate hassign) (SeqRun.nil _))
  · change _ = .continuing (closeScope s _)
    rw [closeScope_count hcount]

theorem body_reject {call : Service} {s : State} {cb fb length i : Nat} {C F : Nat → Nat}
    (rc : FlagsRep s.heap cb length C) (rf : FlagsRep s.heap fb length F)
    (hc : s.env "claims" = some (.ptr cb)) (hf : s.env "flags" = some (.ptr fb))
    (hi : s.env "i" = some (.u64 i)) (hil : i < length) (different : C i ≠ F i) :
    Run call body s (.returned s (.i32 0)) := by
  have hzero : Eval call (.nat 0) s s (.i32 0) := by simp [Eval, eval, pure_literal, literal]
  have htest : Run call testStmt s (.returned s (.i32 0)) := by
    apply StmtRun.branch (test_eval rc rf hc hf hi hil)
    simpa [truth, Value.bits, different] using (StmtRun.returnValue hzero)
  apply StmtRun.sequence
  · exact SeqRun.returned htest
  · change _ = .returned (closeScope s s) (.i32 0)
    rw [QuotientCInit.closeScope_same_env rfl]

theorem pass_remaining (k : Nat) {call : Service} {s : State} {cb fb length i : Nat} {C F : Nat → Nat}
    (rc : FlagsRep s.heap cb length C) (rf : FlagsRep s.heap fb length F)
    (hc : s.env "claims" = some (.ptr cb)) (hf : s.env "flags" = some (.ptr fb))
    (hi : s.env "i" = some (.u64 i)) (hcount : s.env "count" = some (.u64 (prefixSum F i)))
    (hlen : s.env "length" = some (.u64 length)) (hword : length < modulus)
    (bits : ∀ j, j < length → F j ≤ 1) (same : ∀ j, j < length → C j = F j)
    (remaining : i+k = length) :
    ∃ t, ForRun call (some SegmentCInit.initGuard) SegmentCInit.initIncrement body s (.continuing t) ∧
      t.heap = s.heap ∧ t.env = QuotientCMachine.bind
        (QuotientCMachine.bind s.env "count" (.u64 (prefixSum F length))) "i" (.u64 length) := by
  induction k generalizing s i with
  | zero =>
    have hieq : i=length := by omega
    refine ⟨s, ?_, rfl, ?_⟩
    · apply ForRun.done
      have hg := GuardRun.present (truth:=truth) (SegmentCInit.guard_eval (call:=call) hi hlen)
      simpa [truth, Value.bits, show ¬i<length by omega] using hg
    · funext name
      by_cases hI : name="i"
      · subst name; simp [QuotientCMachine.bind,hi,hieq]
      · by_cases hC : name="count"
        · subst name; simp [QuotientCMachine.bind,hcount,hieq]
        · simp [QuotientCMachine.bind, Function.update_of_ne hI, Function.update_of_ne hC]
  | succ k ih =>
    have hil : i<length := by omega
    let after : State := {s with env:=QuotientCMachine.bind s.env "count" (.u64 (prefixSum F (i+1)))}
    have hb : Run call body s (.continuing after) := body_pass rc rf hc hf hi hcount hil hword bits (same i hil)
    let step : State := {after with env:=QuotientCMachine.bind after.env "i" (.u64 (i+1))}
    have hstep : Eval call SegmentCInit.initIncrement after step (.u64 (i+1)) :=
      SegmentCInit.increment_eval (by simp [after,QuotientCMachine.bind,hi]) (by omega)
    obtain ⟨t,ht,hheap,henv⟩ := ih (s:=step) (i:=i+1) rc rf
      (by simp [step,after,QuotientCMachine.bind,hc]) (by simp [step,after,QuotientCMachine.bind,hf])
      (by simp [step,QuotientCMachine.bind]) (by simp [step,after,QuotientCMachine.bind])
      (by simp [step,after,QuotientCMachine.bind,hlen]) (by omega)
    refine ⟨t, ?_, hheap, ?_⟩
    · apply ForRun.next _ hb hstep ht
      have hg := GuardRun.present (truth:=truth) (SegmentCInit.guard_eval (call:=call) hi hlen)
      simpa [truth,Value.bits,hil] using hg
    · rw [henv]
      funext name
      by_cases hI : name="i"
      · subst name; simp [step,after,QuotientCMachine.bind]
      · by_cases hC : name="count"
        · subst name; simp [step,after,QuotientCMachine.bind]
        · simp [step,after,QuotientCMachine.bind,Function.update_of_ne hI,Function.update_of_ne hC]

theorem matching_loop {call : Service} {s : State} {cb fb length : Nat} {C F : Nat → Nat}
    (rc : FlagsRep s.heap cb length C) (rf : FlagsRep s.heap fb length F)
    (hc : s.env "claims" = some (.ptr cb)) (hf : s.env "flags" = some (.ptr fb))
    (hcount : s.env "count" = some (.u64 0)) (hlen : s.env "length" = some (.u64 length))
    (fresh : s.env "i" = none) (hword : length < modulus)
    (bits : ∀ j, j < length → F j ≤ 1) (same : ∀ j, j < length → C j=F j) :
    ∃ t, Run call claimsFor s (.continuing t) ∧ t.heap=s.heap ∧
      t.env=QuotientCMachine.bind s.env "count" (.u64 (prefixSum F length)) := by
  let first : State := {s with env:=QuotientCMachine.bind s.env "i" (.u64 0)}
  have hd : Run call SegmentCInit.initDeclaration s (.continuing first) := by
    apply StmtRun.declare
    simp [Declare,declare_singleton,fresh,pure_literal,literal,uint64,Value.scalar,modulus,first]
  obtain ⟨last,hl,hh,he⟩ := pass_remaining length (s:=first) (i:=0) rc rf
    (by simp [first,QuotientCMachine.bind,hc]) (by simp [first,QuotientCMachine.bind,hf])
    (by simp [first,QuotientCMachine.bind]) (by simp [first,QuotientCMachine.bind,hcount,prefixSum])
    (by simp [first,QuotientCMachine.bind,hlen]) hword bits same (by omega)
  refine ⟨closeScope s last, StmtRun.forLoop hd hl rfl, hh, ?_⟩
  funext name
  by_cases hI : name="i"
  · subst name; simp [closeScope,fresh,QuotientCMachine.bind]
  · by_cases hC : name="count"
    · subst name; simp [closeScope,hcount,he,first,QuotientCMachine.bind]
    · change (if (s.env name).isSome then last.env name else none)=_
      rw [he]
      simp only [first,QuotientCMachine.bind,Function.update_of_ne hI,Function.update_of_ne hC]
      cases hn : s.env name <;> rfl

#print axioms actual_claims
#print axioms prefixSum_eq_sum
#print axioms body_pass
#print axioms body_reject
#print axioms matching_loop
end RamanujanPV.SegmentCClaims
