/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCExecute

/-! Complete actual descending small-table while-loop. The mathematical sieve
invariant proves both source underflow guards; no successful-output or guard
premise is substituted for the loop's mathematical correctness. -/
namespace RamanujanPV.QuotientCSmallLoop
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open QuotientCMachine QuotientCExecute QuotientTables QuotientSieve
set_option autoImplicit false
set_option maxHeartbeats 2000000

def smallGuard : Expr := .binary "<=" (.var "square") (.var "v")
def smallWhile : Stmt := .whileLoop smallGuard smallBody

private def sequenceAt : Stmt → Nat → Option Stmt
  | .sequence body, i => body[i]?
  | _, _ => none

def actualSmallWhile : Option Stmt := do
  let .forLoop _ _ _ (.branch _ _ active) ←
    sequenceAt QuotientCSourceV2.countFunction.body 5 | none
  let .branch _ yes _ ← sequenceAt active 5 | none
  sequenceAt yes 1

theorem actual_small_while : actualSmallWhile = some smallWhile := rfl

lemma guard_eval {call : Service} {s : State} {square v : Nat}
    (hs : s.env "square" = some (.u64 square))
    (hv : s.env "v" = some (.u64 v)) :
    Eval call smallGuard s s (.i32 (if square ≤ v then 1 else 0)) :=
  eval_le_of ((pure_var call s.heap s.env 6 "square").trans hs)
    ((pure_var call s.heap s.env 6 "v").trans hv)

lemma stage_guards {N r p v before : Nat} {T : Tables}
    (hp : Nat.Prime p) (hsq : p*p ≤ v) (hvr : v ≤ r)
    (hbefore : before = total p (p-1)) (stage : SmallStage N r p v T) :
    1 ≤ v ∧ 1 ≤ v/p ∧ v/p ≤ r ∧
      before ≤ T.small (v/p) ∧ T.small (v/p)-before ≤ T.small v := by
  have hp2 := hp.two_le
  have hv1 : 1 ≤ v := by nlinarith
  have hq1 : 1 ≤ v/p := (Nat.le_div_iff_mul_le hp.pos).mpr (by nlinarith)
  have hqr : v/p ≤ r := (Nat.div_le_self v p).trans hvr
  have hread : T.small (v/p) = total p (v/p) := by
    rw [stage.2 (v/p) hq1 hqr, if_neg (by have h := Nat.div_le_self v p; omega)]
  have hwrite : T.small v = total p v := by rw [stage.2 v hv1 hvr, if_neg (by omega)]
  have guards := QuotientWordBounds.subtraction_guards hp hsq
  rw [hread, hwrite, hbefore]
  exact ⟨hv1, hq1, hqr, guards⟩

theorem run_remaining (remaining : Nat) {call : Service} {s : State}
    {sb lb N r p before processed : Nat} {T0 : Tables}
    (hp : Nat.Prime p) (hpr : p ≤ r) (hroot : r*r ≤ N) (hN : N ≤ 2000000000000)
    (hbefore : before = total p (p-1)) (initialStage : SmallStage N r p r T0)
    (owned : Owned s.heap)
    (rep : HeapRep s.heap sb lb r (smallLoop p before r processed T0))
    (hsmall : s.env "small" = some (.ptr sb))
    (hvalue : s.env "v" = some (.u64 (r-processed)))
    (hprime : s.env "p" = some (.u64 p))
    (hbeforeEnv : s.env "before" = some (.u64 before))
    (hsquare : s.env "square" = some (.u64 (p*p)))
    (hfresh : s.env "sub" = none)
    (hcount : processed+remaining = smallCount r p) :
    ∃ t, WhileRun call smallGuard smallBody s (.continuing t) ∧
      t.env = bind s.env "v" (.u64 (r-smallCount r p)) ∧ Owned t.heap ∧
      HeapRep t.heap sb lb r (smallLoop p before r (smallCount r p) T0) := by
  have hp2 := hp.two_le
  have hrN : r ≤ N := by nlinarith
  have hrw : r < modulus := by norm_num [modulus]; omega
  induction remaining generalizing s processed with
  | zero =>
      have hprocessed : processed = smallCount r p := by omega
      have hstop : ¬p*p ≤ r-processed := by
        have hsqpos : 0 < p*p := Nat.mul_pos hp.pos hp.pos
        unfold smallCount at hprocessed
        omega
      refine ⟨s, ?_, ?_, owned, ?_⟩
      · apply WhileRun.done (guard_eval hsquare hvalue)
        simp [truth, Value.bits, hstop]
      · rw [← hprocessed]
        symm
        funext name
        by_cases h : name = "v"
        · subst name; simp [QuotientCMachine.bind, hvalue]
        · simp [QuotientCMachine.bind, Function.update_of_ne h]
      · simpa [hprocessed] using rep
  | succ remaining ih =>
      have hk : processed ≤ smallCount r p := by omega
      have hsq : p*p ≤ r-processed := by unfold smallCount at hcount; omega
      have hvr : r-processed ≤ r := Nat.sub_le _ _
      have stage := smallLoop_stage hp hbefore initialStage processed hk
      obtain ⟨hv1,hq1,hqr,hguard1,hguard2⟩ := stage_guards hp hsq hvr hbefore stage
      have hvw : r-processed < modulus := hvr.trans_lt hrw
      obtain ⟨body,hbody,henv,howned,hrep⟩ := small_body_exec owned rep hv1 hvr hp.pos hvw
        hq1 hqr hsmall hvalue hprime hbeforeEnv hfresh hguard1 hguard2
      have hnew : r-processed-1 = r-(processed+1) := by omega
      have hnextRep : HeapRep body.heap sb lb r (smallLoop p before r (processed+1) T0) :=
        hrep
      obtain ⟨t,htail,ht,htowned,htrep⟩ := ih (s := body) (processed := processed+1)
        howned hnextRep
        (by simp [henv,QuotientCMachine.bind,hsmall])
        (by simpa [henv,QuotientCMachine.bind,hnew])
        (by simp [henv,QuotientCMachine.bind,hprime])
        (by simp [henv,QuotientCMachine.bind,hbeforeEnv])
        (by simp [henv,QuotientCMachine.bind,hsquare])
        (by simp [henv,QuotientCMachine.bind,hfresh]) (by omega)
      refine ⟨t, WhileRun.next (guard_eval hsquare hvalue) ?_ hbody htail, ?_, htowned, htrep⟩
      · simp [truth,Value.bits,hsq]
      · simpa [henv,QuotientCMachine.bind,Function.update_idem] using ht

/-- Actual source while-loop, including the zero-iteration case p²>r. The
functional smallLoop uses exactly the same descending in-place write order. -/
theorem small_while_exec {call : Service} {s : State} {sb lb N r p before : Nat} {T : Tables}
    (hp : Nat.Prime p) (hpr : p ≤ r) (hroot : r*r ≤ N) (hN : N ≤ 2000000000000)
    (hbefore : before = total p (p-1)) (initialStage : SmallStage N r p r T)
    (owned : Owned s.heap) (rep : HeapRep s.heap sb lb r T)
    (hsmall : s.env "small" = some (.ptr sb))
    (hvalue : s.env "v" = some (.u64 r))
    (hprime : s.env "p" = some (.u64 p))
    (hbeforeEnv : s.env "before" = some (.u64 before))
    (hsquare : s.env "square" = some (.u64 (p*p)))
    (hfresh : s.env "sub" = none) :
    ∃ t, Run call smallWhile s (.continuing t) ∧
      t.env = bind s.env "v" (.u64 (r-smallCount r p)) ∧ Owned t.heap ∧
      HeapRep t.heap sb lb r (smallLoop p before r (smallCount r p) T) ∧
      Invariant N r (p+1) (smallLoop p before r (smallCount r p) T) := by
  obtain ⟨t,hrun,henv,howned,hrep⟩ := run_remaining (smallCount r p)
    (processed := 0) hp hpr hroot hN hbefore initialStage owned rep hsmall
    (by simpa using hvalue) hprime hbeforeEnv hsquare hfresh (by omega)
  exact ⟨t, StmtRun.whileLoop hrun, henv, howned, hrep,
    smallLoop_complete hp hbefore initialStage⟩

theorem final_value_when_active {r p : Nat} (hactive : p*p ≤ r) (hp : 0 < p) :
    r-smallCount r p = p*p-1 := by
  have : 0 < p*p := Nat.mul_pos hp hp
  unfold smallCount
  omega

#print axioms actual_small_while
#print axioms stage_guards
#print axioms small_while_exec
end RamanujanPV.QuotientCSmallLoop
