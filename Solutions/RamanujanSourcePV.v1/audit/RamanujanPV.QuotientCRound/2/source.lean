/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCLarge
import RamanujanPV.QuotientCSmallLoop
import RamanujanPV.QuotientCInit

/-! Complete actual source body of one outer quotient-sieve round. Adjacent
table counts prove the primality branch; the two source inner loops have their
actual execution and arithmetic guards already proved. -/
namespace RamanujanPV.QuotientCRound
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open QuotientCMachine QuotientCExecute QuotientTables QuotientSieve
set_option autoImplicit false
set_option maxHeartbeats 4000000

structure RoundEnv (sb lb N r p : Nat) (env : Env) : Prop where
  n : env "n" = some (.u64 N)
  rValue : env "r" = some (.u64 r)
  pValue : env "p" = some (.u64 p)
  small : env "small" = some (.ptr sb)
  large : env "large" = some (.ptr lb)
  beforeFresh : env "before" = none
  stopFresh : env "stop" = none
  squareFresh : env "square" = none
  iFresh : env "i" = none
  vFresh : env "v" = none
  ipFresh : env "ip" = none
  subFresh : env "sub" = none

lemma RoundEnv.bind_p {sb lb N r p : Nat} {env : Env}
    (h : RoundEnv sb lb N r p env) (next : Nat) :
    RoundEnv sb lb N r next (bind env "p" (.u64 next)) := by
  exact {
    n := by simpa using h.n
    rValue := by simpa using h.rValue
    pValue := by simp
    small := by simpa using h.small
    large := by simpa using h.large
    beforeFresh := by simpa using h.beforeFresh
    stopFresh := by simpa using h.stopFresh
    squareFresh := by simpa using h.squareFresh
    iFresh := by simpa using h.iFresh
    vFresh := by simpa using h.vFresh
    ipFresh := by simpa using h.ipFresh
    subFresh := by simpa using h.subFresh }

def squareExpr : Expr := .binary "*" (.var "p") (.var "p")
def quotientExpr : Expr := .binary "/" (.var "n") squareExpr
def previousExpr : Expr := .index (.var "small") (.binary "-" (.var "p") (.nat 1))
def detectionGuard : Expr := .binary "==" (.index (.var "small") (.var "p")) previousExpr
def stopGuard : Expr := .binary "<" quotientExpr (.var "r")
def stopAssign : Expr := .binary "=" (.var "stop") quotientExpr
def stopBranch : Stmt := .branch stopGuard (.eval stopAssign) .skip
def activeBody : Stmt := .sequence [
  .declare [⟨"uint64_t", "before", some previousExpr⟩],
  .declare [⟨"uint64_t", "stop", some (.var "r")⟩],
  stopBranch, QuotientCLarge.largeFor,
  .declare [⟨"uint64_t", "square", some squareExpr⟩],
  QuotientCSmallLoop.smallBranch]
def roundBody : Stmt := .branch detectionGuard .skip activeBody

def actualRoundBody : Option Stmt := do
  let .sequence body := QuotientCSourceV2.countFunction.body | none
  let .forLoop _ _ _ outer ← body[5]? | none
  pure outer

theorem actual_round_body : actualRoundBody = some roundBody := rfl

lemma pure_square (k : Nat) {call : Service} {heap : Heap} {env : Env} {p : Nat}
    (hp : env "p" = some (.u64 p)) (hpp : p*p < modulus) :
    evalPure call heap env (k+2) squareExpr = some (.u64 (p*p)) :=
  pure_binary_of ((pure_var call heap env k "p").trans hp)
    ((pure_var call heap env k "p").trans hp) (binary_u64_mul hpp)

lemma pure_quotient (k : Nat) {call : Service} {heap : Heap} {env : Env} {N p : Nat}
    (hn : env "n" = some (.u64 N)) (hp : env "p" = some (.u64 p))
    (hpp : p*p < modulus) (hp0 : 0 < p) (hNw : N < modulus) :
    evalPure call heap env (k+3) quotientExpr = some (.u64 (N/(p*p))) :=
  pure_binary_of ((pure_var call heap env (k+1) "n").trans hn)
    (pure_square k hp hpp) (binary_u64_div (Nat.mul_pos hp0 hp0) hNw)

lemma pure_previous (k : Nat) {call : Service} {heap : Heap} {env : Env}
    {sb p old : Nat} (ha : env "small" = some (.ptr sb))
    (hp : env "p" = some (.u64 p)) (hp1 : 1 ≤ p) (hpw : p < modulus)
    (hr : QuotientCMachine.read heap sb (p-1) = some (.u64 old)) :
    evalPure call heap env (k+3) previousExpr = some (.u64 old) :=
  pure_index_of ((pure_var call heap env (k+1) "small").trans ha)
    (pure_binary_of ((pure_var call heap env k "p").trans hp)
      ((pure_literal call heap env k 1).trans QuotientCInit.literal_one)
      (QuotientCInit.sub_literal_one hp1 hpw)) hr

lemma detection_eval {call : Service} {s : State} {sb lb r p : Nat} {T : Tables}
    (rep : HeapRep s.heap sb lb r T) (hp2 : 2 ≤ p) (hpr : p ≤ r) (hpw : p < modulus)
    (ha : s.env "small" = some (.ptr sb)) (hp : s.env "p" = some (.u64 p)) :
    Eval call detectionGuard s s (.i32 (if T.small p = T.small (p-1) then 1 else 0)) := by
  have hpRead : evalPure call s.heap s.env 7 (.index (.var "small") (.var "p")) =
      some (.u64 (T.small p)) :=
    pure_index_of ((pure_var call s.heap s.env 5 "small").trans ha)
      ((pure_var call s.heap s.env 5 "p").trans hp) (rep.2.1 p (by omega) hpr)
  have hmRead := pure_previous (call := call) 4 ha hp (by omega : 1 ≤ p) hpw
    (rep.2.1 (p-1) (by omega) (by omega))
  have hbinary : binary "==" (.u64 (T.small p)) (.u64 (T.small (p-1))) =
      some (.i32 (if T.small p = T.small (p-1) then 1 else 0)) := by
    simp [binary,Value.scalar]
  have hresult := pure_binary_of hpRead hmRead hbinary
  unfold Eval
  change (do return (s, ← evalPure call s.heap s.env 8 detectionGuard)) = _
  rw [hresult]
  rfl

lemma stop_branch_exec {call : Service} {s : State} {N r p : Nat}
    (hn : s.env "n" = some (.u64 N)) (hp : s.env "p" = some (.u64 p))
    (hr : s.env "r" = some (.u64 r)) (hstop : s.env "stop" = some (.u64 r))
    (hpp : p*p < modulus) (hp0 : 0 < p) (hNw : N < modulus) :
    ∃ t, Run call stopBranch s (.continuing t) ∧
      t.env = bind s.env "stop" (.u64 (largeStop N r p)) ∧ t.heap = s.heap := by
  have hg : Eval call stopGuard s s (.i32 (if N/(p*p) < r then 1 else 0)) :=
    eval_lt_of (pure_quotient 4 hn hp hpp hp0 hNw)
      ((pure_var call s.heap s.env 6 "r").trans hr)
  by_cases hless : N/(p*p) < r
  · let t : State := {s with env := bind s.env "stop" (.u64 (N/(p*p)))}
    have he : Eval call stopAssign s t (.u64 (N/(p*p))) :=
      eval_variable_assign_of hstop (pure_quotient 5 hn hp hpp hp0 hNw)
        (uint64_of_u64 ((Nat.div_le_self N (p*p)).trans_lt hNw))
    refine ⟨t, ?_, ?_, rfl⟩
    · apply StmtRun.branch hg
      simpa [truth,Value.bits,hless] using StmtRun.evaluate he
    · simp only [t,largeStop,min_eq_right hless.le]
  · refine ⟨s, ?_, ?_, rfl⟩
    · apply StmtRun.branch hg
      simpa [truth,Value.bits,hless] using StmtRun.skip (Eval := Eval call)
        (Declare := Declare call) (truth := truth) (Scope := Scope) s
    · have hmin : largeStop N r p = r := min_eq_left (by omega)
      rw [hmin]
      symm
      funext name
      by_cases h : name = "stop"
      · subst name; simp [QuotientCMachine.bind,hstop]
      · simp [QuotientCMachine.bind,Function.update_of_ne h]

theorem active_exec {call : Service} {s : State} {sb lb N r p : Nat} {T : Tables}
    (hN : N ≤ 2000000000000) (hr : r = N.sqrt) (hp : Nat.Prime p) (hpr : p ≤ r)
    (hinit : Invariant N r p T) (owned : Owned s.heap) (rep : HeapRep s.heap sb lb r T)
    (env : RoundEnv sb lb N r p s.env) :
    ∃ t, Run call activeBody s (.continuing t) ∧ t.env = s.env ∧ Owned t.heap ∧
      HeapRep t.heap sb lb r
        (smallLoop p (T.small (p-1)) r (smallCount r p)
          (largeLoop N r p (T.small (p-1)) (largeStop N r p) T)) := by
  have hp2 := hp.two_le
  have hroot : r*r ≤ N := by simpa [hr] using Nat.sqrt_le N
  have hrootHi : N < (r+1)*(r+1) := by simpa [hr,Nat.succ_eq_add_one] using Nat.lt_succ_sqrt N
  have hrN : r ≤ N := by nlinarith
  have hNw : N < modulus := by norm_num [modulus]; omega
  have hrw : r < modulus := hrN.trans_lt hNw
  have hpw : p < modulus := hpr.trans_lt hrw
  have hpp : p*p < modulus := ((Nat.mul_le_mul hpr hpr).trans hroot).trans_lt hNw
  let before := T.small (p-1)
  have hb : before = total p (p-1) := hinit.1 (p-1) (by omega) (by omega)
  have hmRead := rep.2.1 (p-1) (by omega) (by omega)
  obtain ⟨block,hblock,halign,hindex,haddress,hvalue,hbw⟩ := read_some_details hmRead
  let s1 : State := {s with env := bind s.env "before" (.u64 before)}
  let s2 : State := {s1 with env := bind s1.env "stop" (.u64 r)}
  have hd1 : Declare call [⟨"uint64_t","before",some previousExpr⟩] s s1 :=
    declare_singleton_of env.beforeFresh (pure_previous 5 env.small env.pValue (by omega) hpw hmRead)
      (uint64_of_u64 hbw)
  have hd2 : Declare call [⟨"uint64_t","stop",some (.var "r")⟩] s1 s2 :=
    declare_singleton_of (by simp [s1,env.stopFresh])
      ((pure_var call s1.heap s1.env 8 "r").trans (by simpa [s1] using env.rValue))
      (uint64_of_u64 hrw)
  obtain ⟨s3,hstop,he3,hh3⟩ := stop_branch_exec (s := s2)
    (by simpa [s2,s1] using env.n) (by simpa [s2,s1] using env.pValue)
    (by simpa [s2,s1] using env.rValue) (by simp [s2]) hpp hp.pos hNw
  have largeEnv : QuotientCLarge.LoopEnv sb lb N r p before (largeStop N r p) s3.env := by
    constructor <;> simp [he3,s2,s1,QuotientCMachine.bind,env.n,env.rValue,env.pValue,
      env.small,env.large,env.ipFresh,env.subFresh]
  obtain ⟨s4,hlarge,he4,hown4,hrep4⟩ := QuotientCLarge.large_for_exec hN hr hp hpr hb hinit
    (by simpa [hh3,s2,s1] using owned) (by simpa [hh3,s2,s1] using rep) largeEnv
    (by simp [he3,s2,s1,QuotientCMachine.bind,env.iFresh])
  let s5 : State := {s4 with env := bind s4.env "square" (.u64 (p*p))}
  have hd5 : Declare call [⟨"uint64_t","square",some squareExpr⟩] s4 s5 :=
    declare_singleton_of (by simp [he4,he3,s2,s1,QuotientCMachine.bind,env.squareFresh])
      (pure_square 6 (by simpa [he4] using largeEnv.pValue) hpp) (uint64_of_u64 hpp)
  have stage := smallStage_initial hp hrootHi hb hinit
  obtain ⟨s6,hsmall,he6,hown6,hrep6,hinv6⟩ := QuotientCSmallLoop.small_branch_exec
    (s := s5) hp hpr hroot hN hb stage hown4 hrep4
    (by simpa [s5,he4] using largeEnv.small)
    (by simpa [s5,he4] using largeEnv.rValue)
    (by simpa [s5,he4] using largeEnv.pValue)
    (by simpa [s5,he4] using largeEnv.beforeValue)
    (by simp [s5])
    (by simp [s5,he4,he3,s2,s1,QuotientCMachine.bind,env.vFresh])
    (by simpa [s5,he4] using largeEnv.subFresh)
  let t := closeScope s s6
  have henv : t.env = s.env := by
    funext name
    simp only [t,closeScope,he6,s5,he4,he3,s2,s1]
    by_cases hsquare : name = "square"
    · subst name; simp [env.squareFresh]
    · by_cases hstop : name = "stop"
      · subst name; simp [env.stopFresh]
      · by_cases hbefore : name = "before"
        · subst name; simp [env.beforeFresh]
        · simp only [QuotientCMachine.bind,Function.update_of_ne hsquare,
            Function.update_of_ne hstop,Function.update_of_ne hbefore]
          cases h : s.env name <;> simp [h]
  refine ⟨t, ?_, henv, hown6, hrep6⟩
  apply StmtRun.sequence (inner := .continuing s6)
  · exact SeqRun.next (StmtRun.declare hd1)
      (SeqRun.next (StmtRun.declare hd2)
      (SeqRun.next hstop (SeqRun.next hlarge
      (SeqRun.next (StmtRun.declare hd5) (SeqRun.next hsmall (SeqRun.nil s6))))))
  · rfl

theorem round_exec {call : Service} {s : State} {sb lb N r p : Nat} {T : Tables}
    (hN : N ≤ 2000000000000) (hr : r = N.sqrt) (hp2 : 2 ≤ p) (hpr : p ≤ r)
    (hinit : Invariant N r p T) (owned : Owned s.heap) (rep : HeapRep s.heap sb lb r T)
    (env : RoundEnv sb lb N r p s.env) :
    ∃ t, Run call roundBody s (.continuing t) ∧ t.env = s.env ∧ Owned t.heap ∧
      HeapRep t.heap sb lb r (primeRound N r p T) := by
  have hroot : r*r ≤ N := by simpa [hr] using Nat.sqrt_le N
  have hrN : r ≤ N := by nlinarith
  have hpw : p < modulus := by norm_num [modulus]; omega
  have hguard := detection_eval (call := call) rep hp2 hpr hpw env.small env.pValue
  by_cases same : T.small p = T.small (p-1)
  · refine ⟨s, ?_, rfl, owned, ?_⟩
    · apply StmtRun.branch hguard
      simpa [truth,Value.bits,same] using StmtRun.skip (Eval := Eval call)
        (Declare := Declare call) (truth := truth) (Scope := Scope) s
    · simpa only [primeRound,if_pos same] using rep
  · have hprime : Nat.Prime p := by
      apply (detected_iff_prime hp2).mp
      have hpv := hinit.1 p (by omega) hpr
      have hpm := hinit.1 (p-1) (by omega) (by omega)
      simpa only [← hpv,← hpm] using same
    obtain ⟨t,hrun,henv,howned,hrep⟩ := active_exec hN hr hprime hpr hinit owned rep env
    refine ⟨t, ?_, henv, howned, ?_⟩
    · apply StmtRun.branch hguard
      simpa [truth,Value.bits,same] using hrun
    · simpa only [primeRound,if_neg same] using hrep

#print axioms actual_round_body
#print axioms active_exec
#print axioms round_exec
end RamanujanPV.QuotientCRound
