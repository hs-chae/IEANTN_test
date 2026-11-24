/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCMachine
import RamanujanPV.QuotientCSourceV2
import RamanujanPV.QuotientTables

/-! Execution of the actual quotient-counter initialization loop. Old table
contents are arbitrary. Only allocated block metadata and ownership are input;
all initialized values and their checked reads are established by actual stores.
This is one source-loop refinement, not a claim about a complete native run. -/
namespace RamanujanPV.QuotientCInit
open LCMSourcePV.Witness.C
open LCMSourcePV.ASTLoops
open QuotientCMachine QuotientTables
set_option autoImplicit false
set_option maxHeartbeats 4000000

def initBody : Stmt := .sequence [
  .eval (.binary "=" (.index (.var "small") (.var "i"))
    (.binary "-" (.var "i") (.nat 1))),
  .eval (.binary "=" (.index (.var "large") (.var "i"))
    (.binary "-" (.binary "/" (.var "n") (.var "i")) (.nat 1)))]

def initGuard : Expr := .binary "<=" (.var "i") (.var "r")
def initIncrement : Expr := .unary "++" (.var "i")
def initDeclaration : Stmt := .declare [⟨"uint64_t", "i", some (.nat 1)⟩]
def initFor : Stmt := .forLoop initDeclaration (some initGuard) initIncrement initBody

def actualInitFor : Option Stmt := match QuotientCSourceV2.countFunction.body with
  | .sequence body => body[4]?
  | _ => none

theorem actual_init_for : actualInitFor = some initFor := rfl

def Buffers (heap : Heap) (sb lb r : Nat) : Prop :=
  sb ≠ lb ∧ ∃ small large, heap sb = some small ∧ heap lb = some large ∧
    r < small.extent ∧ r < large.extent

def Prefix (heap : Heap) (sb lb N next : Nat) : Prop :=
  ∀ j, 1 ≤ j → j < next →
    QuotientCMachine.read heap sb j = some (.u64 (j-1)) ∧
    QuotientCMachine.read heap lb j = some (.u64 (N/j-1))

/-- Definitionally the existing CExecute.HeapRep of Tables.initial N. Keeping
the identical read contract here avoids importing unrelated subtraction-store
proofs into the initialization loop's own source closure. -/
def InitialRep (heap : Heap) (sb lb r N : Nat) : Prop :=
  sb ≠ lb ∧
    (∀ v, 1 ≤ v → v ≤ r → QuotientCMachine.read heap sb v = some (.u64 (v-1))) ∧
    (∀ i, 1 ≤ i → i ≤ r → QuotientCMachine.read heap lb i = some (.u64 (N/i-1)))

lemma closeScope_same_env {s t : State} (he : t.env = s.env) : closeScope s t = t := by
  rcases s with ⟨se, sh⟩
  rcases t with ⟨te, th⟩
  dsimp only at he
  apply congrArg (fun env : Env => ({env := env, heap := th} : State))
  funext name
  rw [he]
  cases h : se name <;> simp [h]

lemma sub_literal_one {n : Nat} (hn : 1 ≤ n) (hword : n < modulus) :
    binary "-" (.u64 n) (.i32 1) = some (.u64 (n-1)) := by
  have hid : n + modulus - 1 = (n-1) + modulus := by omega
  have hn' : n-1 < modulus := (Nat.sub_le n 1).trans_lt hword
  simp [binary, Value.scalar, unsignedCommon, hid, Nat.mod_eq_of_lt hn']

lemma literal_one : literal 1 = some (.i32 1) := by norm_num [literal]

theorem pure_sub_one {call : Service} {heap : Heap} {env : Env} {i : Nat}
    (hi : env "i" = some (.u64 i)) (hi1 : 1 ≤ i) (hiw : i < modulus) :
    evalPure call heap env 8 (.binary "-" (.var "i") (.nat 1)) =
      some (.u64 (i-1)) := by
  apply pure_binary_of
  · simpa only [pure_var] using hi
  · simpa only [pure_literal] using literal_one
  · exact sub_literal_one hi1 hiw

theorem pure_quotient_sub_one {call : Service} {heap : Heap} {env : Env} {N i : Nat}
    (hn : env "n" = some (.u64 N)) (hi : env "i" = some (.u64 i))
    (hi0 : 0 < i) (hNw : N < modulus) (hq : 1 ≤ N/i) :
    evalPure call heap env 8
      (.binary "-" (.binary "/" (.var "n") (.var "i")) (.nat 1)) =
      some (.u64 (N/i-1)) := by
  apply pure_binary_of
  · apply pure_binary_of
    · simpa only [pure_var] using hn
    · simpa only [pure_var] using hi
    · exact binary_u64_div hi0 hNw
  · simpa only [pure_literal] using literal_one
  · exact sub_literal_one hq ((Nat.div_le_self N i).trans_lt hNw)

theorem initialized_store_eval {call : Service} {s : State} {after : Heap}
    {array : String} {base i value : Nat} {rhs : Expr}
    (ha : s.env array = some (.ptr base)) (hi : s.env "i" = some (.u64 i))
    (hrhs : evalPure call s.heap s.env 8 rhs = some (.u64 value))
    (hvalue : value < modulus) (hw : write s.heap base i value = some after) :
    Eval call (.binary "=" (.index (.var array) (.var "i")) rhs)
      s {s with heap := after} (.u64 value) := by
  exact eval_index_store_of (by simpa only [pure_var] using ha)
    (by simpa only [pure_var] using hi) hrhs (uint64_of_u64 hvalue) hw

lemma prefix_one (heap : Heap) (sb lb N : Nat) : Prefix heap sb lb N 1 := by
  intro j hj hlt
  omega

/-- Both actual writes, without requiring any old value to be initialized or
even readable. The resulting pair has explicit same-index and frame facts. -/
theorem initialize_pair {call : Service} {s : State} {sb lb N r i : Nat}
    (owned : Owned s.heap) (buffers : Buffers s.heap sb lb r)
    (hsmall : s.env "small" = some (.ptr sb))
    (hlarge : s.env "large" = some (.ptr lb))
    (hn : s.env "n" = some (.u64 N)) (hi : s.env "i" = some (.u64 i))
    (hi1 : 1 ≤ i) (hir : i ≤ r) (hrN : r ≤ N) (hN : N ≤ 2000000000000)
    (hprefix0 : Prefix s.heap sb lb N i) :
    ∃ t, Run call initBody s (.continuing t) ∧ t.env = s.env ∧
      Owned t.heap ∧ Buffers t.heap sb lb r ∧ Prefix t.heap sb lb N (i+1) := by
  obtain ⟨hne, S, L, hS, hL, hrS, hrL⟩ := buffers
  have hiN : i ≤ N := hir.trans hrN
  have hNw : N < modulus := by norm_num [modulus]; omega
  have hiw : i < modulus := hiN.trans_lt hNw
  have hq : 1 ≤ N/i := (Nat.le_div_iff_mul_le (by omega : 0 < i)).mpr (by simpa using hiN)
  have hqw : N/i < modulus := (Nat.div_le_self N i).trans_lt hNw
  have hsv : i-1 < modulus := (Nat.sub_le _ _).trans_lt hiw
  have hlv : N/i-1 < modulus := (Nat.sub_le _ _).trans_lt hqw
  have hSa := (owned.1 sb S hS).1
  have hLa := (owned.1 lb L hL).1
  have hSaddr : sb+8*i+8 ≤ modulus := by have h := (owned.1 sb S hS).2; omega
  have hLaddr : lb+8*i+8 ≤ modulus := by have h := (owned.1 lb L hL).2; omega
  let H1 := Function.update s.heap sb (some {S with words := Function.update S.words i (i-1)})
  let H2 := Function.update H1 lb (some {L with words := Function.update L.words i (N/i-1)})
  have hw1 : write s.heap sb i (i-1) = some H1 :=
    write_of_block hS hSa (by omega) hSaddr hsv
  have hL1 : H1 lb = some L := by simp [H1, Function.update_of_ne hne.symm, hL]
  have hw2 : write H1 lb i (N/i-1) = some H2 :=
    write_of_block hL1 hLa (by omega) hLaddr hlv
  let t1 : State := {s with heap := H1}
  let t2 : State := {s with heap := H2}
  have he1 : Eval call (.binary "=" (.index (.var "small") (.var "i"))
      (.binary "-" (.var "i") (.nat 1))) s t1 (.u64 (i-1)) := by
    exact initialized_store_eval hsmall hi (pure_sub_one hi hi1 hiw) hsv hw1
  have he2 : Eval call (.binary "=" (.index (.var "large") (.var "i"))
      (.binary "-" (.binary "/" (.var "n") (.var "i")) (.nat 1))) t1 t2 (.u64 (N/i-1)) := by
    exact initialized_store_eval hlarge hi
      (pure_quotient_sub_one hn hi (by omega) hNw hq) hlv hw2
  refine ⟨t2, ?_, rfl, write_preserves_owned (write_preserves_owned owned hw1) hw2, ?_, ?_⟩
  · apply StmtRun.sequence
    · exact SeqRun.next (StmtRun.evaluate he1)
        (SeqRun.next (StmtRun.evaluate he2) (SeqRun.nil t2))
    · change .continuing t2 = closeFlow s (.continuing t2)
      rw [closeFlow, closeScope_same_env (by rfl)]
  · refine ⟨hne, {S with words := Function.update S.words i (i-1)},
      {L with words := Function.update L.words i (N/i-1)}, ?_, ?_, hrS, hrL⟩
    · simp [t2, H2, H1, Function.update_of_ne hne]
    · simp [t2, H2]
  · intro j hj hjnext
    by_cases hji : j = i
    · subst j
      constructor
      · have hh := read_of_block (heap := t2.heap) (base := sb) (index := i)
          (block := {S with words := Function.update S.words i (i-1)})
          (by simp [t2, H2, H1, Function.update_of_ne hne]) hSa
          (by change i < S.extent; omega) hSaddr (by simpa using hsv)
        simpa only [Function.update_self] using hh
      · have hh := read_of_block (heap := t2.heap) (base := lb) (index := i)
          (block := {L with words := Function.update L.words i (N/i-1)})
          (by simp [t2, H2]) hLa (by change i < L.extent; omega) hLaddr (by simpa using hlv)
        simpa only [Function.update_self] using hh
    · have hp := hprefix0 j hj (by omega)
      constructor
      · simpa [t2, H2, H1, QuotientCMachine.read, Function.update_of_ne hne,
          hS, Function.update_of_ne hji] using hp.1
      · simpa [t2, H2, H1, QuotientCMachine.read, Function.update_of_ne hne.symm,
          hL, Function.update_of_ne hji] using hp.2

lemma guard_eval {call : Service} {s : State} {i r : Nat}
    (hi : s.env "i" = some (.u64 i)) (hr : s.env "r" = some (.u64 r)) :
    Eval call initGuard s s (.i32 (if i ≤ r then 1 else 0)) := by
  simp [Eval, initGuard, eval, pure_var, pure_binary, hi, hr]

lemma increment_eval {call : Service} {s : State} {i : Nat}
    (hi : s.env "i" = some (.u64 i)) (hnext : i+1 < modulus) :
    Eval call initIncrement s {s with env := bind s.env "i" (.u64 (i+1))}
      (.u64 (i+1)) := by
  simp [Eval, initIncrement, eval_increment, hi, Nat.mod_eq_of_lt hnext]

theorem for_remaining (k : Nat) {call : Service} {s : State} {sb lb N r i : Nat}
    (owned : Owned s.heap) (buffers : Buffers s.heap sb lb r)
    (hsmall : s.env "small" = some (.ptr sb))
    (hlarge : s.env "large" = some (.ptr lb))
    (hn : s.env "n" = some (.u64 N)) (hi : s.env "i" = some (.u64 i))
    (hr : s.env "r" = some (.u64 r))
    (hi1 : 1 ≤ i) (hrN : r ≤ N) (hN : N ≤ 2000000000000)
    (hcount : i+k = r+1) (hprefix0 : Prefix s.heap sb lb N i) :
    ∃ t, ForRun call (some initGuard) initIncrement initBody s (.continuing t) ∧
      t.env = bind s.env "i" (.u64 (r+1)) ∧ Owned t.heap ∧
      Buffers t.heap sb lb r ∧ Prefix t.heap sb lb N (r+1) := by
  induction k generalizing s i with
  | zero =>
      have hieq : i = r+1 := by omega
      refine ⟨s, ?_, ?_, owned, buffers, ?_⟩
      · apply ForRun.done
        have hg := GuardRun.present (truth := truth) (guard_eval (call := call) hi hr)
        simpa [truth, Value.bits, show ¬i≤r by omega] using hg
      · rw [← hieq]
        symm
        funext name
        by_cases h : name = "i"
        · subst name; simp [QuotientCMachine.bind, hi]
        · simp [QuotientCMachine.bind, Function.update_of_ne h]
      · simpa [hieq] using hprefix0
  | succ k ih =>
      have hir : i ≤ r := by omega
      obtain ⟨body, hbody, henv, howned, hbuffers, hprefix⟩ :=
        initialize_pair owned buffers hsmall hlarge hn hi hi1 hir hrN hN hprefix0
      have hnext : i+1 < modulus := by norm_num [modulus]; omega
      let step : State := {body with env := bind body.env "i" (.u64 (i+1))}
      have hstep : Eval call initIncrement body step (.u64 (i+1)) :=
        increment_eval (by simpa [henv] using hi) hnext
      obtain ⟨t, htail, ht, htowned, htbuffers, htprefix⟩ := ih (s := step) (i := i+1) howned hbuffers
        (by simp [step, QuotientCMachine.bind, henv, hsmall])
        (by simp [step, QuotientCMachine.bind, henv, hlarge])
        (by simp [step, QuotientCMachine.bind, henv, hn])
        (by simp [step, QuotientCMachine.bind])
        (by simp [step, QuotientCMachine.bind, henv, hr])
        (by omega) (by omega) hprefix
      refine ⟨t, ?_, ?_, htowned, htbuffers, htprefix⟩
      · apply ForRun.next _ hbody hstep htail
        have hg := GuardRun.present (truth := truth) (guard_eval (call := call) hi hr)
        simpa [truth, Value.bits, hir] using hg
      · simpa [step, henv, QuotientCMachine.bind, Function.update_idem] using ht

theorem initialization_loop {call : Service} {s : State} {sb lb N r : Nat}
    (owned : Owned s.heap) (buffers : Buffers s.heap sb lb r)
    (hsmall : s.env "small" = some (.ptr sb))
    (hlarge : s.env "large" = some (.ptr lb))
    (hn : s.env "n" = some (.u64 N)) (hr : s.env "r" = some (.u64 r))
    (hiFresh : s.env "i" = none) (hrN : r ≤ N) (hN : N ≤ 2000000000000) :
    ∃ t, Run call initFor s (.continuing t) ∧ t.env = s.env ∧
      Owned t.heap ∧ InitialRep t.heap sb lb r N := by
  let first : State := {s with env := bind s.env "i" (.u64 1)}
  have hdecl : Run call initDeclaration s (.continuing first) := by
    apply StmtRun.declare
    simp [Declare, declare_singleton, hiFresh, pure_literal, literal, uint64,
      Value.scalar, modulus, first]
  obtain ⟨last, hloop, hlast, howned, hbuffers, hprefix⟩ :=
    for_remaining r owned buffers
      (s := first) (by simp [first, QuotientCMachine.bind, hsmall])
      (by simp [first, QuotientCMachine.bind, hlarge])
      (by simp [first, QuotientCMachine.bind, hn])
      (by simp [first, QuotientCMachine.bind])
      (by simp [first, QuotientCMachine.bind, hr]) (by omega) hrN hN (by omega)
      (prefix_one _ _ _ _)
  let final := closeScope s last
  refine ⟨final, StmtRun.forLoop hdecl hloop rfl, ?_, howned, hbuffers.1, ?_, ?_⟩
  · funext name
    by_cases h : name = "i"
    · subst name
      simp [final, closeScope, hiFresh]
    · change (if (s.env name).isSome then last.env name else none) = s.env name
      rw [hlast]
      simp only [first, QuotientCMachine.bind, Function.update_of_ne h]
      cases hs : s.env name <;> rfl
  · intro v hv hvr
    exact (hprefix v hv (by omega)).1
  · intro i hi hir
    exact (hprefix i hi (by omega)).2

#print axioms actual_init_for
#print axioms initialize_pair
#print axioms initialization_loop
end RamanujanPV.QuotientCInit
