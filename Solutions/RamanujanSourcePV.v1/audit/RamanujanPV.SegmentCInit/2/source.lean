/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.SegmentCheckerSource
import RamanujanPV.QuotientCInit

/-! Actual source initialization of the segmented checker's flags. No value or
classification of the old buffer contents is assumed. All stores are executed. -/
namespace RamanujanPV.SegmentCInit
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops QuotientCMachine
set_option autoImplicit false
set_option maxHeartbeats 0

def initBody : Stmt := .eval (.binary "=" (.index (.var "flags") (.var "i")) (.nat 1))
def initGuard : Expr := .binary "<" (.var "i") (.var "length")
def initIncrement : Expr := .unary "++" (.var "i")
def initDeclaration : Stmt := .declare [⟨"uint64_t", "i", some (.nat 0)⟩]
def initFor : Stmt := .forLoop initDeclaration (some initGuard) initIncrement initBody

def actualInit : Option Stmt := match SegmentCheckerSource.checkerFunction.body with
  | .sequence body => body[5]?
  | _ => none

theorem actual_init : actualInit = some initFor := rfl

def Buffer (heap : Heap) (base length : Nat) : Prop :=
  ∃ block, heap base = some block ∧ length ≤ block.extent

def Prefix (heap : Heap) (base next : Nat) : Prop :=
  ∀ j, j < next → QuotientCMachine.read heap base j = some (.u64 1)

def Frame (before after : Heap) (base : Nat) : Prop :=
  ∀ address, address ≠ base → after address = before address

lemma guard_eval {call : Service} {s : State} {i length : Nat}
    (hi : s.env "i" = some (.u64 i)) (hlen : s.env "length" = some (.u64 length)) :
    Eval call initGuard s s (.i32 (if i < length then 1 else 0)) := by
  simp [Eval, initGuard, eval, pure_var, pure_binary, hi, hlen]

lemma increment_eval {call : Service} {s : State} {i : Nat}
    (hi : s.env "i" = some (.u64 i)) (hnext : i+1 < modulus) :
    Eval call initIncrement s {s with env := bind s.env "i" (.u64 (i+1))}
      (.u64 (i+1)) := by
  simp [Eval, initIncrement, eval_increment, hi, Nat.mod_eq_of_lt hnext]

theorem initialize_one {call : Service} {s : State} {base length i : Nat}
    (owned : Owned s.heap) (buffer : Buffer s.heap base length)
    (hflags : s.env "flags" = some (.ptr base)) (hi : s.env "i" = some (.u64 i))
    (hil : i < length) (prior : Prefix s.heap base i) :
    ∃ t, Run call initBody s (.continuing t) ∧ t.env = s.env ∧
      Owned t.heap ∧ Buffer t.heap base length ∧ Prefix t.heap base (i+1) ∧
      SameShape s.heap t.heap ∧ Frame s.heap t.heap base := by
  obtain ⟨block, hb, hextent⟩ := buffer
  have halign := (owned.1 base block hb).1
  have haddress : base+8*i+8 ≤ modulus := by
    have h := (owned.1 base block hb).2
    omega
  have hone : (1 : Nat) < modulus := by norm_num [modulus]
  let after := Function.update s.heap base (some {block with words := Function.update block.words i 1})
  have hw : write s.heap base i 1 = some after :=
    write_of_block hb halign (by omega) haddress hone
  let t : State := {s with heap := after}
  have evaluated : Eval call (.binary "=" (.index (.var "flags") (.var "i")) (.nat 1))
      s t (.u64 1) := by
    exact eval_index_store_of (by simpa only [pure_var] using hflags)
      (by simpa only [pure_var] using hi)
      (by simp only [pure_literal]; norm_num [literal])
      (by norm_num [uint64, Value.scalar, modulus]) hw
  refine ⟨t, StmtRun.evaluate evaluated, rfl, write_preserves_owned owned hw, ?_, ?_, ?_, ?_⟩
  · exact ⟨{block with words := Function.update block.words i 1}, by simp [t, after], hextent⟩
  · intro j hj
    by_cases hji : j = i
    · subst j
      have hread := read_of_block (heap:=t.heap) (base:=base) (index:=i)
        (block:={block with words := Function.update block.words i 1})
        (by simp [t, after]) halign (by change i < block.extent; omega) haddress
        (by simpa using hone)
      simpa only [Function.update_self] using hread
    · have hp := prior j (by omega)
      simpa [t, after, QuotientCMachine.read, hb, Function.update_of_ne hji] using hp
  · exact word_update_sameShape hb
  · intro address hne
    simp [t, after, Function.update_of_ne hne]

theorem for_remaining (k : Nat) {call : Service} {s : State} {base length i : Nat}
    (owned : Owned s.heap) (buffer : Buffer s.heap base length)
    (hflags : s.env "flags" = some (.ptr base)) (hi : s.env "i" = some (.u64 i))
    (hlen : s.env "length" = some (.u64 length)) (hword : length < modulus)
    (hcount : i+k = length) (prior : Prefix s.heap base i) :
    ∃ t, ForRun call (some initGuard) initIncrement initBody s (.continuing t) ∧
      t.env = bind s.env "i" (.u64 length) ∧ Owned t.heap ∧
      Buffer t.heap base length ∧ Prefix t.heap base length ∧
      SameShape s.heap t.heap ∧ Frame s.heap t.heap base := by
  induction k generalizing s i with
  | zero =>
    have hieq : i = length := by omega
    refine ⟨s, ?_, ?_, owned, buffer, ?_, (fun _ => rfl), (fun _ _ => rfl)⟩
    · apply ForRun.done
      have hg := GuardRun.present (truth:=truth) (guard_eval (call:=call) hi hlen)
      simpa [truth, Value.bits, show ¬ i < length by omega] using hg
    · rw [←hieq]
      symm
      funext name
      by_cases h : name = "i"
      · subst name; simp [bind, hi]
      · simp [bind, Function.update_of_ne h]
    · simpa [hieq] using prior
  | succ k ih =>
    have hil : i < length := by omega
    obtain ⟨body, hbody, henv, howned, hbuffer, hprefix, hshape, hframe⟩ :=
      initialize_one owned buffer hflags hi hil prior
    have hnext : i+1 < modulus := (by omega : i+1 ≤ length).trans_lt hword
    let step : State := {body with env := bind body.env "i" (.u64 (i+1))}
    have hstep : Eval call initIncrement body step (.u64 (i+1)) :=
      increment_eval (by simpa [henv] using hi) hnext
    obtain ⟨t, htail, ht, htowned, htbuffer, htprefix, htshape, htframe⟩ := ih (s:=step)
      (i:=i+1) howned hbuffer
      (by simp [step, bind, henv, hflags]) (by simp [step, bind])
      (by simp [step, bind, henv, hlen]) hword (by omega) hprefix
    refine ⟨t, ?_, ?_, htowned, htbuffer, htprefix, ?_, ?_⟩
    · apply ForRun.next _ hbody hstep htail
      have hg := GuardRun.present (truth:=truth) (guard_eval (call:=call) hi hlen)
      simpa [truth, Value.bits, hil] using hg
    · simpa [step, henv, bind, Function.update_idem] using ht
    · intro address
      exact (hshape address).trans (htshape address)
    · intro address hne
      exact (htframe address hne).trans (hframe address hne)

/-- Complete actual source for-loop from arbitrary old contents. The result
has fresh checked one-words, exact metadata and other-block frame preservation. -/
theorem initialization_loop {call : Service} {s : State} {base length : Nat}
    (owned : Owned s.heap) (buffer : Buffer s.heap base length)
    (hflags : s.env "flags" = some (.ptr base))
    (hlen : s.env "length" = some (.u64 length))
    (hiFresh : s.env "i" = none) (hword : length < modulus) :
    ∃ t, Run call initFor s (.continuing t) ∧ t.env = s.env ∧
      Owned t.heap ∧ Buffer t.heap base length ∧ Prefix t.heap base length ∧
      SameShape s.heap t.heap ∧ Frame s.heap t.heap base := by
  let first : State := {s with env := bind s.env "i" (.u64 0)}
  have hdecl : Run call initDeclaration s (.continuing first) := by
    apply StmtRun.declare
    simp [Declare, declare_singleton, hiFresh, pure_literal, literal, uint64,
      Value.scalar, modulus, first]
  obtain ⟨last, hloop, hlast, howned, hbuffer, hprefix, hshape, hframe⟩ :=
    for_remaining length owned buffer (s:=first)
      (by simp [first, bind, hflags]) (by simp [first, bind])
      (by simp [first, bind, hlen]) hword (by omega) (by intro j hj; omega)
  let final := closeScope s last
  refine ⟨final, StmtRun.forLoop hdecl hloop rfl, ?_, howned, hbuffer, hprefix, hshape, hframe⟩
  funext name
  by_cases h : name = "i"
  · subst name
    simp [final, closeScope, hiFresh]
  · change (if (s.env name).isSome then last.env name else none) = s.env name
    rw [hlast]
    simp only [first, bind, Function.update_of_ne h]
    cases hs : s.env name <;> rfl

#print axioms actual_init
#print axioms initialize_one
#print axioms initialization_loop
end RamanujanPV.SegmentCInit
