/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientSieve
import Mathlib.Logic.Function.Basic

/-! Functional refinement of the actual quotient-table algorithm.
The large table is traversed in increasing index order and the small table in
 decreasing argument order, exactly as benchmark_quotient_pi.cpp. This file proves
mathematical memory-order invariants; source/AST execution correspondence is a
separate obligation and is not asserted by these functional theorems. -/
namespace RamanujanPV.QuotientTables
open RamanujanPV.QuotientSieve
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure Tables where
  small : Nat → Nat
  large : Nat → Nat

def Invariant (N r p : Nat) (T : Tables) : Prop :=
  (∀ v, 1  ≤  v → v  ≤  r → T.small v = total p v) ∧
  (∀ i, 1  ≤  i → i  ≤  r → T.large i = total p (N / i))

def initial (N : Nat) : Tables where
  small v := v - 1
  large i := N / i - 1

theorem initial_invariant (N r : Nat) : Invariant N r 2 (initial N) := by
  constructor
  · intro v hv hvr
    exact (total_initial v).symm
  · intro i hi hir
    exact (total_initial (N/i)).symm

def largeRead (N r p i : Nat) (T : Tables) : Nat :=
  if i * p  ≤  r then T.large (i*p) else T.small (N/(i*p))

def largeStep (N r p before i : Nat) (T : Tables) : Tables where
  small := T.small
  large := Function.update T.large i (T.large i - (largeRead N r p i T - before))

def BigStage (N r p next : Nat) (T : Tables) : Prop :=
  (∀ v, 1  ≤  v → v  ≤  r → T.small v = total p v) ∧
  (∀ i, 1  ≤  i → i  ≤  r → T.large i =
    if i  <  next then total (p+1) (N/i) else total p (N/i))

lemma bigStage_initial {N r p : Nat} {T : Tables} (h : Invariant N r p T) :
    BigStage N r p 1 T := by
  refine ⟨h.1, ?_⟩
  intro i hi hir
  rw [if_neg (by omega)]
  exact h.2 i hi hir

/-- Quotient closure is exact integer division, not an approximate lookup. -/
lemma quotient_closure (N i p : Nat) : (N/i)/p = N/(i*p) := by
  rw [Nat.div_div_eq_div_mul]

/-- The selected index lies in the represented small/large table, and every
large-table read is ahead of the currently written position. -/
theorem large_read_correct {N r p i : Nat} {T : Tables}
    (hp : Nat.Prime p) (hi : 1  ≤  i) (hir : i  ≤  r)
    (hisquare : i  ≤  N/(p*p)) (hroot : N  <  (r+1)*(r+1))
    (hstage : BigStage N r p i T) :
    largeRead N r p i T = total p ((N/i)/p) := by
  have hip : 0  <  i*p := Nat.mul_pos (by omega) hp.pos
  have hmul : i*(p*p)  ≤  N := (Nat.le_div_iff_mul_le (Nat.mul_pos hp.pos hp.pos)).mp hisquare
  have hqLower : p  ≤  N/(i*p) := (Nat.le_div_iff_mul_le hip).mpr (by nlinarith)
  rw [quotient_closure]
  unfold largeRead
  split_ifs with hsmall
  · have hnext : i  <  i*p := by nlinarith [hp.two_le]
    rw [hstage.2 (i*p) (by omega) hsmall, if_neg (by omega)]
  · have hqUpper : N/(i*p)  ≤  r := by
      by_contra bad
      have hbig : r+1  ≤  N/(i*p) := by omega
      have hbig' := (Nat.le_div_iff_mul_le hip).mp hbig
      nlinarith
    exact hstage.1 (N/(i*p)) (by have hp2 := hp.two_le; omega) hqUpper

/-- A single in-place large-table update preserves all still-needed old entries. -/
theorem large_step_preserves {N r p i before : Nat} {T : Tables}
    (hp : Nat.Prime p) (hi : 1  ≤  i) (hir : i  ≤  r)
    (hisquare : i  ≤  N/(p*p)) (hroot : N  <  (r+1)*(r+1))
    (hbefore : before = total p (p-1)) (hstage : BigStage N r p i T) :
    BigStage N r p (i+1) (largeStep N r p before i T) := by
  refine ⟨hstage.1, ?_⟩
  intro j hj hjr
  by_cases hji : j = i
  · subst j
    have hs : p*p  ≤  N/i := (Nat.le_div_iff_mul_le (by omega : 0 < i)).mpr
      (by have h := (Nat.le_div_iff_mul_le (Nat.mul_pos hp.pos hp.pos)).mp hisquare; nlinarith)
    have hread := large_read_correct hp hi hir hisquare hroot hstage
    dsimp only [largeStep]
    rw [Function.update_self, hread, hbefore, hstage.2 i hi hir, if_neg (by omega), if_pos (by omega)]
    exact (total_step hp hs).symm
  · dsimp only [largeStep]
    rw [Function.update_of_ne hji, hstage.2 j hj hjr]
    by_cases hlt : j  <  i <;> simp [hlt, show (j < i+1) ↔ (j < i) by omega]

def largeStop (N r p : Nat) : Nat := min r (N/(p*p))

def largeLoop (N r p before : Nat) : Nat → Tables → Tables
  | 0, T => T
  | k+1, T => largeStep N r p before (k+1) (largeLoop N r p before k T)

/-- Source's ascending i loop: at step i, every ip lookup is still old. -/
theorem largeLoop_stage {N r p before : Nat} {T : Tables}
    (hp : Nat.Prime p) (hroot : N < (r+1)*(r+1))
    (hbefore : before = total p (p-1)) (hinit : Invariant N r p T)
    (k : Nat) (hk : k ≤ largeStop N r p) :
    BigStage N r p (k+1) (largeLoop N r p before k T) := by
  induction k with
  | zero => exact bigStage_initial hinit
  | succ k ih =>
    have hk' : k ≤ largeStop N r p := by omega
    have hr : k+1 ≤ r := hk.trans (Nat.min_le_left _ _)
    have hq : k+1 ≤ N/(p*p) := hk.trans (Nat.min_le_right _ _)
    simpa only [largeLoop] using large_step_preserves hp (by omega) hr hq hroot hbefore (ih hk')

/-- Entries beyond the loop stop need no subtraction: their represented
argument lies strictly below p squared. -/
theorem largeLoop_complete {N r p before : Nat} {T : Tables}
    (hp : Nat.Prime p) (hroot : N < (r+1)*(r+1))
    (hbefore : before = total p (p-1)) (hinit : Invariant N r p T) :
    (∀ v, 1 ≤ v → v ≤ r → (largeLoop N r p before (largeStop N r p) T).small v = total p v) ∧
    (∀ i, 1 ≤ i → i ≤ r → (largeLoop N r p before (largeStop N r p) T).large i = total (p+1) (N/i)) := by
  have stage := largeLoop_stage hp hroot hbefore hinit (largeStop N r p) le_rfl
  refine ⟨stage.1, ?_⟩
  intro i hi hir
  have h := stage.2 i hi hir
  by_cases hdone : i < largeStop N r p + 1
  · simpa only [if_pos hdone] using h
  · rw [if_neg hdone] at h
    have hstop : min r (N/(p*p)) < i := by change largeStop N r p < i; omega
    have hquot : N/(p*p) < i := by
      rcases min_lt_iff.mp hstop with bad | good
      · omega
      · exact good
    have hN : N < i*(p*p) := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hp.pos hp.pos)).mp hquot
    have hs : N/i < p*p := (Nat.div_lt_iff_lt_mul (by omega : 0 < i)).mpr (by nlinarith)
    exact h.trans (total_skip_below_square hs).symm

def smallStep (p before v : Nat) (T : Tables) : Tables where
  small := Function.update T.small v (T.small v - (T.small (v/p) - before))
  large := T.large

def SmallStage (N r p boundary : Nat) (T : Tables) : Prop :=
  (∀ i, 1 ≤ i → i ≤ r → T.large i = total (p+1) (N/i)) ∧
  (∀ v, 1 ≤ v → v ≤ r → T.small v =
    if boundary < v then total (p+1) v else total p v)

/-- Source's descending v loop reads v/p below the write, hence still old. -/
theorem small_step_preserves {N r p v before : Nat} {T : Tables}
    (hp : Nat.Prime p) (hv : p*p ≤ v) (hvr : v ≤ r)
    (hbefore : before = total p (p-1)) (hstage : SmallStage N r p v T) :
    SmallStage N r p (v-1) (smallStep p before v T) := by
  have hp2 := hp.two_le
  have hv0 : 0 < v := by nlinarith
  refine ⟨hstage.1, ?_⟩
  intro j hj hjr
  by_cases hji : j = v
  · subst j
    have hqlo : 1 ≤ v/p := (Nat.le_div_iff_mul_le hp.pos).mpr (by nlinarith)
    have hqhi : v/p ≤ r := (Nat.div_le_self v p).trans hvr
    have hq : ¬v < v/p := by have h := Nat.div_le_self v p; omega
    have hread : T.small (v/p) = total p (v/p) := by
      rw [hstage.2 (v/p) hqlo hqhi, if_neg hq]
    have hwrite : T.small v = total p v := by
      rw [hstage.2 v (by omega) hvr, if_neg (by omega)]
    dsimp only [smallStep]
    rw [Function.update_self, hread, hwrite, hbefore, if_pos (by omega)]
    exact (total_step hp hv).symm
  · dsimp only [smallStep]
    rw [Function.update_of_ne hji, hstage.2 j hj hjr]
    by_cases hlt : v < j <;> simp [hlt, show (v-1 < j) ↔ (v < j) by omega]

lemma smallStage_initial {N r p before : Nat} {T : Tables}
    (hp : Nat.Prime p) (hroot : N < (r+1)*(r+1))
    (hbefore : before = total p (p-1)) (hinit : Invariant N r p T) :
    SmallStage N r p r (largeLoop N r p before (largeStop N r p) T) := by
  have h := largeLoop_complete hp hroot hbefore hinit
  refine ⟨h.2, ?_⟩
  intro v hv hvr
  rw [if_neg (by omega)]
  exact h.1 v hv hvr

def smallLoop (p before r : Nat) : Nat → Tables → Tables
  | 0, T => T
  | k+1, T => smallStep p before (r-k) (smallLoop p before r k T)

def smallCount (r p : Nat) : Nat := r + 1 - p*p

/-- Every small-table access is inside the range, and after k descending
updates precisely the entries above r-k have the next sieve invariant. -/
theorem smallLoop_stage {N r p before : Nat} {T : Tables}
    (hp : Nat.Prime p) (hbefore : before = total p (p-1))
    (hinit : SmallStage N r p r T)
    (k : Nat) (hk : k ≤ smallCount r p) :
    SmallStage N r p (r-k) (smallLoop p before r k T) := by
  induction k with
  | zero => simpa only [smallLoop, Nat.sub_zero] using hinit
  | succ k ih =>
    have hp2 := hp.two_le
    have hcount : k+1 ≤ r+1-p*p := hk
    have hk' : k ≤ smallCount r p := by omega
    have hv : p*p ≤ r-k := by omega
    have hvr : r-k ≤ r := Nat.sub_le _ _
    have h := small_step_preserves hp hv hvr hbefore (ih hk')
    simpa only [smallLoop, Nat.sub_sub, show k+1 = k+1 by rfl] using h

/-- The completed descending loop establishes the complete next invariant. -/
theorem smallLoop_complete {N r p before : Nat} {T : Tables}
    (hp : Nat.Prime p) (hbefore : before = total p (p-1))
    (hinit : SmallStage N r p r T) :
    Invariant N r (p+1) (smallLoop p before r (smallCount r p) T) := by
  have h := smallLoop_stage hp hbefore hinit (smallCount r p) le_rfl
  refine ⟨?_, h.1⟩
  intro v hv hvr
  have hs := h.2 v hv hvr
  by_cases hdone : r - smallCount r p < v
  · simpa only [if_pos hdone] using hs
  · rw [if_neg hdone] at hs
    have hvsmall : v < p*p := by unfold smallCount at hdone; omega
    exact hs.trans (total_skip_below_square hvsmall).symm

def primeRound (N r p : Nat) (T : Tables) : Tables :=
  if T.small p = T.small (p-1) then T
  else
    let before := T.small (p-1)
    let afterLarge := largeLoop N r p before (largeStop N r p) T
    smallLoop p before r (smallCount r p) afterLarge

/-- The source's adjacent-entry primality test is proved against the invariant;
composite rounds preserve the table without trusting a list of primes. -/
theorem primeRound_correct {N r p : Nat} {T : Tables}
    (hp2 : 2 ≤ p) (hpr : p ≤ r) (hroot : N < (r+1)*(r+1))
    (hinit : Invariant N r p T) : Invariant N r (p+1) (primeRound N r p T) := by
  have hpv : T.small p = total p p := hinit.1 p (by omega) hpr
  have hpm : T.small (p-1) = total p (p-1) := hinit.1 (p-1) (by omega) (by omega)
  unfold primeRound
  split_ifs with same
  · have hcomposite : ¬Nat.Prime p := by
      intro prime
      have hdet := (detected_iff_prime hp2).mpr prime
      rw [hpv, hpm] at same
      exact hdet same
    constructor
    · intro v hv hvr
      rw [total_skip_composite hcomposite]
      exact hinit.1 v hv hvr
    · intro i hi hir
      rw [total_skip_composite hcomposite]
      exact hinit.2 i hi hir
  · have hprime : Nat.Prime p := by
      apply (detected_iff_prime hp2).mp
      simpa only [← hpv, ← hpm] using same
    exact smallLoop_complete hprime hpm (smallStage_initial hprime hroot hpm hinit)

def sieveLoop (N r : Nat) : Nat → Tables → Tables
  | 0, T => T
  | k+1, T => primeRound N r (k+2) (sieveLoop N r k T)

theorem sieveLoop_invariant {N r : Nat} (hroot : N < (r+1)*(r+1))
    (k : Nat) (hk : k ≤ r-1) :
    Invariant N r (k+2) (sieveLoop N r k (initial N)) := by
  induction k with
  | zero => exact initial_invariant N r
  | succ k ih =>
    have hk' : k ≤ r-1 := by omega
    have hp2 : 2 ≤ k+2 := by omega
    have hpr : k+2 ≤ r := by omega
    simpa only [sieveLoop] using primeRound_correct hp2 hpr hroot (ih hk')

/-- The complete functional small/large quotient sieve returns actual prime
counting at every N covered by the supplied square-root frontier. It neither
assumes output counts nor enumerates the large number N inside Lean. -/
def count (N r : Nat) : Nat := (sieveLoop N r (r-1) (initial N)).large 1

theorem count_eq_primeCounting {N r : Nat} (hr : 1 ≤ r) (hroot : N < (r+1)*(r+1)) :
    count N r = Nat.primeCounting N := by
  have h := sieveLoop_invariant hroot (r-1) le_rfl
  have hp : r-1+2 = r+1 := by omega
  rw [hp] at h
  have hv := h.2 1 (by omega) hr
  change count N r = _ at hv
  have hv' : count N r = total (r+1) N := by simpa only [Nat.div_one] using hv
  exact hv'.trans (total_final hroot)

/-- Both checked unsigned subtractions are nonnegative under the invariant.
The second inequality is the finite-set cardinality of the removed composites. -/
theorem subtraction_safe {p v : Nat} (hp : Nat.Prime p) (hs : p*p ≤ v) :
    total p (p-1) ≤ total p (v/p) ∧
    total p (v/p) - total p (p-1) ≤ total p v := by
  have hq : p ≤ v/p := (Nat.le_div_iff_mul_le hp.pos).mpr hs
  have hsubset := survivors_bound_mono (p:=p) (show p-1 ≤ v/p by omega)
  have hcard := Finset.card_le_card hsubset
  change total p (p-1) ≤ total p (v/p) at hcard
  refine ⟨hcard, ?_⟩
  have hremoved : (removed p v).card ≤ (survivors p v).card := by
    apply Finset.card_le_card
    intro n hn
    exact (Finset.mem_sdiff.mp hn).1
  have htail : (tail p (v/p)).card = total p (v/p) - total p (p-1) :=
    Finset.card_sdiff_of_subset hsubset
  rw [removed_card hp, htail] at hremoved
  exact hremoved

/-- Every stored mathematical count fits within its argument, yielding a
source-level uint64 range bound once the source's argument bound is supplied. -/
theorem total_le_argument (p v : Nat) : total p v ≤ v := by
  have h : (survivors p v).card ≤ (Finset.Icc 2 v).card := by
    apply Finset.card_le_card
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  change total p v ≤ _ at h
  rw [Nat.card_Icc] at h
  omega

#print axioms primeRound_correct
#print axioms count_eq_primeCounting
#print axioms subtraction_safe
#print axioms largeLoop_complete
#print axioms smallLoop_complete
#print axioms initial_invariant
#print axioms large_step_preserves
end RamanujanPV.QuotientTables
