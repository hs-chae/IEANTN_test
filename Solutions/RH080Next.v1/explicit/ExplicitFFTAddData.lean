/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTDivideSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

/-- Supported application aliasing: identical slices, separate allocations,
or nonoverlapping six-word signed values within one allocation. -/
def SafeAlias (outObject outStart inObject inStart : Nat) : Prop :=
  outObject≠inObject ∨ outStart=inStart ∨ outStart+6 ≤ inStart ∨ inStart+6 ≤ outStart

def scan (sub : Bool) (a b : Nat → Nat) (j : Nat) : (Nat → Nat)×Nat :=
  if sub then subDigits base a b j else addDigits base a b j

def digitTotal (sub : Bool) (a b c : Nat) : Nat := if sub then base+a-b-c else a+b+c
def nextCarry (sub : Bool) (t : Nat) : Nat:=if sub then 1-t/base else t/base

def currentData (old : Nat → Nat → Nat) (outObject outStart : Nat) (sub : Bool)
    (a b : Nat → Nat) (j object i : Nat) : Nat :=
  if object=outObject ∧ outStart ≤ i ∧ i < outStart+j then (scan sub a b j).1 (i-outStart)
  else old object i

theorem currentData_initial (old : Nat → Nat → Nat) (outObject outStart : Nat) (sub : Bool)
    (a b : Nat → Nat) : currentData old outObject outStart sub a b 0=old := by
  funext object i
  simp [currentData]

theorem scan_initial (sub : Bool) (a b : Nat → Nat) : (scan sub a b 0).2=0 := by
  cases sub <;> rfl

theorem scan_step (sub : Bool) (a b : Nat → Nat) (j : Nat) :
    scan sub a b (j+1)=
      (Function.update (scan sub a b j).1 j ((digitTotal sub (a j) (b j) (scan sub a b j).2)%base),
        nextCarry sub (digitTotal sub (a j) (b j) (scan sub a b j).2)) := by
  cases sub <;> rfl

theorem currentData_step (old : Nat → Nat → Nat) (outObject outStart : Nat) (sub : Bool)
    (a b : Nat → Nat) (j : Nat) :
    Function.update (currentData old outObject outStart sub a b j outObject) (outStart+j)
      ((digitTotal sub (a j) (b j) (scan sub a b j).2)%base)=
        currentData old outObject outStart sub a b (j+1) outObject := by
  funext i
  by_cases he : i=outStart+j
  · subst i
    simp [currentData,scan_step]
  · by_cases hi : outStart ≤ i ∧ i < outStart+j
    · have hne : i-outStart≠j := by omega
      simp [currentData,Function.update_of_ne he,hi,
        show outStart ≤ i ∧ i < outStart+(j+1) by omega,scan_step,Function.update_of_ne hne]
    · simp [currentData,Function.update_of_ne he,hi,
        show ¬(outStart ≤ i ∧ i < outStart+(j+1)) by omega]

/-- Read-after-write alias reasoning is proved for the actual unread source
index, rather than assuming both original input arrays remain unchanged. -/
theorem currentData_unread (old : Nat → Nat → Nat) (outObject outStart inObject inStart : Nat)
    (safe : SafeAlias outObject outStart inObject inStart) (sub : Bool) (a b : Nat → Nat)
    (j : Nat) (hj : j < 5) :
    currentData old outObject outStart sub a b j inObject (inStart+j)=old inObject (inStart+j) := by
  rcases safe with separate|same|left|right
  · simp [currentData,separate.symm]
  · subst inStart
    simp [currentData]
  · dsimp [currentData]
    rw [if_neg (by intro bad; omega)]
  · dsimp [currentData]
    rw [if_neg (by intro bad; omega)]

theorem addDigits_bounds (a b : Nat → Nat) (n : Nat)
    (ha : ∀j < n,a j < base) (hb : ∀j < n,b j < base) :
    (addDigits base a b n).2 ≤ 1 ∧ ∀j < n,(addDigits base a b n).1 j < base := by
  induction n with
  | zero=>simp [addDigits]
  | succ n ih=>
    obtain ⟨hc,hd⟩:=ih (fun i hi=>ha i (by omega)) (fun i hi=>hb i (by omega))
    constructor
    · change (a n+b n+(addDigits base a b n).2)/base ≤ 1
      have han:=ha n (by omega)
      have hbn:=hb n (by omega)
      have small : (a n+b n+(addDigits base a b n).2)/base < 2 :=
        (Nat.div_lt_iff_lt_mul (by norm_num [base])).mpr (by omega)
      omega
    · intro j hj
      change Function.update (addDigits base a b n).1 n ((a n+b n+(addDigits base a b n).2)%base) j < base
      by_cases he : j=n
      · subst j
        simpa only [Function.update_self] using Nat.mod_lt (a n+b n+(addDigits base a b n).2) (by norm_num [base])
      · rw [Function.update_of_ne he]
        exact hd j (by omega)

theorem scan_bounds (sub : Bool) (a b : Nat → Nat) (n : Nat)
    (ha : ∀j < n,a j < base) (hb : ∀j < n,b j < base) :
    (scan sub a b n).2 ≤ 1 ∧ ∀j < n,(scan sub a b n).1 j < base := by
  cases sub with
  | false=>exact addDigits_bounds a b n ha hb
  | true=>exact subDigits_bounds base n (by norm_num [base]) a b ha hb

theorem digitTotal_bounds (sub : Bool) (a b c : Nat) (ha : a < base) (hb : b < base) (hc : c ≤ 1) :
    digitTotal sub a b c < 2*base ∧ nextCarry sub (digitTotal sub a b c) ≤ 1 := by
  cases sub with
  | false=>
    have ht : a+b+c < 2*base := by omega
    exact ⟨ht,by have h: (a+b+c)/base < 2 := (Nat.div_lt_iff_lt_mul (by norm_num [base])).mpr (by omega); exact Nat.le_of_lt_succ h⟩
  | true=>exact ⟨by dsimp [digitTotal]; omega,Nat.sub_le 1 _⟩

#print axioms currentData_step
#print axioms currentData_unread
#print axioms scan_bounds
end RH080Next.FFTPV.AddSource
