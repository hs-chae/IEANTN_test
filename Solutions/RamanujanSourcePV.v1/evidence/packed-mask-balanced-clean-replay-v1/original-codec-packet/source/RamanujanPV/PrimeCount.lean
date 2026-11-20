/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.CArithmetic

namespace RamanujanPV
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Each transition executes the source ++n, actual trial-prime helper and
uint64 addition; no prime-count table or count-oracle is a premise. -/
inductive CountExec (bound : Nat) : Nat → Nat → Nat → Prop
  | done {n count} (stop : ¬n<bound) : CountExec bound n count count
  | step {n count bit result} (guard : n<bound)
      (prime : PrimeExec ((n+1)%wordMod) bit)
      (rest : CountExec bound ((n+1)%wordMod) ((count+bit)%wordMod) result) :
      CountExec bound n count result

def primePrefix (n : Nat) : Nat := Nat.primeCounting n

theorem prefix_zero : primePrefix 0=0 := by simp [primePrefix]
theorem prefix_step (n : Nat) :
    primePrefix (n+1)=primePrefix n+(if Nat.Prime (n+1) then 1 else 0) := by
  unfold primePrefix Nat.primeCounting Nat.primeCounting'
  exact Nat.count_succ _ _

theorem prefix_le (n : Nat) : primePrefix n≤n := by
  induction n with
  | zero => simp [prefix_zero]
  | succ n ih =>
      rw [prefix_step]
      split <;> omega

theorem count_exec_correct_aux {bound : Nat} (word : bound<wordMod) :
    ∀n count result, CountExec bound n count result → n≤bound → count=primePrefix n →
      result=primePrefix bound := by
  intro n count result run
  induction run with
  | @done n count stop =>
      intro before countEq
      have eq : n=bound := by omega
      subst n
      exact countEq
  | @step n count bit result guard prime rest ih =>
      intro before countEq
      have nword : n+1<wordMod := by omega
      have bumpEq : (n+1)%wordMod=n+1 := Nat.mod_eq_of_lt nword
      have primeExact : PrimeExec (n+1) bit := by simpa [bumpEq] using prime
      have bitEq : bit=(if Nat.Prime (n+1) then 1 else 0) := by
        by_cases hp : Nat.Prime (n+1)
        · have hb := (prime_exec_correct primeExact).2.mpr hp
          simp [hp,hb]
        · rcases (prime_exec_correct primeExact).1 with h0|h1
          · simp [hp,h0]
          · exact False.elim (hp ((prime_exec_correct primeExact).2.mp h1))
      have countNext : (count+bit)%wordMod=primePrefix ((n+1)%wordMod) := by
        rw [countEq,bitEq,bumpEq,←prefix_step]
        exact Nat.mod_eq_of_lt ((prefix_le _).trans_lt nword)
      exact ih (by rw [bumpEq];omega) countNext

theorem count_exec_correct {bound n result : Nat}
    (word : bound<wordMod) (run : CountExec bound n (primePrefix n) result)
    (before : n≤bound) : result=primePrefix bound :=
  count_exec_correct_aux word n (primePrefix n) result run before rfl

/-- Termination and complete mathematical output of the actual uint64 loop.
The bound is strictly below2^64, so ++n and accumulated count never wrap. -/
theorem count_exec_terminates (bound : Nat) (word : bound<wordMod) :
    ∀fuel n, n≤bound → bound<n+fuel → ∃result, CountExec bound n (primePrefix n) result := by
  intro fuel
  induction fuel with
  | zero =>
      intro n before budget
      exact ⟨primePrefix n,CountExec.done (by omega)⟩
  | succ fuel ih =>
      intro n before budget
      by_cases guard : n<bound
      · have nword : n+1<wordMod := by omega
        have bumpEq : (n+1)%wordMod=n+1 := Nat.mod_eq_of_lt nword
        obtain ⟨bit,prime⟩ := prime_exec_terminates (n+1) nword
        have bitEq : bit=(if Nat.Prime (n+1) then 1 else 0) := by
          by_cases hp : Nat.Prime (n+1)
          · have hb := (prime_exec_correct prime).2.mpr hp
            simp [hp,hb]
          · rcases (prime_exec_correct prime).1 with h0|h1
            · simp [hp,h0]
            · exact False.elim (hp ((prime_exec_correct prime).2.mp h1))
        have nextEq : (primePrefix n+bit)%wordMod=primePrefix (n+1) := by
          rw [bitEq,←prefix_step]
          exact Nat.mod_eq_of_lt ((prefix_le _).trans_lt nword)
        obtain ⟨result,rest⟩ := ih (n+1) (by omega) (by omega)
        refine ⟨result,CountExec.step (bit:=bit) guard ?_ ?_⟩
        · simpa [bumpEq] using prime
        · simpa [bumpEq,nextEq] using rest
      · exact ⟨primePrefix n,CountExec.done guard⟩

theorem count_exec_complete (bound : Nat) (word : bound<wordMod) :
    CountExec bound 0 0 (Nat.primeCounting bound) := by
  obtain ⟨result,run⟩ := count_exec_terminates bound word (bound+1) 0 (by omega) (by omega)
  have outEq := count_exec_correct word run (by omega)
  simpa [prefix_zero,primePrefix,outEq] using run

#print axioms count_exec_correct
#print axioms count_exec_complete
end RamanujanPV
