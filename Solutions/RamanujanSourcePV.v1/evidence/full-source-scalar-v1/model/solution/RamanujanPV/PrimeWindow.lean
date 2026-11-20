/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCountRealization
import RamanujanPV.QuotientDemandCheck
import RamanujanPV.LocalWindowCode

/-! Exact local prime-count increments. A base count is reused; every following
integer is independently classified using a proved-prime table or a checked
proper divisor. The prime-table correctness is an explicit pending input until
its actual primality certificates compile. No boolean prime list is trusted. -/
namespace RamanujanPV.PrimeWindow
open QuotientDemandCheck QuotientCCell
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma primeCounting_succ (n : Nat) :
    Nat.primeCounting (n+1)=Nat.primeCounting n+(if Nat.Prime (n+1) then 1 else 0) := by
  exact Nat.count_succ Nat.Prime (n+1)

lemma entry_classification {base primeCount i : Nat} {primes : Lean.RArray Nat} {entries : Lean.RArray Entry}
    (primeGood : ∀ j, j < primeCount → Nat.Prime (primes.get j))
    (checked : checkEntry base primes primeCount entries i=true) :
    (Nat.Prime (base+i+1) ↔ (entries.get i).isPrime=true) ∧
    (entries.get i).cumulative=(if i=0 then 0 else (entries.get (i-1)).cumulative)+
      (if (entries.get i).isPrime then 1 else 0) := by
  have clauses :
      (if (entries.get i).isPrime then
        decide ((entries.get i).witness < primeCount ∧ primes.get (entries.get i).witness=base+i+1)
       else decide (2 ≤ (entries.get i).witness ∧ (entries.get i).witness < base+i+1 ∧
         (base+i+1)%(entries.get i).witness=0))=true ∧
      (entries.get i).cumulative=(if i=0 then 0 else (entries.get (i-1)).cumulative)+
        (if (entries.get i).isPrime then 1 else 0) := by simpa [checkEntry] using checked
  refine ⟨?_,clauses.2⟩
  cases hm : (entries.get i).isPrime with
  | false =>
    have factors : 2 ≤ (entries.get i).witness ∧ (entries.get i).witness < base+i+1 ∧
        (base+i+1)%(entries.get i).witness=0 := by simpa [hm] using clauses.1
    have hn := Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero factors.2.2) factors.1 factors.2.1
    simp [hm,hn]
  | true =>
    have fields : (entries.get i).witness < primeCount ∧ primes.get (entries.get i).witness=base+i+1 :=
      by simpa [hm] using clauses.1
    have hp := primeGood _ fields.1
    rw [fields.2] at hp
    simp [hm,hp]

/-- Exact cardinality transport through every local classified integer. -/
theorem count_at {base count i : Nat} {primes : Lean.RArray Nat} {primeCount : Nat} {entries : Lean.RArray Entry}
    (primeGood : ∀ j, j < primeCount → Nat.Prime (primes.get j))
    (checked : checkAll base primes primeCount entries count=true) (index : i < count) :
    Nat.primeCounting (base+i+1)=Nat.primeCounting base+(entries.get i).cumulative := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have check := allFrom_at count 0 checked i (by omega) (by omega)
    obtain ⟨classification,step⟩ := entry_classification primeGood check
    have flag : (if Nat.Prime (base+i+1) then 1 else 0)=(if (entries.get i).isPrime then 1 else 0) := by
      by_cases hp : Nat.Prime (base+i+1)
      · simp [hp,classification.mp hp]
      · have hm : (entries.get i).isPrime=false := Bool.eq_false_iff.mpr (fun h=>hp (classification.mpr h))
        simp [hp,hm]
    rw [primeCounting_succ,step,flag]
    by_cases zero : i=0
    · subst i
      simp
    · have prev := ih (i-1) (by omega) (by omega)
      have eq : base+(i-1)+1=base+i := by omega
      rw [eq] at prev
      rw [prev,if_neg zero,Nat.add_assoc]

/-- A local increment becomes a verified-source count of the same unchanged C
counter, once its actual base count and local classification are established. -/
theorem source_count_at {base baseValue count i : Nat} {primes : Lean.RArray Nat}
    {primeCount : Nat} {entries : Lean.RArray Entry}
    (baseExecution : SourceExecution base baseValue)
    (primeGood : ∀ j, j < primeCount → Nat.Prime (primes.get j))
    (checked : checkAll base primes primeCount entries count=true) (index : i < count)
    (lower : 2 ≤ base+i+1) (upper : base+i+1 ≤ 2000000000000) :
    SourceExecution (base+i+1) (baseValue+(entries.get i).cumulative) := by
  apply QuotientCountRealization.source_execution_from_kernel_value lower upper
  rw [count_at primeGood checked index,source_execution_count baseExecution]

#print axioms count_at
#print axioms source_count_at
end RamanujanPV.PrimeWindow
