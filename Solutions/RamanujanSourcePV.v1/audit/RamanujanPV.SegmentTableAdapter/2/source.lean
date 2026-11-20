/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.SegmentCFunction
import RamanujanPV.PrimeWindow

/-! Ordinary checked local tables and source-first C verification are distinct
parts of this adapter. The table proof discharges the source's comparison
condition; the complete actual C body independently constructs every flag by
sieving, before comparing input words or returning a count. This does not assert
that an unverified native C++ caller initialized its arguments correctly. -/
namespace RamanujanPV.SegmentTableAdapter
open QuotientCMachine SegmentMemory SegmentCheckerMath
open QuotientDemandCheck PrimeWindow
set_option autoImplicit false

def flags (entries : Lean.RArray PrimeWindow.Entry) (i : Nat) : Nat :=
  if (entries.get i).isPrime then 1 else 0

theorem classified_flags {base count primeCount : Nat} {primes : Lean.RArray Nat}
    {entries : Lean.RArray PrimeWindow.Entry}
    (primeGood : ∀j,j<primeCount→Nat.Prime (primes.get j))
    (checked : checkAll base primes primeCount entries count=true)
    (basePositive : 1≤base) (countPositive : 0<count) :
    ∀i,i<(base+count)-(base+1)+1→
      flags entries i=finalFlags (base+1) (base+count) i := by
  intro i hi
  have index : i<count := by omega
  have entry := allFrom_at count 0 checked i (by omega) (by omega)
  have classification := (entry_classification primeGood entry).1
  rw [final_flag (by omega) (by omega)]
  have sameN : base+1+i=base+i+1 := by omega
  rw [sameN]
  by_cases hp : Nat.Prime (base+i+1)
  · simp [flags,hp,classification.mp hp]
  · have hn : (entries.get i).isPrime=false :=
      Bool.eq_false_iff.mpr (fun h=>hp (classification.mpr h))
    simp [flags,hp,hn]

/-- A concrete exact segment count together with a checked local table is
realized by the complete actual source checker, under its precise memory input
applicability contract. Numerical table checking alone is not called PV. -/
theorem source_execution_from_checked_table {call : Service} {s : State}
    {base count capacity cb fb primeCount output : Nat} {primes : Lean.RArray Nat}
    {entries : Lean.RArray PrimeWindow.Entry}
    (primeGood : ∀j,j<primeCount→Nat.Prime (primes.get j))
    (checked : checkAll base primes primeCount entries count=true)
    (basePositive : 1≤base) (countPositive : 0<count)
    (upper : base+count≤2000000000000) (cap : count≤capacity) (apart : cb≠fb)
    (owned : Owned s.heap) (scratch : SegmentCInit.Buffer s.heap fb count)
    (inputFlags : FlagsRep s.heap cb count (flags entries))
    (env : SegmentCFunctionPrefix.Inputs (base+1) (base+count) capacity cb fb s.env)
    (countValue : segmentCount (base+1) (base+count)=output) :
    ∃t, Run call SegmentCheckerSource.checkerFunction.body s
        (.returned t (.u64 (output+1))) ∧ t.env=s.env ∧ Owned t.heap := by
  have length : (base+count)-(base+1)+1=count := by omega
  obtain ⟨t,run,envt,ownedt⟩ := SegmentCFunction.correct_claims_execution
    (call:=call) (lo:=base+1) (hi:=base+count) (by omega) (by omega) upper
    (by omega) apart owned (by simpa [length] using scratch)
    (by simpa [length] using inputFlags) env
    (classified_flags primeGood checked basePositive countPositive)
  exact ⟨t,by simpa only [countValue] using run,envt,ownedt⟩

#print axioms classified_flags
#print axioms source_execution_from_checked_table
end RamanujanPV.SegmentTableAdapter
