/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCertificateCode

/-! Pure local-classification certificate syntax and boolean checks. Soundness
is proved separately in PrimeWindow.lean; this module performs no native call. -/
namespace RamanujanPV.PrimeWindow
open QuotientDemandCheck
set_option autoImplicit false

structure Entry where
  isPrime : Bool
  witness : Nat
  cumulative : Nat
  deriving Repr,DecidableEq

noncomputable def checkEntry (base : Nat) (primes : Lean.RArray Nat) (primeCount : Nat)
    (entries : Lean.RArray Entry) (i : Nat) : Bool :=
  let e:=entries.get i
  let n:=base+i+1
  (if e.isPrime then decide (e.witness < primeCount ∧ primes.get e.witness=n)
   else decide (2 ≤ e.witness ∧ e.witness < n ∧ n%e.witness=0)) &&
  decide (e.cumulative=(if i=0 then 0 else (entries.get (i-1)).cumulative)+(if e.isPrime then 1 else 0))

noncomputable def checkAll (base : Nat) (primes : Lean.RArray Nat) (primeCount : Nat)
    (entries : Lean.RArray Entry) (count : Nat) : Bool :=
  allFrom (checkEntry base primes primeCount entries) 0 count

end RamanujanPV.PrimeWindow
