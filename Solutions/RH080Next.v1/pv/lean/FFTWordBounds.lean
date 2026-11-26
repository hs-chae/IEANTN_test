/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTWordArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.WordArrays

/-- The precise source inner-loop invariant, retaining the next digit and carry. -/
theorem schoolbook_next_bounds (a b digit carry : Nat)
    (ha : a<1000000000) (hb : b<1000000000)
    (hd : digit<1000000000) (hc : carry<1000000000) :
    (digit+a*b+carry)%1000000000<1000000000 ∧
      (digit+a*b+carry)/1000000000<1000000000 := by
  have hp : a*b≤999999998000000001 :=
    Nat.mul_le_mul (by omega : a≤999999999) (by omega : b≤999999999)
  constructor
  · exact Nat.mod_lt _ (by decide)
  · omega

/-- Source long division carries a bounded remainder and emits one base digit.
All actual divisors (including N=2^24) are within this stated interface. -/
theorem divide_digit_bounds (remainder digit divisor : Nat)
    (hd : digit<1000000000) (hdiv : 0<divisor) (hmax : divisor≤16777216)
    (hr : remainder<divisor) :
    remainder*1000000000+digit<2^64 ∧
    (remainder*1000000000+digit)/divisor<1000000000 ∧
    (remainder*1000000000+digit)%divisor<divisor := by
  have ht : remainder*1000000000+digit<divisor*1000000000 := by omega
  refine ⟨by omega,?_,Nat.mod_lt _ hdiv⟩
  exact (Nat.div_lt_iff_lt_mul hdiv).mpr (by simpa only [Nat.mul_comm] using ht)

/-- Source increment and signed addition cannot overflow the underlying word. -/
theorem add_digit_bounds (a b carry : Nat) (ha : a<1000000000)
    (hb : b<1000000000) (hc : carry≤1) :
    a+b+carry<2^64 ∧ (a+b+carry)/1000000000≤1 ∧
      (a+b+carry)%1000000000<1000000000 := by
  refine ⟨by omega,by omega,Nat.mod_lt _ (by decide)⟩

/-- Source subtraction uses a base offset, so each actual subtraction is exact
unsigned arithmetic, and the new borrow remains 0 or 1. -/
theorem subtract_digit_bounds (a b borrow : Nat) (ha : a<1000000000)
    (hb : b<1000000000) (hc : borrow≤1) :
    b+borrow≤1000000000+a ∧
    1000000000+a-b-borrow<2^64 ∧
    (1000000000+a-b-borrow)/1000000000≤1 ∧
    1-(1000000000+a-b-borrow)/1000000000≤1 := by
  omega

#print axioms schoolbook_next_bounds
#print axioms divide_digit_bounds
#print axioms add_digit_bounds
#print axioms subtract_digit_bounds
end RH080Next.FFTPV.WordArrays
