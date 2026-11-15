/- Exact mathematical model of printS's repeated remainder/division and
reverse traversal. This module alone is a kernel mathematical component,
not a proof that the C function executes it. Source execution is separate. -/
import Mathlib.Data.Nat.Digits.Lemmas
import ScopedIO.TextWorldRuntime

namespace ScopedIO.PrintSDecimalModel
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The forced first loop iteration emits zero even when the magnitude is 0.
Nat.digits uses the empty list for 0, so that convention is adjusted explicitly. -/
def digits (n : Nat) : List Nat := if n = 0 then [0] else Nat.digits 10 n

def bytes (n : Nat) : List Nat := (digits n).reverse.map (48 + ·)

/-- Raw source neg flag is retained, including a possible signed zero.
Actual signed constructors can separately discharge normalization. -/
def signedBytes (negative : Bool) (n : Nat) : List Nat :=
  (if negative then [45] else []) ++ bytes n

theorem digits_step (n : Nat) : digits n = n % 10 :: Nat.digits 10 (n / 10) := by
  by_cases zero : n = 0
  · simp [digits,zero]
  · exact (if_neg zero).trans (Nat.digits_eq_cons_digits_div (by decide) zero)

theorem digits_ne_nil (n : Nat) : digits n ≠ [] := by
  rw [digits_step]
  exact List.cons_ne_nil _ _

theorem digit_lt {n d : Nat} (h : d ∈ digits n) : d < 10 := by
  by_cases zero : n = 0
  · have equal : d = 0 := by simpa [digits,zero] using h
    omega
  · exact Nat.digits_lt_base (by decide) (by simpa [digits,zero] using h)

theorem ofDigits_digits (n : Nat) : Nat.ofDigits 10 (digits n) = n := by
  by_cases zero : n = 0
  · simp [digits,zero,Nat.ofDigits]
  · simpa [digits,zero] using Nat.ofDigits_digits 10 n

theorem quotient_step (n k : Nat) : n / 10^(k+1) = (n / 10^k) / 10 := by
  rw [pow_succ,Nat.div_div_eq_div_mul]

theorem remainder_digit (n k : Nat) : n / 10^k % 10 < 10 := Nat.mod_lt _ (by decide)

theorem digits_capacity (n : Nat) : (digits n).length ≤ 1024 ↔ n < 10^1024 := by
  by_cases zero : n = 0
  · simp [digits,zero]
  · simpa [digits,zero] using (Nat.digits_length_le_iff (by decide) n)

theorem source_guard {n k : Nat} (capacity : (digits n).length ≤ 1024)
    (active : k < (digits n).length) : k < 1024 ∧ k+1 ≤ 1024 ∧ k+1 < 2^32 := by
  omega

theorem bytes_valid (n : Nat) : ∀ byte ∈ bytes n, byte < 128 := by
  intro byte member
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp member
  have small : d < 10 := digit_lt (List.mem_reverse.mp hd)
  omega

theorem signedBytes_valid (negative : Bool) (n : Nat) :
    ∀ byte ∈ signedBytes negative n, byte < 128 := by
  intro byte member
  have either : byte ∈ (if negative then [45] else []) ∨ byte ∈ bytes n :=
    List.mem_append.mp member
  rcases either with sign | digit
  · cases negative <;> simp_all
  · exact bytes_valid n byte digit

/-- Recovering digit values from the emitted most-significant-first bytes
and reversing gives exactly the magnitude, including the zero case. -/
theorem output_represents (n : Nat) :
    Nat.ofDigits 10 ((bytes n).map (· - 48)).reverse = n := by
  have cancel : (bytes n).map (· - 48) = (digits n).reverse := by
    simp [bytes,List.map_map,Function.comp_def]
  rw [cancel,List.reverse_reverse]
  exact ofDigits_digits n

end ScopedIO.PrintSDecimalModel
