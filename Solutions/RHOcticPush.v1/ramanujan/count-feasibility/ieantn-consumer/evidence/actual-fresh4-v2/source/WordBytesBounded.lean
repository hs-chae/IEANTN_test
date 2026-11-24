/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientDriverExecution

/-! The existing eight-byte little-endian encoder is injective below its
capacity. This small arithmetic fact adds no execution or ABI assumption. -/
namespace RHOcticPush.IEANTNCount
open RamanujanPV.QuotientDriverExecution
set_option autoImplicit false

theorem wordBytes_injective_below {a b : Nat}
    (ha : a < 256^8) (hb : b < 256^8) (bytes : wordBytes a = wordBytes b) : a = b := by
  have digit (i : Nat) (hi : i < 8) : (a / 256^i) % 256 = (b / 256^i) % 256 :=
    List.map_inj_left.mp bytes i (List.mem_range.mpr hi)
  have step (i : Nat) (next : a / 256^(i+1) = b / 256^(i+1))
      (same : (a / 256^i) % 256 = (b / 256^i) % 256) : a / 256^i = b / 256^i := by
    apply Nat.ext_div_mod (n := 256)
    · simpa only [Nat.div_div_eq_div_mul, pow_succ] using next
    · exact same
  have e8 : a / 256^8 = b / 256^8 := by
    rw [Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb]
  have e7 := step 7 e8 (digit 7 (by decide))
  have e6 := step 6 e7 (digit 6 (by decide))
  have e5 := step 5 e6 (digit 5 (by decide))
  have e4 := step 4 e5 (digit 4 (by decide))
  have e3 := step 3 e4 (digit 3 (by decide))
  have e2 := step 2 e3 (digit 2 (by decide))
  have e1 := step 1 e2 (digit 1 (by decide))
  have e0 := step 0 e1 (digit 0 (by decide))
  simpa only [pow_zero, Nat.div_one] using e0

#print axioms wordBytes_injective_below
end RHOcticPush.IEANTNCount
