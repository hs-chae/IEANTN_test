/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCertificateCode
namespace RamanujanPV.QuotientPartition
open QuotientDemandCheck
/-- Exact Boolean ranges compose; this imports no mathematical oracle. -/
theorem append (check : Nat → Bool) (n m : Nat) :
    ∀ i, allFrom check i (n+m) = (allFrom check i n && allFrom check (i+n) m) := by
  induction n with
  | zero => intro i; simp [allFrom]
  | succ n ih => intro i; simp [allFrom, Nat.succ_add, ih, Nat.add_assoc, Bool.and_assoc]
theorem append_checked {check : Nat → Bool} {i n m : Nat}
    (left : allFrom check i n = true) (right : allFrom check (i+n) m = true) :
    allFrom check i (n+m) = true := by
  rw [append]
  simp [left, right]
#print axioms append_checked
end RamanujanPV.QuotientPartition
