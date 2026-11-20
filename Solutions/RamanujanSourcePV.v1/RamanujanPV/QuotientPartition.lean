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
  | zero => intro i; exact congrArg (allFrom check i) (Nat.zero_add m)
  | succ n ih =>
    intro i
    calc
      allFrom check i ((n+1)+m) = (check i && allFrom check (i+1) (n+m)) :=
        congrArg (allFrom check i) (Nat.succ_add n m)
      _ = (check i && (allFrom check (i+1) n && allFrom check ((i+1)+n) m)) :=
        congrArg (fun b => check i && b) (ih (i+1))
      _ = ((check i && allFrom check (i+1) n) && allFrom check ((i+1)+n) m) :=
        (Bool.and_assoc _ _ _).symm
      _ = (allFrom check i (n+1) && allFrom check (i+(n+1)) m) :=
        congrArg (fun k => allFrom check i (n+1) && allFrom check k m) (Nat.succ_add i n)
theorem append_checked {check : Nat → Bool} {i n m : Nat}
    (left : allFrom check i n = true) (right : allFrom check (i+n) m = true) :
    allFrom check i (n+m) = true := by
  exact (append check n m i).trans
    ((congrArg (fun b => b && allFrom check (i+n) m) left).trans
      (congrArg (fun b => true && b) right))
#print axioms append_checked
end RamanujanPV.QuotientPartition
