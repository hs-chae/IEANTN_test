/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib
import Lean.Data.RArray

/-! Compact kernel prime-certificate aggregation. This is a mathematical
certificate-tree helper, not source-first verification of a C program. Every
leaf must carry its genuine primality proof; a tree lookup creates no new fact. -/
namespace RamanujanPV.LocalPrimeTree

def PrimeTreeGood : Lean.RArray Nat → Prop
  | .leaf prime => Nat.Prime prime
  | .branch _ left right => PrimeTreeGood left ∧ PrimeTreeGood right

@[simp] theorem good_leaf (prime : Nat) :
    PrimeTreeGood (.leaf prime) ↔ Nat.Prime prime := Iff.rfl

@[simp] theorem good_branch (pivot : Nat) (left right : Lean.RArray Nat) :
    PrimeTreeGood (.branch pivot left right) ↔ PrimeTreeGood left ∧ PrimeTreeGood right := Iff.rfl

theorem getImpl_prime (tree : Lean.RArray Nat) (good : PrimeTreeGood tree) (index : Nat) :
    Nat.Prime (tree.getImpl index) := by
  induction tree with
  | leaf value => exact good
  | branch pivot left right leftGood rightGood =>
      simp only [Lean.RArray.getImpl]
      split
      · exact leftGood good.1
      · exact rightGood good.2

/-- RArray is a total decision tree: every possible lookup returns one of its
proved-prime leaves. In-range index/value correspondence remains the separate
certificate-provider obligation. -/
theorem get_prime {tree : Lean.RArray Nat} (good : PrimeTreeGood tree) (index : Nat) :
    Nat.Prime (tree.get index) := by
  rw [Lean.RArray.get_eq_getImpl]
  exact getImpl_prime tree good index

theorem bounded_prime_provider {tree : Lean.RArray Nat} (good : PrimeTreeGood tree)
    (count : Nat) : ∀ index, index < count → Nat.Prime (tree.get index) := by
  intro index _
  exact get_prime good index

#print axioms get_prime
#print axioms good_branch
end RamanujanPV.LocalPrimeTree
