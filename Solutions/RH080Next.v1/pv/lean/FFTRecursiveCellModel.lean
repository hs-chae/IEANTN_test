/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveSourceLayout
import FFTCopyLoop
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open WordArrays
open scoped BigOperators

/-- The signed value depends on exactly the six actual words of a source cell. -/
theorem represented_congr {a b : Nat → Nat} {i j : Nat}
    (h : ∀k, k < 6 → a (i+k) = b (j+k)) :
    CanonicalSource.represented a i = CanonicalSource.represented b j := by
  have sign := h 5 (by norm_num)
  have magnitude : FFT.Limbs.magnitude 1000000000 5 (fun k => a (i+k)) =
      FFT.Limbs.magnitude 1000000000 5 (fun k => b (j+k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    change a (i+k)*1000000000^k = b (j+k)*1000000000^k
    rw [h k (by have hh := Finset.mem_range.mp hk;omega)]
  simp only [CanonicalSource.represented,sign,magnitude]

theorem cell_congr {a b : Nat → Nat} {i j : Nat}
    (h : ∀k, k < 12 → a (12*i+k) = b (12*j+k)) : cell a i = cell b j := by
  apply Prod.ext
  · apply represented_congr
    intro k hk
    exact h k (by omega)
  · apply represented_congr
    intro k hk
    simpa only [Nat.add_assoc] using h (6+k) (by omega)

/-- The actual copy helper's computed prefix supplies exactly the leaf input
cell; the equality is derived from word indices, not an output certificate. -/
theorem cell_copy_leaf (old input : Nat → Nat) (start index : Nat) :
    cell (CopyLoop.prefixData old (fun j => input (index*12+j)) (start*12) 12) start =
      cell input index := by
  apply cell_congr
  intro k hk
  have inside : start*12 ≤ 12*start+k ∧ 12*start+k < start*12+12 := by omega
  unfold CopyLoop.prefixData
  rw [if_pos inside]
  change input (index*12+(12*start+k-start*12)) = input (12*index+k)
  congr 1
  omega

/-- The formal operational FFT relation is genuinely connected to the source
copy result at the base case. No numerical leaf answer is assumed. -/
theorem copied_leaf_trace (table : Nat → List FFT.IntegerModel.CInt)
    (old input : Nat → Nat) (start index step : Nat) :
    FFT.IntegerModel.ExecutionTrace table (cell input) 0 index step
      [cell (CopyLoop.prefixData old (fun j => input (index*12+j)) (start*12) 12) start] := by
  rw [cell_copy_leaf]
  exact .leaf index step

#print axioms copied_leaf_trace
end RH080Next.FFTPV.RecursiveSource
