/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveCellModel
import FFTRecursiveButterflyAddInvariant
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource

/-- Exact actual words copied from the source twelve-word slice. -/
theorem copy_cell_word (old input : Nat → Nat) (start source k : Nat) (hk : k<12) :
    CopyLoop.prefixData old (fun j => input (source+j)) (start*12) 12 (12*start+k) = input (source+k) := by
  have inside : start*12≤12*start+k ∧ 12*start+k<start*12+12 := by omega
  unfold CopyLoop.prefixData
  rw [if_pos inside]
  congr 1
  omega

/-- Different complete cells of the same output allocation are not changed by
one actual twelve-word source copy, rather than merely sharing an object frame. -/
theorem copy_cell_other (old input : Nat → Nat) (start source target : Nat) (different : target≠start) :
    cell (CopyLoop.prefixData old (fun j => input (source+j)) (start*12) 12) target = cell old target := by
  apply cell_congr
  intro k hk
  have outside : ¬(start*12≤12*target+k ∧ 12*target+k<start*12+12) := by omega
  simp [CopyLoop.prefixData,outside]

theorem copy_cell_normalized (old input : Nat → Nat) (start source : Nat)
    (digits : ∀c : Fin 2,∀k,k<5 → input (source+6*c.val+k)<1000000000)
    (signs : ∀c : Fin 2,input (source+6*c.val+5)≤1) :
    NormalizedCell (CopyLoop.prefixData old (fun j => input (source+j)) (start*12) 12) start := by
  constructor
  · intro c k hk
    have h := copy_cell_word old input start source (6*c.val+k) (by have bound := c.isLt;omega)
    have same : CopyLoop.prefixData old (fun j => input (source+j)) (start*12) 12 (12*start+6*c.val+k)=input (source+6*c.val+k) := by
      simpa only [Nat.add_assoc] using h
    rw [same]
    exact digits c k hk
  · intro c
    have h := copy_cell_word old input start source (6*c.val+5) (by have bound := c.isLt;omega)
    have same : CopyLoop.prefixData old (fun j => input (source+j)) (start*12) 12 (12*start+6*c.val+5)=input (source+6*c.val+5) := by
      simpa only [Nat.add_assoc] using h
    rw [same]
    exact signs c

/-- Word-normalization of a disjoint existing cell survives the actual copy. -/
theorem copy_other_normalized (old input : Nat → Nat) (start source target : Nat)
    (different : target≠start) (normalized : NormalizedCell old target) :
    NormalizedCell (CopyLoop.prefixData old (fun j => input (source+j)) (start*12) 12) target := by
  have same : ∀k,k<12 → CopyLoop.prefixData old (fun j => input (source+j)) (start*12) 12 (12*target+k)=old (12*target+k) := by
    intro k hk
    have outside : ¬(start*12≤12*target+k ∧ 12*target+k<start*12+12) := by omega
    simp [CopyLoop.prefixData,outside]
  constructor
  · intro c k hk
    have word := same (6*c.val+k) (by have bound := c.isLt;omega)
    have word' : CopyLoop.prefixData old (fun j => input (source+j)) (start*12) 12 (12*target+6*c.val+k)=old (12*target+6*c.val+k) := by
      simpa only [Nat.add_assoc] using word
    rw [word']
    exact normalized.1 c k hk
  · intro c
    have word := same (6*c.val+5) (by have bound := c.isLt;omega)
    have word' : CopyLoop.prefixData old (fun j => input (source+j)) (start*12) 12 (12*target+6*c.val+5)=old (12*target+6*c.val+5) := by
      simpa only [Nat.add_assoc] using word
    rw [word']
    exact normalized.2 c

#print axioms copy_cell_normalized
#print axioms copy_other_normalized
end RH080Next.FFTPV.RecursiveSource
