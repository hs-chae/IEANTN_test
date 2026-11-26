/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderBindings
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect WordArrays

def rawStores (old : Nat → Nat) (start encoded : Nat) : Nat → Nat:=
  Function.update (Function.update (Function.update (Function.update old
    (start+2) ((InputCell.magnitudeValue encoded*100)%InputCell.base))
    (start+3) (((InputCell.magnitudeValue encoded*100)/InputCell.base)%InputCell.base))
    (start+4) (((InputCell.magnitudeValue encoded*100)/InputCell.base)/InputCell.base))
    (start+5) (InputCell.signValue encoded)

def readyCell (old : Nat → Nat) (start encoded : Nat) : Nat → Nat:=
  CanonicalSource.canonicalData (rawStores old start encoded) start

def iterationData (old : Nat → Nat) (n j encoded : Nat) : Nat → Nat:=
  let prepared:=readyCell old (12*j) encoded
  if 0< j then CopyLoop.prefixData prepared (fun k=> prepared (12*j+k)) (12*(n-j)) 12 else prepared

def currentData (encoded : Nat → Nat) (n : Nat) : Nat → Nat → Nat
  | 0=> fun _=>0
  | j+1=> iterationData (currentData encoded n j) n j (encoded j)

theorem rawStores_word (old : Nat → Nat) (start encoded k : Nat) (hk : k<12)
    (zero : ∀i<12,old (start+i)=0) : rawStores old start encoded (start+k)=InputCell.rawCell encoded k:=by
  have zero0 : old start=0:=by simpa only [Nat.add_zero] using zero 0 (by omega)
  interval_cases k <;> simp [rawStores,InputCell.rawCell,InputCell.packed,zero,zero0]

theorem canonical_words_congr (a b : Nat → Nat) (start target k : Nat) (hk : k<12)
    (same : ∀i<12,a (start+i)=b (target+i)) :
    CanonicalSource.canonicalData a start (start+k)=CanonicalSource.canonicalData b target (target+k):=by
  have sums : CanonicalSource.digitSum a start 5=CanonicalSource.digitSum b target 5:=by
    apply Finset.sum_congr rfl
    intro i hi
    exact same i (by have hi:=Finset.mem_range.mp hi;omega)
  unfold CanonicalSource.canonicalData
  rw [sums]
  split_ifs
  · by_cases atSign : k=5
    · subst k;simp
    · rw [Function.update_of_ne (show start+k≠start+5 by omega),Function.update_of_ne (show target+k≠target+5 by omega)]
      exact same k hk
  · exact same k hk

theorem readyCell_word (old : Nat → Nat) (start encoded k : Nat) (hk : k<12)
    (zero : ∀i<12,old (start+i)=0) : readyCell old start encoded (start+k)=InputCell.cell encoded k:=by
  simpa only [readyCell,InputCell.cell,Nat.zero_add] using canonical_words_congr (rawStores old start encoded) (InputCell.rawCell encoded) start 0 k hk
    (fun i hi=> by simpa only [Nat.zero_add] using rawStores_word old start encoded i hi zero)

theorem readyCell_outside (old : Nat → Nat) (start encoded k : Nat) (outside : k< start ∨ start+12≤ k) :
    readyCell old start encoded k=old k:=by
  have ne2 : k≠start+2:=by omega
  have ne3 : k≠start+3:=by omega
  have ne4 : k≠start+4:=by omega
  have ne5 : k≠start+5:=by omega
  unfold readyCell CanonicalSource.canonicalData
  split_ifs <;> simp only [Function.update_of_ne ne5,rawStores,Function.update_of_ne ne4,Function.update_of_ne ne3,Function.update_of_ne ne2]

theorem iterationData_outside (old : Nat → Nat) (n j encoded k : Nat)
    (forward : k<12*j ∨ 12*j+12≤ k) (mirror : k<12*(n-j) ∨ 12*(n-j)+12≤ k) :
    iterationData old n j encoded k=old k:=by
  unfold iterationData
  split_ifs
  · rw [show CopyLoop.prefixData (readyCell old (12*j) encoded) (fun i=> readyCell old (12*j) encoded (12*j+i)) (12*(n-j)) 12 k=
      readyCell old (12*j) encoded k from by simp [CopyLoop.prefixData,show ¬(12*(n-j)≤ k ∧ k<12*(n-j)+12) by omega]]
    exact readyCell_outside old (12*j) encoded k forward
  · exact readyCell_outside old (12*j) encoded k forward

/-- The whole as-yet-unwritten middle region is still the actual zeroed input
allocation. This will discharge the raw-store precondition for every source row. -/
theorem currentData_middle (encoded : Nat → Nat) (n j k r : Nat)
    (low : j≤ k) (high : k+j≤ n) (hr : r<12) : currentData encoded n j (12*k+r)=0:=by
  induction j with
  | zero=> rfl
  | succ j ih=>
    rw [currentData,iterationData_outside _ n j (encoded j) (12*k+r) (Or.inr (by omega))]
    · exact ih (by omega) (by omega)
    · exact Or.inl (by omega)

#print axioms readyCell_word
#print axioms iterationData_outside
#print axioms currentData_middle
end RH080Next.FFTPV.InputLoader
