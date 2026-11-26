/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader

theorem iteration_forward (old : Nat → Nat) (n j encoded r : Nat) (shape : 2*j<n) (hr : r<12)
    (zero : ∀i<12,old (12*j+i)=0) : iterationData old n j encoded (12*j+r)=InputCell.cell encoded r:=by
  unfold iterationData
  split_ifs
  · have outside : ¬(12*(n-j)≤12*j+r ∧ 12*j+r<12*(n-j)+12):=by omega
    simp only [CopyLoop.prefixData,if_neg outside]
    exact readyCell_word old _ encoded r hr zero
  · exact readyCell_word old _ encoded r hr zero

theorem iteration_mirror (old : Nat → Nat) (n j encoded r : Nat) (positive : 0<j) (hr : r<12)
    (zero : ∀i<12,old (12*j+i)=0) : iterationData old n j encoded (12*(n-j)+r)=InputCell.cell encoded r:=by
  unfold iterationData
  rw [if_pos positive]
  have inside : 12*(n-j)≤12*(n-j)+r ∧ 12*(n-j)+r<12*(n-j)+12:=by omega
  simp only [CopyLoop.prefixData,if_pos inside,Nat.add_sub_cancel_left]
  exact readyCell_word old _ encoded r hr zero

theorem currentData_forward (encoded : Nat → Nat) (n j k r : Nat) (shape : 2*j<n) (hk : k<j) (hr : r<12) :
    currentData encoded n j (12*k+r)=InputCell.cell (encoded k) r:=by
  induction j generalizing k with
  | zero=>omega
  | succ j ih=>
    by_cases last : k=j
    · subst k
      exact iteration_forward _ n j (encoded j) r (by omega) hr (fun i hi=>currentData_middle encoded n j j i (le_refl _) (by omega) hi)
    · rw [currentData,iterationData_outside _ n j (encoded j) (12*k+r)]
      · exact ih k (by omega) (by omega)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)

theorem currentData_mirror (encoded : Nat → Nat) (n j k r : Nat) (shape : 2*j<n) (hk0 : 0<k) (hk : k<j) (hr : r<12) :
    currentData encoded n j (12*(n-k)+r)=InputCell.cell (encoded k) r:=by
  induction j generalizing k with
  | zero=>omega
  | succ j ih=>
    by_cases last : k=j
    · subst k
      exact iteration_mirror _ n j (encoded j) r hk0 hr (fun i hi=>currentData_middle encoded n j j i (le_refl _) (by omega) hi)
    · rw [currentData,iterationData_outside _ n j (encoded j) (12*(n-k)+r)]
      · exact ih k (by omega) hk0 (by omega)
      · exact Or.inr (by omega)
      · exact Or.inr (by omega)

/-- Exact whole sparse even input vector represented by the loader's word
model. Forward cells, reflected cells and every untouched zero cell are covered. -/
theorem currentData_decoded (encoded : Nat → Nat) (n j k r : Nat) (shape : 2*j<n) (hk : k<n) (hr : r<12) :
    currentData encoded n j (12*k+r)=
      if k<j then InputCell.cell (encoded k) r else if n-k<j then InputCell.cell (encoded (n-k)) r else 0:=by
  by_cases forward : k<j
  · rw [if_pos forward]
    exact currentData_forward encoded n j k r shape forward hr
  · rw [if_neg forward]
    by_cases mirror : n-k<j
    · rw [if_pos mirror]
      have positive : 0<n-k:=by omega
      have result:=currentData_mirror encoded n j (n-k) r shape positive mirror hr
      simpa only [Nat.sub_sub_self hk.le] using result
    · rw [if_neg mirror]
      exact currentData_middle encoded n j k r (by omega) (by omega) hr

#print axioms currentData_forward
#print axioms currentData_mirror
#print axioms currentData_decoded
end RH080Next.FFTPV.InputLoader
