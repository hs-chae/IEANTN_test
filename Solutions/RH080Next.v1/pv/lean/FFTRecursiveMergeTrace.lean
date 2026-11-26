/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveLoopTotal
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource

def cells (data : Nat → Nat) (start count : Nat) : List FFT.IntegerModel.CInt :=
  (List.range count).map (fun k => cell data (start+k))

@[simp] theorem cells_length (data : Nat → Nat) (start count : Nat) :
    (cells data start count).length=count := by simp [cells]

theorem cells_getD (data : Nat → Nat) (start count k : Nat) (hk : k<count) :
    (cells data start count).getD k (0,0)=cell data (start+k) := by
  simp [cells,List.getD_eq_getElem, hk]

theorem cells_append (data : Nat → Nat) (start a b : Nat) :
    cells data start (a+b)=cells data start a++cells data (start+a) b := by
  simp only [cells,List.range_add,List.map_append,List.map_map]
  congr 1
  apply List.map_congr_left
  intro k hk
  simp only [Function.comp_apply]
  congr 1
  omega

theorem cells_congr {a b : Nat → Nat} {start count : Nat}
    (same : ∀k,k<count → cell a (start+k)=cell b (start+k)) : cells a start count=cells b start count := by
  apply List.map_congr_left
  intro k hk
  exact same k (List.mem_range.mp hk)

private theorem merge_range (a b w p q : Nat → FFT.IntegerModel.CInt) (n : Nat)
    (hp : ∀k,k<n → p k=FFT.IntegerModel.add (a k) (FFT.IntegerModel.mul (b k) (w k)))
    (hq : ∀k,k<n → q k=FFT.IntegerModel.sub (a k) (FFT.IntegerModel.mul (b k) (w k))) :
    FFT.IntegerModel.MergeTrace ((List.range n).map a) ((List.range n).map b)
      ((List.range n).map w) ((List.range n).map p) ((List.range n).map q) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    simp only [List.range_succ,List.map_append,List.map_cons,List.map_nil]
    exact (ih (fun k hk=>hp k (by omega)) (fun k hk=>hq k (by omega))).append
      (.cons _ _ _ _ _ [] [] [] [] [] (hp n (by omega)) (hq n (by omega)) .nil)

/-- The completed real row invariant supplies the independent integer merge
relation, with the exact global stride-selected source twiddles. -/
theorem MergeProgress.merge_trace {initial table output : Nat → Nat} {start s total : Nat}
    (h : MergeProgress initial table start (2^s) (total/2^(s+1)) (2^s) output) :
    FFT.IntegerModel.MergeTrace (cells initial start (2^s)) (cells initial (start+2^s) (2^s))
      (stages table total (s+1)) (cells output start (2^s)) (cells output (start+2^s) (2^s)) := by
  have stage : stages table total (s+1)=
      (List.range (2^s)).map (fun j=>cell table (j*(total/2^(s+1)))) := by simp [stages]
  rw [stage]
  apply merge_range
  · intro k hk
    simpa [sumCell,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (h.processed k hk).1
  · intro k hk
    simpa [differenceCell,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (h.processed k hk).2.1

theorem MergeProgress.normalized {initial table output : Nat → Nat} {start half stride : Nat}
    (h : MergeProgress initial table start half stride half output) :
    ∀k,k<2*half → NormalizedCell output (start+k) := by
  intro k hk
  by_cases low : k<half
  · exact (h.processed k low).2.2.1
  · have high : k-half<half := by omega
    have good:=(h.processed (k-half) high).2.2.2
    convert good using 1 <;> omega

#print axioms MergeProgress.merge_trace
#print axioms MergeProgress.normalized
end RH080Next.FFTPV.RecursiveSource
