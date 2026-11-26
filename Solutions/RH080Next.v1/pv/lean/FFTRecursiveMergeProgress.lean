/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyBlock
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource

def sumCell (initial table : Nat → Nat) (start half stride r : Nat) : FFT.IntegerModel.CInt :=
  FFT.IntegerModel.add (cell initial (start+r))
    (FFT.IntegerModel.mul (cell initial (start+r+half)) (cell table (r*stride)))
def differenceCell (initial table : Nat → Nat) (start half stride r : Nat) : FFT.IntegerModel.CInt :=
  FFT.IntegerModel.sub (cell initial (start+r))
    (FFT.IntegerModel.mul (cell initial (start+r+half)) (cell table (r*stride)))

theorem normalized_congr {a b : Nat → Nat} {i j : Nat}
    (words : ∀k,k<12 → a (12*i+k)=b (12*j+k)) (good : NormalizedCell b j) : NormalizedCell a i := by
  constructor
  · intro c k hk
    have same:=words (6*c.val+k) (by have bound:=c.isLt;omega)
    simpa only [Nat.add_assoc] using same.trans_lt (by simpa only [Nat.add_assoc] using good.1 c k hk)
  · intro c
    have same:=words (6*c.val+5) (by have bound:=c.isLt;omega)
    simpa only [Nat.add_assoc] using same.trans_le (by simpa only [Nat.add_assoc] using good.2 c)

/-- A row-based invariant over the real output words. No final output is a
premise: processed rows have derived integer values, unprocessed rows retain
the original child outputs word-for-word, and all other output words persist. -/
structure MergeProgress (initial table : Nat → Nat) (start half stride j : Nat) (output : Nat → Nat) : Prop where
  processed : ∀r,r<j →
    cell output (start+r)=sumCell initial table start half stride r ∧
    cell output (start+r+half)=differenceCell initial table start half stride r ∧
    NormalizedCell output (start+r) ∧ NormalizedCell output (start+r+half)
  unprocessed : ∀r,j≤r → r<half → ∀k,k<12 →
    output (12*(start+r)+k)=initial (12*(start+r)+k) ∧
    output (12*(start+r+half)+k)=initial (12*(start+r+half)+k)
  outside : ∀k,(k<start*12 ∨ (start+2*half)*12≤k) → output k=initial k

theorem MergeProgress.zero (initial table : Nat → Nat) (start half stride : Nat) :
    MergeProgress initial table start half stride 0 initial :=
  ⟨by intro r impossible;omega,by intro r lo hi k hk;exact ⟨rfl,rfl⟩,by intro k hk;rfl⟩

/-- The two source cell footprints preserve every different complete cell. -/
theorem two_cells_other {before after : Nat → Nat} {a b target : Nat}
    (outside : ∀k,(k<a*12 ∨ a*12+12≤k) → (k<b*12 ∨ b*12+12≤k) → after k=before k)
    (da : target≠a) (db : target≠b) : ∀k,k<12 → after (12*target+k)=before (12*target+k) := by
  intro k hk
  exact outside _ (by omega) (by omega)

theorem MergeProgress.next {initial table output next : Nat → Nat} {start half stride j : Nat}
    (h : MergeProgress initial table start half stride j output) (active : j<half)
    (left : cell next (start+j)=sumCell output table start half stride j)
    (right : cell next (start+j+half)=differenceCell output table start half stride j)
    (leftGood : NormalizedCell next (start+j)) (rightGood : NormalizedCell next (start+j+half))
    (outside : ∀k,(k<(start+j)*12 ∨ (start+j)*12+12≤k) →
      (k<(start+j+half)*12 ∨ (start+j+half)*12+12≤k) → next k=output k) :
    MergeProgress initial table start half stride (j+1) next := by
  have unprocessed:=h.unprocessed j (le_refl _) active
  have leftOld:=cell_congr (fun k hk => (unprocessed k hk).1)
  have rightOld:=cell_congr (fun k hk => (unprocessed k hk).2)
  have oldLeft : sumCell output table start half stride j=sumCell initial table start half stride j := by
    simp only [sumCell,leftOld,rightOld]
  have oldRight : differenceCell output table start half stride j=differenceCell initial table start half stride j := by
    simp only [differenceCell,leftOld,rightOld]
  refine ⟨?_,?_,?_⟩
  · intro r hr
    by_cases same : r=j
    · subst r;exact ⟨left.trans oldLeft,right.trans oldRight,leftGood,rightGood⟩
    · have previous:=h.processed r (by omega)
      have wl:=two_cells_other outside (target:=start+r) (by omega) (by omega)
      have wr:=two_cells_other outside (target:=start+r+half) (by omega) (by omega)
      exact ⟨(cell_congr wl).trans previous.1,(cell_congr wr).trans previous.2.1,
        normalized_congr wl previous.2.2.1,normalized_congr wr previous.2.2.2⟩
  · intro r lo hi k hk
    have previous:=h.unprocessed r (by omega) hi k hk
    have wl:=two_cells_other outside (target:=start+r) (by omega) (by omega)
    have wr:=two_cells_other outside (target:=start+r+half) (by omega) (by omega)
    exact ⟨(wl k hk).trans previous.1,(wr k hk).trans previous.2⟩
  · intro k hk
    exact (outside k (by omega) (by omega)).trans (h.outside k hk)

#print axioms MergeProgress.next
end RH080Next.FFTPV.RecursiveSource
