/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveCallParameters
import FFTCanonicalSourceFinal
import FFTTraceChecker
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

/-- Exact arithmetic invariants of the original recursive source call.
These are index/extent conditions, not execution or numerical-output oracles. -/
structure IndexShape (start index step n total : Nat) : Prop where
  positive : 0 < n
  step_positive : 0 < step
  output : start+n ≤ total
  index : index < step
  stride : step*n = total
  total_small : total ≤ 2^24

theorem IndexShape.scalar_bounds {start index step n total : Nat}
    (h : IndexShape start index step n total) :
    start < 2^64 ∧ index < 2^64 ∧ step < 2^64 ∧ n < 2^64 ∧ total < 2^64 := by
  have hn := h.positive
  have hs := h.step_positive
  have hp := h.stride
  have ht := h.total_small
  have hsn := h.output
  have hi := h.index
  have sb : step ≤ total := by nlinarith
  have nb : n ≤ total := by nlinarith
  omega

theorem IndexShape.children {start index step n total half : Nat}
    (h : IndexShape start index step n total) (split : n = 2*half) (positive : 0 < half) :
    IndexShape start index (step*2) half total ∧
    IndexShape (start+half) (index+step) (step*2) half total := by
  have hp := h.stride
  have hs := h.step_positive
  have hi := h.index
  have ho := h.output
  have product : step*2*half = total := by rw [Nat.mul_assoc,←split];exact hp
  constructor
  · exact ⟨positive,by omega,by omega,by omega,product,h.total_small⟩
  · exact ⟨positive,by omega,by omega,by omega,product,h.total_small⟩

theorem IndexShape.stride_exact {start index step n total : Nat}
    (h : IndexShape start index step n total) : total/n = step := by
  rw [←h.stride,Nat.mul_div_left _ h.positive]

theorem IndexShape.source_offsets {start index step n total : Nat}
    (h : IndexShape start index step n total) :
    12*start+12*n ≤ 12*total ∧ 12*index+12 ≤ 12*total ∧
    12*total < 2^64 := by
  have ho := h.output
  have hp := h.stride
  have hn := h.positive
  have hs := h.step_positive
  have hi := h.index
  have ht := h.total_small
  have sb : step ≤ total := by nlinarith
  omega

/-- Each stored complex cell is the actual two signed base-billion values.
The integer model receives these values, not an assumed initialized FFT state. -/
def cell (data : Nat → Nat) (k : Nat) : FFT.IntegerModel.CInt :=
  (CanonicalSource.represented data (12*k), CanonicalSource.represented data (12*k+6))

def NormalizedCell (data : Nat → Nat) (k : Nat) : Prop :=
  (∀c : Fin 2, ∀j, j < 5 → data (12*k+6*c.val+j) < 1000000000) ∧
  ∀c : Fin 2, data (12*k+6*c.val+5) ≤ 1

/-- The actual stride-selected global table at each recursive level. -/
def stages (table : Nat → Nat) (total s : Nat) : List FFT.IntegerModel.CInt :=
  if s=0 then [] else (List.range (2^(s-1))).map (fun j => cell table (j*(total/2^s)))

#print axioms IndexShape.children
#print axioms IndexShape.source_offsets
end RH080Next.FFTPV.RecursiveSource
