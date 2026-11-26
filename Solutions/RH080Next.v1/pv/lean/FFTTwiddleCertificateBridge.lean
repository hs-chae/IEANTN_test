/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTwiddleSourceFinal
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.TwiddleSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

/-- The independent operational table certificate determines the same exact
integer recurrence as the source constructor. This is a mathematical bridge,
not a relabeling of certificate checking as source verification. -/
theorem trace_entry {seed : FFT.IntegerModel.CInt} {rest : List FFT.IntegerModel.CInt}
    (trace : FFT.IntegerModel.TwiddleTrace seed (FFT.IntegerModel.unit,0) rest)
    (k : Nat) (inside : k<((FFT.IntegerModel.unit,0)::rest).length) :
    ((FFT.IntegerModel.unit,0)::rest).getD k (0,0)=sequence seed k := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [trace.getD_step k (by simpa using inside),ih (by omega)]
    rfl

/-- Every table entry used by the real recursive C program agrees with the
literal independently kernel-verified table, after the actual C constructor
has established its View. No observed table is assumed. -/
theorem source_table_matches_trace {F : Type} {state : State F}
    {tableObject workObject n owner : Nat} {ids : Var→Nat} {tableData workData : Nat→Nat}
    {seed : FFT.IntegerModel.CInt}
    (h : View state tableObject workObject n ids owner (n/2) tableData workData seed)
    {rest : List FFT.IntegerModel.CInt}
    (trace : FFT.IntegerModel.TwiddleTrace seed (FFT.IntegerModel.unit,0) rest)
    (length : ((FFT.IntegerModel.unit,0)::rest).length=n/2) (k : Nat) (inside : k<n/2) :
    ComplexSource.pair tableData (k*12)=((FFT.IntegerModel.unit,0)::rest).getD k (0,0) := by
  exact (h.tableValues k inside).trans (trace_entry trace k (by omega)).symm

#print axioms trace_entry
#print axioms source_table_matches_trace
end RH080Next.FFTPV.TwiddleSource
