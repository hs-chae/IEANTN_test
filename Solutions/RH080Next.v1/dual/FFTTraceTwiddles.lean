/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTIntegerInterpretation

set_option autoImplicit false
noncomputable section
namespace RH080Next.FFT.IntegerModel

theorem TwiddleTrace.getD_step {seed previous : CInt} {rest : List CInt}
    (h : TwiddleTrace seed previous rest) (j : Nat) (hj : j<rest.length) :
    (previous::rest).getD (j+1) (0,0)=mul ((previous::rest).getD j (0,0)) seed := by
  induction h generalizing j with
  | nil previous => simp at hj
  | cons previous current rest hc tail ih =>
    cases j with
    | zero => simpa using hc
    | succ j => simpa using ih j (by simpa using hj)

/-- One mathematical recurrence extension past the allocated C table. This
extra value is never identified with an out-of-bounds C memory read. -/
def extendTable (seed : CInt) (table : List CInt) (j : Nat) : CInt :=
  if j<table.length then table.getD j (0,0) else mul (table.getD (j-1) (0,0)) seed

theorem extendTable_step (seed previous : CInt) (rest : List CInt)
    (h : TwiddleTrace seed previous rest) (j : Nat) (hj : j<(previous::rest).length) :
    extendTable seed (previous::rest) (j+1)=mul (extendTable seed (previous::rest) j) seed := by
  rw [extendTable,extendTable,if_pos hj]
  by_cases hh : j+1<(previous::rest).length
  · rw [if_pos hh]
    exact h.getD_step j (by simpa using hh)
  · rw [if_neg hh]
    simp

theorem decodedTable_start (seed : CInt) (rest : List CInt) :
    decode (extendTable seed ((unit,0)::rest) 0)=1 := by
  simpa [extendTable] using decode_unit

theorem decodedTable_step (seed previous : CInt) (rest : List CInt)
    (h : TwiddleTrace seed previous rest) (j : Nat) (hj : j<(previous::rest).length) :
    ‖decode (extendTable seed (previous::rest) (j+1))-
      decode seed*decode (extendTable seed (previous::rest) j)‖≤4/(unit:ℝ) := by
  rw [extendTable_step _ _ _ h j hj,decode_mul,roundedComplex_comm]
  exact roundedComplex_error _ _

/-- Repeated exact decimation; no re-squared approximate roots are used. -/
inductive DecimationTrace : Nat → List CInt → List CInt → Prop
  | refl (as : List CInt) : DecimationTrace 0 as as
  | cons (n : Nat) (as bs cs : List CInt) (even : EvenTrace as bs)
      (tail : DecimationTrace n bs cs) : DecimationTrace (n+1) as cs

theorem DecimationTrace.getD {n : Nat} {as bs : List CInt}
    (h : DecimationTrace n as bs) (j : Nat) :
    bs.getD j (0,0)=as.getD (2^n*j) (0,0) := by
  induction h with
  | refl as => simp
  | cons n as bs cs even tail ih =>
    rw [ih,even.getD]
    congr 1
    rw [Nat.pow_succ]
    ring

/-- Exact globally-strided entry used by a stage of the C recursion. -/
theorem decoded_stage_entry (S t j : Nat) (hS : 0<S) (ht : t<S) (hj : j<2^t)
    (seed : CInt) (rest : List CInt) (stages : Nat → List CInt)
    (hlen : ((unit,0)::rest).length=2^(S-1))
    (chain : DecimationTrace (S-(t+1)) ((unit,0)::rest) (stages (t+1))) :
    decode ((stages (t+1)).getD j (0,0))=
      decode (extendTable seed ((unit,0)::rest) (j*2^(S-(t+1)))) := by
  have hp : (2:Nat)^t*2^(S-(t+1))=2^(S-1) := by
    rw [←Nat.pow_add]
    congr 1
    omega
  have hb : j*2^(S-(t+1))<((unit,0)::rest).length := by
    rw [hlen,←hp]
    exact Nat.mul_lt_mul_of_pos_right hj (Nat.pow_pos (by decide))
  rw [extendTable,if_pos hb,chain.getD]
  congr 2
  ring

/-- The existing analytic FFT error theorem is genuinely consumed by the
integer execution relation, with every decoded multiplication discharged. -/
theorem ExecutionTrace.dft_error {stages : Nat → List CInt} {input : Nat → CInt}
    {s index step : Nat} {out : List CInt} (h : ExecutionTrace stages input s index step out)
    (eta : ℝ) (heta : 0≤eta)
    (hw : ∀ t<s, ∀ j<2^t,
      ‖decode ((stages (t+1)).getD j (0,0))-negativeRoot (2*2^t)^j‖≤eta)
    (k : Nat) (hk : k<2^s) :
    ‖decode (out.getD k (0,0))-
      dftSum (2^s) k (negativeRoot (2^s)) (fun j => decode (input (index+step*j)))‖≤
      ((1+eta)^s-1)*coefficientMass (2^s) (fun j => decode (input (index+step*j)))+
        ((2:ℝ)^s-1)*(1+eta)^s*(4/(unit:ℝ)) := by
  rw [h.decode_roundedFFT k hk]
  exact roundedFFT_dft_error s _ k hk _ roundedComplex eta (4/(unit:ℝ)) heta
    (by norm_num [unit]) hw roundedComplex_error

#print axioms extendTable_step
#print axioms decodedTable_step
#print axioms DecimationTrace.getD
#print axioms decoded_stage_entry
#print axioms ExecutionTrace.dft_error
end RH080Next.FFT.IntegerModel
