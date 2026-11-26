/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTraceTwiddles
import FFT17Bridge

set_option autoImplicit false
noncomputable section
namespace RH080Next.FFT.IntegerModel

theorem ExecutionTrace.dft_error_of_mass {stages : Nat → List CInt} {input : Nat → CInt}
    {s : Nat} {out : List CInt} (h : ExecutionTrace stages input s 0 1 out)
    (eta M error : ℝ) (heta : 0≤eta)
    (hw : ∀ t<s, ∀ j<2^t,
      ‖decode ((stages (t+1)).getD j (0,0))-negativeRoot (2*2^t)^j‖≤eta)
    (hmass : coefficientMass (2^s) (fun j => decode (input j))≤M)
    (hbudget : ((1+eta)^s-1)*M+((2:ℝ)^s-1)*(1+eta)^s*(4/(unit:ℝ))≤error)
    (k : Nat) (hk : k<2^s) :
    ‖decode (out.getD k (0,0))-
      dftSum (2^s) k (negativeRoot (2^s)) (fun j => decode (input j))‖≤error := by
  have hbase := h.dft_error eta heta hw k hk
  simp only [Nat.zero_add,Nat.one_mul] at hbase
  have hp : 0≤(1+eta)^s-1 := by
    have := one_le_pow₀ (n := s) (by linarith : (1:ℝ)≤1+eta)
    linarith
  have hm := mul_le_mul_of_nonneg_left hmass hp
  exact hbase.trans (by linarith)

/-- All recorded N17 stage twiddles inherit the global C-table error. The
single extra recurrence value used in the analytic bound is a mathematical
extension, never an assertion that C reads beyond the allocated table. -/
theorem stage17_bounds (seed : CInt) (rest : List CInt) (stages : Nat → List CInt)
    (hlen : ((unit,0)::rest).length=65536)
    (hseed : decode seed=rootSeed17)
    (htrace : TwiddleTrace seed (unit,0) rest)
    (hchain : ∀ t<17, DecimationTrace (17-(t+1)) ((unit,0)::rest) (stages (t+1))) :
    ∀ t<17, ∀ j<2^t,
      ‖decode ((stages (t+1)).getD j (0,0))-negativeRoot (2*2^t)^j‖≤
        (1/100000000000000000000:ℝ) := by
  let z : Nat → ℂ := fun j => decode (extendTable seed ((unit,0)::rest) j)
  have hz : z 0=1 := decodedTable_start seed rest
  have hstep : ∀ j<65536, ‖z (j+1)-rootSeed17*z j‖≤
      (4/1000000000000000000000000000000000000:ℝ) := by
    intro j hj
    have h := decodedTable_step seed (unit,0) rest htrace j (by omega)
    rw [hseed] at h
    simpa [z,unit] using h
  have hglobal := globalTwiddle17_bound z hz hstep
  intro t ht j hj
  rw [decoded_stage_entry 17 t j (by omega) ht hj seed rest stages
    (by norm_num; exact hlen) (hchain t ht)]
  exact hglobal t ht j hj

theorem ExecutionTrace.error17 {stages : Nat → List CInt} {input : Nat → CInt}
    {out : List CInt} (h : ExecutionTrace stages input 17 0 1 out)
    (seed : CInt) (rest : List CInt)
    (hlen : ((unit,0)::rest).length=65536)
    (hseed : decode seed=rootSeed17)
    (htrace : TwiddleTrace seed (unit,0) rest)
    (hchain : ∀ t<17, DecimationTrace (17-(t+1)) ((unit,0)::rest) (stages (t+1)))
    (hmass : coefficientMass 131072 (fun j => decode (input j))≤81)
    (k : Nat) (hk : k<131072) :
    ‖decode (out.getD k (0,0))-
      dftSum 131072 k (negativeRoot 131072) (fun j => decode (input j))‖≤
        (1/50000000000000000:ℝ) := by
  exact h.dft_error_of_mass (1/100000000000000000000) 81 (1/50000000000000000)
    (by norm_num) (stage17_bounds seed rest stages hlen hseed htrace hchain) hmass
    (by norm_num [unit]) k hk

#print axioms stage17_bounds
#print axioms ExecutionTrace.error17
end RH080Next.FFT.IntegerModel
