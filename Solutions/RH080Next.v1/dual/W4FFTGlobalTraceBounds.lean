/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTGlobalTraceBounds
import FFT24Bridge
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFT.IntegerModel
/-- All recorded N24 stage twiddles inherit the global C-table error. The
single extra recurrence value used in the analytic bound is a mathematical
extension, never an assertion that C reads beyond the allocated table. -/
theorem stage24_bounds (seed : CInt) (rest : List CInt) (stages : Nat → List CInt)
    (hlen : ((unit,0)::rest).length=8388608)
    (hseed : decode seed=rootSeed)
    (htrace : TwiddleTrace seed (unit,0) rest)
    (hchain : ∀ t<24, DecimationTrace (24-(t+1)) ((unit,0)::rest) (stages (t+1))) :
    ∀ t<24, ∀ j<2^t,
      ‖decode ((stages (t+1)).getD j (0,0))-negativeRoot (2*2^t)^j‖≤
        (1/10000000000000000000:ℝ) := by
  let z : Nat → ℂ := fun j => decode (extendTable seed ((unit,0)::rest) j)
  have hz : z 0=1 := decodedTable_start seed rest
  have hstep : ∀ j<8388608, ‖z (j+1)-rootSeed*z j‖≤
      (4/1000000000000000000000000000000000000:ℝ) := by
    intro j hj
    have h := decodedTable_step seed (unit,0) rest htrace j (by omega)
    rw [hseed] at h
    simpa [z,unit] using h
  have hglobal := globalTwiddle24_bound z hz hstep
  intro t ht j hj
  rw [decoded_stage_entry 24 t j (by omega) ht hj seed rest stages
    (by norm_num; exact hlen) (hchain t ht)]
  exact hglobal t ht j hj

theorem ExecutionTrace.error24 {stages : Nat → List CInt} {input : Nat → CInt}
    {out : List CInt} (h : ExecutionTrace stages input 24 0 1 out)
    (seed : CInt) (rest : List CInt)
    (hlen : ((unit,0)::rest).length=8388608)
    (hseed : decode seed=rootSeed)
    (htrace : TwiddleTrace seed (unit,0) rest)
    (hchain : ∀ t<24, DecimationTrace (24-(t+1)) ((unit,0)::rest) (stages (t+1)))
    (hmass : coefficientMass 16777216 (fun j => decode (input j))≤362)
    (k : Nat) (hk : k<16777216) :
    ‖decode (out.getD k (0,0))-
      dftSum 16777216 k (negativeRoot 16777216) (fun j => decode (input j))‖≤
        (1/100000000000000:ℝ) := by
  exact h.dft_error_of_mass (1/10000000000000000000) 362 (1/100000000000000)
    (by norm_num) (stage24_bounds seed rest stages hlen hseed htrace hchain) hmass
    (by norm_num [unit]) k hk

#print axioms stage24_bounds
#print axioms ExecutionTrace.error24
end RH080Next.FFT.IntegerModel
