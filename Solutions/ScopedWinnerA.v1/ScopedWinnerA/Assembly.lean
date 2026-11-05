/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedWinnerA.Result
import ScopedWinnerA.Registered
namespace ScopedWinnerA
open Real IEANTN WinnerDirectKernel Comparison
set_option maxHeartbeats 0
section OriginalInputs
variable
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
include hCHJ hrvm hsmall hlow h hRH hQRH
/-- Existing v2 proof validates the incumbent on D under EXACTLY the same seven inputs.
No old-output or new-density/error oracle is an assumption. -/
theorem incumbent_valid {x : ℝ} (hx : domain x) : Eπ x ≤ oldEnvelope x := by
  rw [old_envelope_exact hx]
  have hx300 : exp (300:ℝ)≤x := (exp_le_exp.mpr (by norm_num)).trans hx.1
  have hb := WinnerDensityA.HeightRHFinal.source_pi_refined_exact
    hCHJ hrvm hsmall hlow h hRH hQRH x hx300
  simpa only [oldExact,scale,pow_zero,mul_one,
    show (7/8:ℝ)-1= -(1:ℝ)/8 by norm_num] using hb
/-- Every inventoried old allowance is legal on the scenario domain, with no extra hypothesis.
This does not assert the original larger-domain node contracts from these seven inputs. -/
theorem every_old_valid {x : ℝ} (hx : domain x) (i : Fin 37) : Eπ x ≤ incumbent x i := by
  have hp := incumbent_valid hCHJ hrvm hsmall hlow h hRH hQRH hx
  exact hp.trans (Finset.inf'_le (incumbent x) (Finset.mem_univ i))
/-- A complete subnetwork-snapshot demonstration: both actual mathematical bounds and
uniform strict comparison with the entire37-entry frozen allowance envelope. -/
theorem subnetwork_snapshot_winner {x : ℝ} (hx : domain x) :
    Eπ x ≤ newCap*scale x ∧ Eπ x ≤ oldEnvelope x ∧
      newCap*scale x+(298/100000000:ℝ)*scale x < oldEnvelope x := by
  constructor
  · have hx300 : exp (300:ℝ)≤x := (exp_le_exp.mpr (by norm_num)).trans hx.1
    have hn := pi_00947147 hCHJ hrvm hsmall hlow h hRH hQRH x hx300
    simpa only [newCap,scale,pow_zero,mul_one,
      show (7/8:ℝ)-1= -(1:ℝ)/8 by norm_num] using hn
  · exact ⟨incumbent_valid hCHJ hrvm hsmall hlow h hRH hQRH hx,scoped_strict hx⟩
end OriginalInputs
#print axioms incumbent_valid
#print axioms subnetwork_snapshot_winner
end ScopedWinnerA
