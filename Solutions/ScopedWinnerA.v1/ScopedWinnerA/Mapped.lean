/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedWinnerA.Assembly
namespace ScopedWinnerA
open Real IEANTN WinnerDirectKernel Comparison
/-- Export the mathematical winner together with the checked correspondence from all18
actual imported registered contracts to their frozen allowance-vector entries.
The original registered contracts are conditional conclusions here, not new assumptions. -/
theorem mapped_snapshot_winner
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
    {x : ℝ} (hx : domain x) :
    (Eπ x ≤ newCap*scale x ∧ Eπ x ≤ oldEnvelope x ∧
      newCap*scale x+(298/100000000:ℝ)*scale x < oldEnvelope x) ∧
    (∀ i : Fin 18, registeredContract i →
      Eπ x ≤ incumbent x (Fin.castLE (by decide : 18≤37) i)) := by
  exact ⟨subnetwork_snapshot_winner hCHJ hrvm hsmall hlow h hRH hQRH hx,
    fun i hi => registered_output_restriction hx i hi⟩
#print axioms mapped_snapshot_winner
end ScopedWinnerA
