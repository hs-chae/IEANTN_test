/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedWinnerA.Mapped
namespace ScopedWinnerA.Coverage
open Real IEANTN WinnerDirectKernel Comparison
set_option maxHeartbeats 0
/-- All39 written output identities. Last two are public aliases of existing slots30/31.
Nothing is removed from the original37-entry vector. -/
def slot (i : Fin 39) : Fin 37 :=
  if h : i.val<37 then ⟨i.val,h⟩ else if i.val=37 then 30 else 31
noncomputable def allowance (x : ℝ) (i : Fin 39) : ℝ := incumbent x (slot i)
noncomputable def envelope (x : ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty (allowance x)
/-- Both newly noticed aliases represent their original exact power allowances. -/
theorem alias_values (x : ℝ) :
    allowance x 37=(0.009898:ℝ)*scale x ∧ allowance x 38=(0.009830:ℝ)*scale x := by
  constructor <;> rfl
/-- Including the missing source identities leaves the mathematical minimum unchanged. -/
theorem envelope_exact {x : ℝ} (hx : domain x) : envelope x=oldExact*scale x := by
  apply le_antisymm
  · exact Finset.inf'_le (allowance x) (Finset.mem_univ (23:Fin 39))
  · apply Finset.le_inf' Finset.univ_nonempty (allowance x)
    intro i _
    exact incumbent_lower hx (slot i)
/-- Final scoped winner covers39 source identities and consumes all18 actual contract mappings. -/
theorem winner
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
    {x : ℝ} (hx : domain x) :
    (Eπ x ≤ newCap*scale x ∧ Eπ x ≤ envelope x ∧
      newCap*scale x+(298/100000000:ℝ)*scale x < envelope x) ∧
    (∀ i : Fin 18, registeredContract i →
      Eπ x ≤ incumbent x (Fin.castLE (by decide : 18≤37) i)) := by
  have hp := mapped_snapshot_winner hCHJ hrvm hsmall hlow h hRH hQRH hx
  have he : envelope x=oldEnvelope x := (envelope_exact hx).trans (old_envelope_exact hx).symm
  simpa only [he] using hp
#print axioms alias_values
#print axioms envelope_exact
#print axioms winner
end ScopedWinnerA.Coverage
