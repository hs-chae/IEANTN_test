/- Canonical exact suffix interface. Finite execution providers remain separate. -/
import SynergyMomentCHi.BudgetProposed
import SourceMomentSumsV1.Data
namespace SynergyMomentCHi.FamilyAPI
open ScopedC ScopedC.Machine ScopedNumerical SynergyMomentC
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
noncomputable section
def stat : Kind→SynergyMomentMath.Cells.Stat
 | .mass=>.mass
 | .firstMoment=>.firstMoment
def total (kind : Kind) (i : Nat) : ProofBox := SourceMomentSumsV1.Data.total (stat kind) i
def c (i : Nat) (lo : Int) : ProofBox :=
 ⟨lo,(SourceMomentWordsV1.All.word i).1-21600*ProofBox.scale 128⟩
def d (i : Nat) (lo : Int) : ProofBox := ⟨lo,(SourceMomentWordsV1.All.word i).2⟩
abbrev ExactRow (kind : Kind) (i : Nat) : Prop := ∀ cLo dLo : Int,
 Budget.run kind (total kind i) i (c i cLo) (d i dLo)=some
  (.continuing (BudgetProposed.afterProposed (total kind i) (total kind (i+1)) i
    (c i cLo) (d i dLo)))
theorem zero (kind : Kind) : total kind 0=⟨0,0⟩ := SourceMomentSumsV1.Data.zero (stat kind)
#print axioms zero
end
end SynergyMomentCHi.FamilyAPI
