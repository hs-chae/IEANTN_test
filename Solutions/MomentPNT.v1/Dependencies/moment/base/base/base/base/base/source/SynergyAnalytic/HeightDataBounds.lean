import SynergyAnalytic.HeightBudgetSound
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kernel_D_domain : (List.range logCellCount).all (fun i=>
    decide (0 ≤ dataD i ∧ dataD i < 330*scale p))=true := by decide +kernel

theorem D_domain (i:Nat) (hi:i<logCellCount) : 0 ≤ DValue i ∧ DValue i<330 := by
  have hd := (List.all_eq_true.mp kernel_D_domain) i (List.mem_range.mpr hi)
  have hwords : 0 ≤ dataD i ∧ dataD i < 330*scale p := of_decide_eq_true hd
  have h0 : (0:ℝ) ≤ (dataD i:ℝ) := by exact_mod_cast hwords.1
  have h1 : (dataD i:ℝ) < 330*(scale p:ℝ) := by exact_mod_cast hwords.2
  exact ⟨div_nonneg h0 (RealBox.scale_real_pos p).le,
    (div_lt_iff₀ (RealBox.scale_real_pos p)).mpr h1⟩

#print axioms kernel_D_domain
#print axioms D_domain
end SynergyAnalytic.HeightPoint
