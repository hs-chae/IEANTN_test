/- Pure exact integer guards on the already kernel-verified word family. -/
import SynergyMomentMath.Real
namespace SynergyMomentMath.Bounds
open ScopedNumerical SynergyBasis SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
def guards (word : Int×Int) : Bool := decide
 (21600*ProofBox.scale 128 ≤ word.1 ∧ word.1 < (2:Int)^512 ∧
  77*ProofBox.scale 128 ≤ word.2 ∧ word.2 ≤ 163*ProofBox.scale 128)
theorem checked : SourceMomentWordsV1.All.words.all guards=true := by decide +kernel

theorem integer_bounds (i : Nat) (hi : i < 768) :
 21600*ProofBox.scale 128 ≤ (SourceMomentWordsV1.All.word i).1 ∧
 (SourceMomentWordsV1.All.word i).1 < (2:Int)^512 ∧
 77*ProofBox.scale 128 ≤ (SourceMomentWordsV1.All.word i).2 ∧
 (SourceMomentWordsV1.All.word i).2 ≤ 163*ProofBox.scale 128 := by
 have member : SourceMomentWordsV1.All.word i∈SourceMomentWordsV1.All.words :=
  List.mem_iff_getElem?.mpr ⟨i,SourceMomentWordsV1.All.word_get i hi⟩
 exact of_decide_eq_true ((List.all_eq_true.mp checked) _ member)

theorem d_range (i : Nat) (hi : i < 768) : 77 ≤ Real.dValue i ∧ Real.dValue i ≤ 163 := by
 have h:=(integer_bounds i hi).2.2
 have scalePos:=RealBox.scale_real_pos 128
 constructor
 · apply (le_div_iff₀ scalePos).mpr
   exact_mod_cast h.1
 · apply (div_le_iff₀ scalePos).mpr
   exact_mod_cast h.2

theorem c_nonnegative (i : Nat) (hi : i < 768) : 0 ≤ Real.cValue i := by
 have base:=(integer_bounds i hi).1
 have positive : (0:Int) ≤ 21600*ProofBox.scale 128 := by decide +kernel
 exact div_nonneg (by exact_mod_cast positive.trans base) (RealBox.scale_real_pos 128).le

theorem mass_nonnegative (i : Nat) (hi : i < 768) : 0 ≤ Real.mass i := by
 have pos : (0:ℝ) < heightEndpoint i := Real.exp_pos _
 have order : 1/heightEndpoint (i+1) ≤ 1/heightEndpoint i :=
  one_div_le_one_div_of_le pos (heightEndpoint_monotone (Nat.le_succ i))
 exact mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
   (mul_nonneg (sub_nonneg.mpr order) (c_nonnegative i hi))
#print axioms checked
#print axioms integer_bounds
#print axioms d_range
#print axioms c_nonnegative
#print axioms mass_nonnegative
end
end SynergyMomentMath.Bounds
