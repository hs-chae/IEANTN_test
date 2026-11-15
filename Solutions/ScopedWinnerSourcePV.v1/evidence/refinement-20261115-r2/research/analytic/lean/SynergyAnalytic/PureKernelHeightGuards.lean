/- Cheap table-only guards for the existing accepted kernel-only height algorithm.
No C AST, source execution, framed point or observed-output module is imported. -/
import SynergyAnalytic.HeightPNTInstance
namespace SynergyAnalytic.HeightPoint.PureKernelHeightGuards
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem all_word_guards : (List.range logCellCount).all (fun i=>
    decide (0 ≤ dataC i ∧ 77*scale p ≤ dataD i ∧ dataD i ≤ 163*scale p))=true := by
  decide +kernel

theorem word_guards {i : Nat} (hi : i < logCellCount) :
    0 ≤ dataC i ∧ 77*scale p ≤ dataD i ∧ dataD i ≤ 163*scale p :=
  of_decide_eq_true ((List.all_eq_true.mp all_word_guards) i (List.mem_range.mpr hi))

theorem integer_real_guards {c d : Int}
    (checked : 0 ≤ c ∧ 77*scale p ≤ d ∧ d ≤ 163*scale p) :
    0 ≤ (c:ℝ)/(scale p:ℝ) ∧
      77 ≤ (d:ℝ)/(scale p:ℝ) ∧ (d:ℝ)/(scale p:ℝ) ≤ 163 := by
  have low : (77:ℝ)*(scale p:ℝ) ≤ (d:ℝ) := by exact_mod_cast checked.2.1
  have high : (d:ℝ) ≤ (163:ℝ)*(scale p:ℝ) := by exact_mod_cast checked.2.2
  exact ⟨div_nonneg (by exact_mod_cast checked.1) (RealBox.scale_real_pos p).le,
    (le_div_iff₀ (RealBox.scale_real_pos p)).mpr low,
    (div_le_iff₀ (RealBox.scale_real_pos p)).mpr high⟩

theorem c_nonnegative {i : Nat} (hi : i < logCellCount) : 0 ≤ cValue i :=
  (integer_real_guards (c:=dataC i) (d:=dataD i) (word_guards hi)).1

theorem slope_range {i : Nat} (hi : i < logCellCount) :
    77 ≤ DValue i ∧ DValue i ≤ 163 :=
  (integer_real_guards (c:=dataC i) (d:=dataD i) (word_guards hi)).2

theorem weights_nonnegative : ∀ i < logCellCount,
    0 ≤ (1/heightEndpoint i-1/heightEndpoint (i+1))*cValue i := by
  intro i hi
  have first : 0 < heightEndpoint 0 := by rw [heightEndpoint_zero];norm_num [WinnerOriginalScalars.height]
  have difference : 0 ≤ 1/heightEndpoint i-1/heightEndpoint (i+1) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le
      (first.trans_le (heightEndpoint_monotone (Nat.zero_le i)))
      (heightEndpoint_monotone (Nat.le_succ i)))
  exact mul_nonneg difference (c_nonnegative hi)

#print axioms all_word_guards
#print axioms word_guards
#print axioms integer_real_guards
#print axioms c_nonnegative
#print axioms slope_range
#print axioms weights_nonnegative
end SynergyAnalytic.HeightPoint.PureKernelHeightGuards
