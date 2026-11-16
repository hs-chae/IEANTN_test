import SynergyAnalytic.ExpHorner
namespace SynergyAnalytic
set_option maxHeartbeats 0

/-- Every exact intermediate of the descending divided-Horner loop stays in
[0,1]. Thus the source's positive-subtraction clamp does not alter the ideal
real polynomial; directed-rounding effects are a separate obligation. -/
theorem expHorner_range (n k : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ expHorner n k z ∧ expHorner n k z ≤ 1 := by
  induction n generalizing k with
  | zero => simp [expHorner]
  | succ n ih =>
    have hh := ih (k+1)
    have hk : (1:ℝ) ≤ (k:ℝ)+1 := by have h := (show (0:ℝ) ≤ k from Nat.cast_nonneg k); linarith
    have hd : 0 < (k:ℝ)+1 := by positivity
    have hc0 : 0 ≤ z/((k:ℝ)+1) := div_nonneg hz hd.le
    have hc1 : z/((k:ℝ)+1) ≤ 1 := (div_le_one hd).2 (hz1.trans hk)
    change 0 ≤ 1-z/((k:ℝ)+1)*expHorner n (k+1) z ∧
      1-z/((k:ℝ)+1)*expHorner n (k+1) z ≤ 1
    have hp0 := mul_nonneg hc0 hh.1
    have hp1 := mul_le_one₀ hc1 hh.1 hh.2
    constructor <;> linarith

#print axioms expHorner_range
end SynergyAnalytic
