import Log35Barrier640

namespace Ramanujan640.AnalyticBarrier
open Real Set Finset RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The exact4096-term harmonic sum used by the frozen gamma check. -/
lemma harmonic4096_bounds :
    (8895103896966/1000000000000:ℝ) ≤ (harmonic 4096 : ℝ) ∧
    (harmonic 4096 : ℝ) ≤ 8895103896967/1000000000000 := by
  norm_num [harmonic, Finset.sum_range_succ]

/-- Same .577,.578 bracket as the source; derived from the actual Mathlib
Euler constant and the frozen harmonic-sum order4096, not assumed. -/
theorem gamma_source_bracket :
    (577/1000:ℝ) < Real.eulerMascheroniConstant ∧
    Real.eulerMascheroniConstant < 578/1000 := by
  have hs := harmonic4096_bounds
  have hl := log_two_decimal
  have hid : Real.log (4096:ℝ) = 12*Real.log 2 := by
    rw [show (4096:ℝ) = 2^12 by norm_num, Real.log_pow]
    norm_num
  have hlogdiff : Real.log (4097:ℝ)-Real.log (4096:ℝ) ≤ 1/4096 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (4097/4096:ℝ))
    rw [Real.log_div (by norm_num) (by norm_num)] at h
    norm_num at h ⊢
    linarith
  have hlo : (harmonic 4096 : ℝ)-Real.log (4097:ℝ) < Real.eulerMascheroniConstant := by
    simpa only [Real.eulerMascheroniSeq,
      show ((4096:ℕ):ℝ)+1=(4097:ℝ) by norm_num]
      using Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 4096
  have hup : Real.eulerMascheroniConstant < (harmonic 4096 : ℝ)-Real.log (4096:ℝ) := by
    simpa [Real.eulerMascheroniSeq'] using Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 4096
  rw [hid] at hlogdiff hup
  constructor <;> linarith

#print axioms harmonic4096_bounds
#print axioms gamma_source_bracket
end Ramanujan640.AnalyticBarrier
