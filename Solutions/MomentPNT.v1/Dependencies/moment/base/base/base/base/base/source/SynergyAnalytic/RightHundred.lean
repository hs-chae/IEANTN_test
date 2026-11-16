import SynergyAnalytic.CoarseElementary
namespace SynergyAnalytic
open Real WinnerOriginalScalars WinnerBetaA.HeightSource
set_option maxHeartbeats 0

/-- Coarse right-line allowance for the analytic far tail. This deliberately
uses gamma≤1 and elementary bounds; no numerical scalar checker is needed. -/
theorem right_hundred : WinnerBetaA.HeightSource.rightV (289/500) (3599/10000) height ≤ 100 := by
  let de : ℝ := 3599/10000
  have hd : 0<de := by norm_num [de]
  have hl : 28 ≤ Real.log height := source_log_ge28 le_rfl
  have hlp : 0<Real.log height := by linarith
  have hm0 : 0 ≤ sourceM0 := source_mzero_pos.le
  have hm : sourceM0 ≤ 2 := sourceM0_le_two
  have hp0 : 0 ≤ Real.pi := Real.pi_pos.le
  have hp : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hH : (1000:ℝ) ≤ height := by norm_num [height]
  have hH0 : 0<height := by norm_num [height]
  have hratio : 1+2*de/Real.log height ≤ (11/10:ℝ) := by
    have hh : 2*de/Real.log height ≤ (1/10:ℝ) := (div_le_iff₀ hlp).mpr (by dsimp [de];linarith)
    linarith
  have hratio1 : 1+de/Real.log height ≤ (11/10:ℝ) := by
    have hh : de/Real.log height ≤ (1/10:ℝ) := (div_le_iff₀ hlp).mpr (by dsimp [de];linarith)
    linarith
  have he : Real.exp (2*de/Real.log height) ≤ 2 := exp_half_le_two
    ((div_le_iff₀ hlp).mpr (by dsimp [de];linarith))
  have he2 : Real.exp (-2*de) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he1 : 1 ≤ Real.exp de := Real.one_le_exp hd.le
  have h5 : rightFive 1 de height ≤ 16 := by
    unfold rightFive
    simp only [mul_one]
    calc
      _ ≤ (4:ℝ)*2*(529/1000)/(2*de)*(11/10)^2*2 := by gcongr
      _ ≤ 16 := by norm_num [de]
  have h6 : rightSix de height ≤ 1 := by
    unfold rightSix
    calc
      _ ≤ (529/1000:ℝ)/(5*de*1)*(11/10)^2+(121/200)*1/28^2 := by gcongr
      _ ≤ 1 := by norm_num [de]
  have hsqrt : (2/5:ℝ) ≤ Real.sqrt (2*(601/5000:ℝ)) := by
    exact (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 2/5) (by norm_num : (0:ℝ) ≤ 2*(601/5000))).2 (by norm_num)
  have hpiS : Real.sqrt Real.pi ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num,by nlinarith [hp]⟩
  have hev : Real.exp (2*(601/5000:ℝ)*((1+de/Real.log height)/height)^2) ≤ 2 := by
    apply exp_half_le_two
    have hi : (1+de/Real.log height)/height ≤ (11/10:ℝ)/1000 := by gcongr
    have hi0 : 0 ≤ (1+de/Real.log height)/height := by positivity
    have hi2 := pow_le_pow_left₀ hi0 hi 2
    nlinarith
  have hr : WinnerBetaA.HeightSource.rightV 1 de height ≤ 100 := by
    unfold WinnerBetaA.HeightSource.rightV
    calc
      _ ≤ 8*(601/5000:ℝ)*2*((16+1*4*2/1000)/(4*(601/5000))+
          1*2/(8*(601/5000)*(2/5))) := by
        have h5p : 0 ≤ rightFive 1 de height := rightFive_nonneg hd
        have h6p : 0 ≤ rightSix de height := rightSix_nonneg hd
        have hb1 : (rightFive 1 de height+rightSix de height*Real.pi*sourceM0/height)/(4*(601/5000:ℝ)) ≤
            (16+1*4*2/1000)/(4*(601/5000:ℝ)) := by gcongr
        have hb2 : rightSix de height*Real.sqrt Real.pi/(8*(601/5000:ℝ)*Real.sqrt (2*(601/5000:ℝ))) ≤
            1*2/(8*(601/5000:ℝ)*(2/5)) := by gcongr
        exact mul_le_mul (mul_le_mul_of_nonneg_left hev (by norm_num))
          (add_le_add hb1 hb2) (by positivity) (by norm_num)
      _ ≤ 100 := by norm_num
  have hh := rightV_uniform_to (by norm_num : (289/500:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1)
    hd (by norm_num [height] : (1:ℝ)<height) (le_rfl : height ≤ height)
  exact hh.trans hr

#print axioms right_hundred
end SynergyAnalytic
