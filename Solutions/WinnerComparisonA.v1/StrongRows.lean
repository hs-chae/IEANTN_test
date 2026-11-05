/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongWarmRowConsumer
import StrongMainMemo3
namespace WinnerStrongEnvelope
open Real MeasureTheory
set_option maxHeartbeats 0
noncomputable def rowIntegral (a b : ℝ) : ℝ :=
  600*(∫sigma in (33/40:ℝ)..(7/8),∫v in a..b,weighted sigma v)
 theorem warm_zero : (19286/10000000000:ℝ) ≤ rowIntegral (1/10000) (1/1000) := by
  have hh:=warm_row_consumed (v0:=1/10000) (step:=9/1000000) (target:=19286/10000000000)
    (n:=100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) WinnerStrongOuter.warm0_check
  convert! hh using 1 <;> norm_num [rowIntegral]
 theorem warm_one : (441466/10000000000:ℝ) ≤ rowIntegral (1/1000) (1/100) := by
  have hh:=warm_row_consumed (v0:=1/1000) (step:=9/100000) (target:=441466/10000000000)
    (n:=100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) WinnerStrongOuter.warm1_check
  convert! hh using 1 <;> norm_num [rowIntegral]
 theorem warm_two : (510932/10000000000:ℝ) ≤ rowIntegral (1/100) (1/50) := by
  have hh:=warm_row_consumed (v0:=1/100) (step:=1/10000) (target:=510932/10000000000)
    (n:=100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) WinnerStrongOuter.warm2_check
  convert! hh using 1 <;> norm_num [rowIntegral]
 theorem main_zero : (256908/10000000000:ℝ) ≤ rowIntegral (1/50) (1/40) := by
  have hh:=main_row_consumed (v0:=1/50) (step:=1/2000) (width:=7/200) (target:=256908/10000000000)
    (n:=10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      WinnerStrongOuter.main0_check WinnerStrongOuter.cap0_check
  convert! hh using 1 <;> norm_num [rowIntegral]
 theorem main_one : (767989/10000000000:ℝ) ≤ rowIntegral (1/40) (1/25) := by
  have hh:=main_row_consumed (v0:=1/40) (step:=1/2000) (width:=1/25) (target:=767989/10000000000)
    (n:=30) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      WinnerStrongOuter.main1_check WinnerStrongOuter.cap1_check
  convert! hh using 1 <;> norm_num [rowIntegral]
 theorem main_two : (509117/10000000000:ℝ) ≤ rowIntegral (1/25) (1/20) := by
  have hh:=main_row_consumed (v0:=1/25) (step:=1/2000) (width:=9/200) (target:=509117/10000000000)
    (n:=20) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      WinnerStrongOuter.main2_check WinnerStrongOuter.cap2_check
  convert! hh using 1 <;> norm_num [rowIntegral]
 theorem main_three : (9236109/1000000000:ℝ) ≤ rowIntegral (1/20) 16 := by
  have hh:=main_row_consumed (v0:=1/20) (step:=1/2000) (width:=1/20) (target:=9236109/1000000000)
    (n:=31900) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      WinnerStrongOuter.main3_original_check WinnerStrongOuter.cap3_original_check
  convert! hh using 1 <;> norm_num [rowIntegral]
#print axioms main_three
end WinnerStrongEnvelope
