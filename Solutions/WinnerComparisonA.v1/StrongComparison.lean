/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongRows
import RectangleAdd
namespace WinnerStrongEnvelope
open Real Set MeasureTheory
set_option maxHeartbeats 0
noncomputable def benchmark : ℝ := rowIntegral (1/10000) 16
 theorem row_add {a b c : ℝ} (ha : (1/10000:ℝ)≤a) (hab : a≤b) (hbc : b≤c) (hc : c≤16) :
    rowIntegral a b+rowIntegral b c=rowIntegral a c := by
  have hF : ContinuousOn (fun p:ℝ×ℝ=>weighted p.1 p.2)
      (Icc (33/40:ℝ) (7/8) ×ˢ Icc a c) :=
    continuousOn_rectangle.mono (Set.prod_mono Subset.rfl (Icc_subset_Icc ha hc))
  exact WinnerOldOuter.Rectangles.rowIntegral_add (by norm_num) hab hbc hF
 theorem benchmark_lower : (23716697/2500000000:ℝ)≤benchmark := by
  have h0:=row_add (a:=1/10000) (b:=1/1000) (c:=1/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1:=row_add (a:=1/10000) (b:=1/100) (c:=1/50) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2:=row_add (a:=1/10000) (b:=1/50) (c:=1/40) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3:=row_add (a:=1/10000) (b:=1/40) (c:=1/25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4:=row_add (a:=1/10000) (b:=1/25) (c:=1/20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5:=row_add (a:=1/10000) (b:=1/20) (c:=16) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold benchmark
  linarith [warm_zero,warm_one,warm_two,main_zero,main_one,main_two,main_three]
 theorem benchmark_rounded_lower : (18973/2000000:ℝ)≤benchmark := by
  linarith [benchmark_lower]
 theorem new_coefficient_strict : (2371/250000:ℝ)<benchmark := by
  linarith [benchmark_lower]
 theorem coefficient_margin : (1/400000:ℝ)≤benchmark-(2371/250000) := by
  linarith [benchmark_lower]
#print axioms benchmark_lower
#print axioms new_coefficient_strict
end WinnerStrongEnvelope
