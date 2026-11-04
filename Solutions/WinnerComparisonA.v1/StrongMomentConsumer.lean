/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongMoments
import RivalFullLower
namespace WinnerStrongC4
open Real Set MeasureTheory
set_option maxHeartbeats 0
noncomputable def momentLower (i : ℕ) : ℝ := match i with
  |0=>24831237/5000000
  |1=>40243359/10000000
  |2=>42716363/10000000
  |3=>4970851/2000000
  |4=>13752593/10000000
  |5=>15803167/10000000
  |6=>21756833/5000000
  |7=>4216861/1250000
  |8=>5692967/2500000
  |9=>2256319/2000000
  |10=>38357431/10000000
  |11=>10538851/5000000
  |_=>0

theorem moment_lower_nonneg (i : ℕ) : 0≤momentLower i := by
  unfold momentLower
  split <;> norm_num

theorem all_moments_lower (i : ℕ) (hi : i<12) :
    momentLower i≤∫y in (-12:ℝ)..3,momentAt y i := by
  interval_cases i
  all_goals unfold momentLower momentAt moment alpha
  all_goals solve
    | convert! WinnerRivalMoments.m0_full_lower using 1 <;> norm_num [WinnerRivalMoments.fullMoment]
    | convert! WinnerRivalMoments.m1_full_lower using 1 <;> norm_num [WinnerRivalMoments.fullMoment]
    | convert! WinnerRivalMoments.m2_full_lower using 1 <;> norm_num [WinnerRivalMoments.fullMoment]
    | convert! WinnerRivalMoments.m3_full_lower using 1 <;> norm_num [WinnerRivalMoments.fullMoment]
    | convert! WinnerRivalMoments.m4_full_lower using 1 <;> norm_num [WinnerRivalMoments.fullMoment]
    | convert! WinnerRivalMoments.m5_full_lower using 1 <;> norm_num [WinnerRivalMoments.fullMoment]
    | convert! WinnerRivalMoments.m6_full_lower using 1 <;> norm_num [WinnerRivalMoments.fullMoment]
    | convert! WinnerRivalMoments.m7_full_lower using 1 <;> norm_num [WinnerRivalMoments.fullMoment]
    | convert! WinnerRivalMoments.m8_full_lower using 1 <;> norm_num [WinnerRivalMoments.fullMoment]
    | convert! WinnerRivalMoments.m9_full_lower using 1 <;> norm_num [WinnerRivalMoments.fullMoment]
    | convert! WinnerRivalMoments.m10_full_lower using 1 <;> norm_num [WinnerRivalMoments.fullMoment]
    | convert! WinnerRivalMoments.m11_full_lower using 1 <;> norm_num [WinnerRivalMoments.fullMoment]

theorem checked_finite_kernel_lower {u r z : ℝ}
    (hu : 0<u) (hr : 0≤r) (hz : 0≤z) :
    expanded momentLower u r z≤∫y in (-12:ℝ)..3,kernel u r z y :=
  finite_kernel_lower hu hr hz all_moments_lower

#print axioms checked_finite_kernel_lower
end WinnerStrongC4
