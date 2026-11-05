/- Copyright (c)2026 IEANTN contributors. Released under Apache2.0. -/
import ArbitraryOuterAssembly
namespace WinnerOldOuter.Rectangles
open Real Set MeasureTheory WinnerOldOuter.Assembly
set_option maxHeartbeats 0
noncomputable def rowIntegral (F:ℝ→ℝ→ℝ) (lo hi a b:ℝ) : ℝ :=
  600*(∫sigma in lo..hi,∫v in a..b,F sigma v)

/-- Actual adjacent height rectangles add exactly; convergence and each
Fubini interchange follow from continuity on the common compact rectangle. -/
theorem rowIntegral_add {F:ℝ→ℝ→ℝ} {lo hi a b c:ℝ}
    (hlo:lo≤hi) (hab:a≤b) (hbc:b≤c)
    (hF:ContinuousOn (fun p:ℝ×ℝ=>F p.1 p.2) (Icc lo hi×ˢ Icc a c)) :
    rowIntegral F lo hi a b+rowIntegral F lo hi b c=rowIntegral F lo hi a c := by
  have hFab:ContinuousOn (fun p:ℝ×ℝ=>F p.1 p.2) (Icc lo hi×ˢ Icc a b):=
    hF.mono (Set.prod_mono Subset.rfl (Icc_subset_Icc le_rfl hbc))
  have hFbc:ContinuousOn (fun p:ℝ×ℝ=>F p.1 p.2) (Icc lo hi×ˢ Icc b c):=
    hF.mono (Set.prod_mono Subset.rfl (Icc_subset_Icc hab le_rfl))
  have hG:ContinuousOn (fun v=>∫sigma in lo..hi,F sigma v) (Icc a c):=
    (rectangle_integrability hlo (hab.trans hbc) hF).2
  have hiab:IntervalIntegrable (fun v=>∫sigma in lo..hi,F sigma v) volume a b:=
    (hG.mono (Icc_subset_Icc le_rfl hbc)).intervalIntegrable_of_Icc hab
  have hibc:IntervalIntegrable (fun v=>∫sigma in lo..hi,F sigma v) volume b c:=
    (hG.mono (Icc_subset_Icc hab le_rfl)).intervalIntegrable_of_Icc hbc
  unfold rowIntegral
  rw [←rectangle_integral_swap hlo hab hFab,←rectangle_integral_swap hlo hbc hFbc,
    ←rectangle_integral_swap hlo (hab.trans hbc) hF,←mul_add,
    intervalIntegral.integral_add_adjacent_intervals hiab hibc]
#print axioms rowIntegral_add
end WinnerOldOuter.Rectangles
