/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongSlopes
import StrongMainProgramSemantics
namespace WinnerStrongEnvelope
open Real Set MeasureTheory WinnerOldFloors WinnerOldOuter.Arbitrary
set_option maxHeartbeats 0
 theorem row_rectangle_continuous {a b : ℝ} (ha : (1/10000:ℝ)≤a) (hb : b≤16) :
    ContinuousOn (fun p:ℝ×ℝ=>weighted p.1 p.2)
      (Icc (7/8-(1/20):ℝ) (7/8) ×ˢ Icc a b) := by
  apply continuousOn_rectangle.mono
  apply Set.prod_mono
  · apply Icc_subset_Icc <;> norm_num
  · exact Icc_subset_Icc ha hb
 theorem main_row_consumed {v0 step width target : ℚ} {n : ℕ}
    (hv : 1/10000 ≤ v0) (hs : 0 ≤ step) (hn : 0<n) (hwidth : 0 ≤ width) (hwidth' : width ≤ 1/20)
    (hend : (v0:ℝ)+(step:ℝ)*n ≤ 16)
    (hMain : WinnerStrongOuter.checkMain v0 step width target n=true)
    (hCap : WinnerStrongOuter.checkCap v0 step width n=true) :
    (target:ℝ) ≤ 600*(∫sigma in (33/40:ℝ)..(7/8),∫v in (v0:ℝ)..((v0:ℝ)+(step:ℝ)*n),weighted sigma v) := by
  have hv0 : 0<v0 := by linarith
  have hvR : (1/10000:ℝ)≤v0 := by
    have hh:=(Rat.cast_le (K:=ℝ)).mpr hv
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
    exact hh
  have hvp : (0:ℝ)<v0 := by exact_mod_cast hv0
  have hsR : (0:ℝ)≤step := by exact_mod_cast hs
  have hwR : (0:ℝ)≤width := by exact_mod_cast hwidth
  have hwR' : (width:ℝ)≤1/20 := by
    have hh:=(Rat.cast_le (K:=ℝ)).mpr hwidth'
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
    exact hh
  have hmax (k : ℕ) (hk : k<n) : (v0:ℝ)+(step:ℝ)*(k+1)≤16 := by
    have hkn : ((k:ℝ)+1)≤n := by exact_mod_cast Nat.succ_le_of_lt hk
    nlinarith [mul_le_mul_of_nonneg_left hkn hsR]
  have hB (k : ℕ) (hk : k<n) := data_exponents_ne hvp.le hsR (hmax k hk)
  have hF:=row_rectangle_continuous hvR hend
  have hLower : ∀k<n,∀v∈Icc ((v0:ℝ)+(step:ℝ)*k) ((v0:ℝ)+(step:ℝ)*(k+1)),
      ∀s∈Icc (7/8-(width:ℝ)) (7/8),cellProfile (30001/100) (7/8)
        ((3663/5000)*Real.pi) (data (v0:ℝ) (step:ℝ) k) s≤weighted s v := by
    intro k hk v hvr s hsr
    exact main_cell_lower hvp hsR (hmax k hk) hwR (by linarith [hsr.1]) hsr.2 hsr.1 hvr.1 hvr.2
      (WinnerStrongOuter.checkCap_sound (by linarith) hs hk hCap)
  have hrow:=row_into_wider_rectangle (F:=weighted) (K:=30001/100) (beta:=7/8)
    (width:=(width:ℝ)) (wholeWidth:=1/20) (den:=(3663/5000)*Real.pi)
    (data (v0:ℝ) (step:ℝ)) hwR hwR' hsR (fun k hk=>(hB k hk).1) (fun k hk=>(hB k hk).2)
    hF (fun s _ v hvv=>nonnegative (by linarith [hvv.1])) hLower
  have hNative:=WinnerStrongOuter.checkMain_sound (by linarith : 0≤v0) hs hn hMain
  have hh:=hNative.trans hrow
  convert! hh using 1 <;> norm_num
#print axioms main_row_consumed
end WinnerStrongEnvelope
