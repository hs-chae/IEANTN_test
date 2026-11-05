/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongRowConsumer
import StrongWarmProgramSemantics
import StrongWarm0
import StrongWarm1
import StrongWarm2
namespace WinnerStrongEnvelope
open Real Set MeasureTheory WinnerOldFloors WinnerOldOuter.Warm
set_option maxHeartbeats 0
 theorem band_profile_eq (v0 step : ℝ) (k j : ℕ) (s : ℝ) :
    bandProfile (30001/100) (7/8) (1/500) (data v0 step k).Bl
      (WinnerStrongOuter.warmM v0 step k j) j s=
      warmCell v0 step ((j:ℝ)/500) (((j:ℝ)+1)/500) k s := by
  unfold bandProfile WinnerStrongOuter.warmM warmCell
  norm_num only [Nat.cast_add,Nat.cast_one]
  ring_nf
 theorem warm_row_consumed {v0 step target : ℚ} {n : ℕ}
    (hv : 1/10000  ≤  v0) (hs : 0  ≤  step) (hn : 0<n)
    (hend : (v0:ℝ)+(step:ℝ)*n  ≤  16)
    (hWarm : WinnerStrongOuter.checkWarm v0 step target n=true) :
    (target:ℝ)  ≤  600*(∫sigma in (33/40:ℝ)..(7/8),∫v in (v0:ℝ)..((v0:ℝ)+(step:ℝ)*n),weighted sigma v) := by
  have hv0 : 0<v0 := by linarith
  have hvR : (1/10000:ℝ) ≤ v0 := by
    have hh:=(Rat.cast_le (K:=ℝ)).mpr hv
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
    exact hh
  have hvp : (0:ℝ)<v0 := by exact_mod_cast hv0
  have hsR : (0:ℝ) ≤ step := by exact_mod_cast hs
  have hmax (k : ℕ) (hk : k<n) : (v0:ℝ)+(step:ℝ)*(k+1) ≤ 16 := by
    have hkn : ((k:ℝ)+1) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hk
    nlinarith [mul_le_mul_of_nonneg_left hkn hsR]
  have hB (k : ℕ) (hk : k<n) := data_exponents_ne hvp.le hsR (hmax k hk)
  have hF:=row_rectangle_continuous hvR hend
  have hF' : ContinuousOn (fun p:ℝ×ℝ=>weighted p.1 p.2)
    (Icc (7/8-(1/500:ℝ)*(25:ℕ)) (7/8) ×ˢ Icc (v0:ℝ) ((v0:ℝ)+(step:ℝ)*n)) := by
    convert! hF using 1 <;> norm_num
  have hLower : ∀k<n,∀v∈Icc ((v0:ℝ)+(step:ℝ)*k) ((v0:ℝ)+(step:ℝ)*(k+1)),∀(j:ℕ),j<25→
      ∀s∈Icc (7/8-(1/500:ℝ)*(j+1)) (7/8-(1/500:ℝ)*j),
        bandProfile (30001/100) (7/8) (1/500) (data (v0:ℝ) (step:ℝ) k).Bl
          (WinnerStrongOuter.warmM v0 step k j) j s ≤ weighted s v := by
    intro k hk v hvr j hj s hsr
    rw [band_profile_eq]
    have hjR : (j:ℝ)+1 ≤ 25 := by exact_mod_cast Nat.succ_le_of_lt hj
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    exact warm_cell_lower hvp hsR (hmax k hk) (by nlinarith [hsr.1])
      (by nlinarith [hsr.2]) (by nlinarith [hsr.1]) hvr.1 hvr.2
  have hrow:=warm_row_sigma_first (F:=weighted) (K:=30001/100) (beta:=7/8) (qStep:=1/500)
    (n:=n) (J:=25) (fun k=>(data (v0:ℝ) (step:ℝ) k).Bl)
    (WinnerStrongOuter.warmM v0 step) (by norm_num) hsR (fun k hk=>(hB k hk).1) hF' hLower
  have hNative:=WinnerStrongOuter.checkWarm_sound (by linarith : 0 ≤ v0) hs hn hWarm
  have hh:=hNative.trans hrow
  convert! hh using 1 <;> norm_num
#print axioms warm_row_consumed
end WinnerStrongEnvelope
