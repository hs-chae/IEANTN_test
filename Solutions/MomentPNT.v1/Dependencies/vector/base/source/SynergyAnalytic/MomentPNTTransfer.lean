/- Quantitative consumers for the new mass/first-moment numerical providers.
The generic interfaces below do not assert that any concrete provider is verified. -/
import SynergyAnalytic.MassMomentTransfer
import SynergyAnalytic.RationalPNTTransfer
import SynergyAnalytic.HeightRawSpectral300
import SynergyAnalytic.DirectPsiSource
namespace SynergyAnalytic
open Real Set IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
open WinnerDensityA CH2QRH
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

noncomputable def momentTail (L : ℝ) : ℝ :=
 (1/250000)*L/(L-160)+1/50000000+
 (1/1000000000000)*L/(L-880/3)+1/1000000000000
noncomputable def finitePNTCoefficient (B L : ℝ) : ℝ :=
 (1+1/1000000000)*(1/1000000000000+B+momentTail L)+
 1/1000000000000+1/100000000

theorem profile_of_finite {a c D : Nat→ℝ} {n : Nat} {B L : ℝ}
 (lowerL : 300 ≤ L)
 (finite : finiteCoefficient (fun i=>2*((1/a i-1/a (i+1))*c i)) D n L ≤ B) :
 profileCoefficient a c D n L ≤ B+momentTail L := by
 rw [finiteCoefficient_height_form] at finite
 have tail:=pairedFactor_upper_fraction (D:=160) (r:=(1/8:ℝ))
  (by norm_num) (by linarith : (160:ℝ) < L)
 have count:=pairedFactor_upper_fraction (D:=(880/3:ℝ)) (r:=(1/8:ℝ))
  (by norm_num) (by linarith : (880/3:ℝ) < L)
 unfold profileCoefficient momentTail
 simp only [mul_div_assoc]
 nlinarith

theorem ray_coefficient_of_finite {a c D : Nat→ℝ} {n : Nat} {B L : ℝ}
 (future : 330 ≤ L)
 (finite : finiteCoefficient (fun i=>2*((1/a i-1/a (i+1))*c i)) D n L ≤ B) :
 rayCoefficient a c D n L ≤ finitePNTCoefficient B L := by
 have profile:=profile_of_finite (by linarith : 300 ≤ L) finite
 have base:=spectralBase_330_tiny
 unfold rayCoefficient finitePNTCoefficient
 nlinarith

theorem pi_ray_of_finite {a c D : Nat→ℝ} {n : Nat} {B L : ℝ}
 (monotone : Monotone a) (first : a 0=WinnerOriginalScalars.height)
 (last : a n=Real.exp 60) (future : 330 ≤ L)
 (finite : finiteCoefficient (fun i=>2*((1/a i-1/a (i+1))*c i)) D n L ≤ B)
 (caps : ActualHeightCaps a c D n)
 (h : PrimaryInputs (3681/10000) (3599/10000))
 (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
 (hsmall : ZeroCount.v1.rvm_error_small)
 (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
 (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
 (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
 HasPowerLogBound Eπ (finitePNTCoefficient B L) 0 (7/8) (Real.exp L) := by
 have source:=source_pi_count_profile_ray monotone first last h caps
  hCHJ hrvm hsmall hlow hRH hQRH future
 have bound:=ray_coefficient_of_finite future finite
 intro x hx
 have positiveX : 0 < x:=(Real.exp_pos L).trans_le hx
 have value:=source x hx
 simp only [pow_zero,mul_one] at value ⊢
 exact value.trans (mul_le_mul_of_nonneg_right bound (by positivity))

theorem raw_ray300_of_budget {a c D : Nat→ℝ} {n : Nat} {B : ℝ}
 (monotone : Monotone a) (first : a 0=WinnerOriginalScalars.height)
 (last : a n=Real.exp 60)
 (budget : spectralBase 300 100+profileCoefficient a c D n 300 ≤ B)
 (h : PrimaryInputs (3681/10000) (3599/10000))
 (caps : ActualHeightCaps a c D n)
 (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
 (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
 (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
 (hQRH : ZetaZeroFreeHalfPlane (7/8)) {L : ℝ} (future : 300 ≤ L) :
 rawSpectral (Real.exp (L/3)) (Real.exp L)*Real.exp (L/8) ≤ B := by
 have thousand : (1000:ℝ) ≤ Real.exp (L/3) := by
  calc
   (1000:ℝ) ≤ 2^100 := by norm_num
   _ ≤ (Real.exp 1)^100 := pow_le_pow_left₀ (by norm_num)
     (by linarith [Real.add_one_le_exp (1:ℝ)]) 100
   _ = Real.exp 100 := by rw [←Real.exp_nat_mul];norm_num
   _ ≤ Real.exp (L/3) := Real.exp_le_exp.mpr (by linarith)
 have truncation : Real.exp 100 ≤ Real.exp (L/3) := Real.exp_le_exp.mpr (by linarith)
 have spectral:=actual_spectral_from_continuous_envelope hrvm hsmall hlow thousand
  (Real.exp_pos L) (by norm_num : (0:ℝ) ≤ 300)
  (by simpa only [Real.log_exp] using future) hQRH
  (ordinateProfile a c D n) (ordinateProfile_continuous a c D n)
  (fun s hs=>source_ordinate_from_count_cells_at100 monotone first last h caps hRH
    hs.1 hs.2 truncation)
 have base:=density_count_base_row (L₀:=300) (L:=L) (τ:=100) (t:=Real.exp (L/3))
  (by norm_num) future (by norm_num) (by linarith)
  (by rw [Real.log_exp];norm_num;linarith)
 have power : (Real.exp L)^((1:ℝ)/8)=Real.exp (L/8) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp]
  congr 1
  ring
 rw [power,Real.log_exp,ordinate_paired_coefficient] at spectral
 exact (spectral.trans (add_le_add base le_rfl)).trans budget

#print axioms profile_of_finite
#print axioms ray_coefficient_of_finite
#print axioms pi_ray_of_finite
#print axioms raw_ray300_of_budget
end SynergyAnalytic
