/- Complete ANT consumption of the one fixed300 kernel-verified vector.
The paired exponential is bounded by sign, not evaluated. Same14analytic inputs. -/
import SynergyVector300.Data
namespace SynergyVector300
open ScopedNumerical SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
open _root_.Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
noncomputable section

def rawUpper : ℝ := (Data.rawUpper : ℝ)/1000000000000
def budget300 : ℝ := 1/1000000000000+rawUpper+momentTail 300
def coefficient : ℝ := (Data.roundedCoefficient : ℝ)/1000000000

theorem vector_contains : RealBox.Contains 128 (Data.total 768)
 (∑ i∈Finset.range 768,realTerm i) := by
 apply SynergyMomentMath.Real.sum_contains (fun i=>some (term i)) Data.total
  realTerm Data.zero
 · intro i hi
   exact ⟨term i,rfl,Data.step i hi⟩
 · intro i hi out h
   have same : term i=out:=Option.some.inj h
   rw [←same]
   exact term_sound i hi
 · exact Nat.le_refl 768

theorem vector_upper : (∑ i∈Finset.range 768,realTerm i) ≤ rawUpper := by
 have scalePos:=RealBox.scale_real_pos 128
 have upper:=vector_contains.2
 apply ((le_div_iff₀ scalePos).2 upper).trans
 apply (div_le_div_iff₀ scalePos (by norm_num : (0:ℝ) < 1000000000000)).2
 exact_mod_cast Data.upper_word

theorem finite_upper : finiteCoefficient SynergyMomentMath.Real.mass
 SynergyMomentMath.Real.dValue 768 300 ≤ rawUpper := by
 have compare:=paired_le_unpaired (w:=SynergyMomentMath.Real.mass)
  (D:=SynergyMomentMath.Real.dValue) (n:=768) (L:=300)
  SynergyMomentMath.Bounds.mass_nonnegative (fun i hi=>by
   have rangeD:=SynergyMomentMath.Bounds.d_range i hi
   exact ⟨by linarith [rangeD.1],by linarith [rangeD.2]⟩)
 have same : unpairedCoefficient SynergyMomentMath.Real.mass
  SynergyMomentMath.Real.dValue 768 300=(∑ i∈Finset.range 768,realTerm i) := rfl
 rw [same] at compare
 exact compare.trans vector_upper

theorem spectral_budget : spectralBase 300 100+profileCoefficient heightEndpoint
 SynergyMomentMath.Real.cValue SynergyMomentMath.Real.dValue 768 300 ≤ budget300 := by
 have finite:=finite_upper
 change finiteCoefficient (fun i=>2*((1/heightEndpoint i-1/heightEndpoint (i+1))*
  SynergyMomentMath.Real.cValue i)) SynergyMomentMath.Real.dValue 768 300 ≤ _ at finite
 have profile:=profile_of_finite (by norm_num : (300:ℝ) ≤ 300) finite
 have base:=spectralBase_300_tiny
 unfold budget300
 linarith

theorem kernel_pi_psi_300
 (h : PrimaryInputs (3681/10000) (3599/10000))
 (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
 (hsmall : ZeroCount.v1.rvm_error_small)
 (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
 (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
 (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
 HasPowerLogBound Eπ coefficient 0 (7/8) (Real.exp 300) ∧
 HasPowerLogBound Eψ coefficient 0 (7/8) (Real.exp 300) := by
 have caps:=SynergyMomentMath.PointCaps.actual_caps SourceMomentSumsV1.Real.domains h hRH
 have pi:=pi_300_from_moment_budget heightEndpoint_monotone heightEndpoint_zero
  heightEndpoint_last spectral_budget caps h hCHJ hrvm hsmall hlow hRH hQRH
 have psi:=psi_300_from_moment_budget heightEndpoint_monotone heightEndpoint_zero
  heightEndpoint_last spectral_budget caps h hCHJ hrvm hsmall hlow hRH hQRH
 have roundedPi : ((1+1/1000000000)*budget300+1/1000000000000+1/100000000:ℝ) ≤
   coefficient := by
  norm_num [budget300,rawUpper,coefficient,Data.rawUpper,Data.roundedCoefficient,momentTail]
 have roundedPsi : (budget300+1/100000000:ℝ) ≤ coefficient := by
  norm_num [budget300,rawUpper,coefficient,Data.rawUpper,Data.roundedCoefficient,momentTail]
 constructor
 · intro x hx
   have positive : 0 < x:=(Real.exp_pos 300).trans_le hx
   have value:=pi x hx
   simp only [pow_zero,mul_one] at value ⊢
   exact value.trans (mul_le_mul_of_nonneg_right roundedPi (by positivity))
 · intro x hx
   have positive : 0 < x:=(Real.exp_pos 300).trans_le hx
   have value:=psi x hx
   simp only [pow_zero,mul_one] at value ⊢
   exact value.trans (mul_le_mul_of_nonneg_right roundedPsi (by positivity))

theorem coefficient_exact : coefficient=8732871/1000000000 := rfl
theorem strict_moment_coefficient : coefficient < (8848544/1000000000:ℝ) := by
 norm_num [coefficient,Data.roundedCoefficient]
#print axioms vector_contains
#print axioms vector_upper
#print axioms finite_upper
#print axioms spectral_budget
#print axioms kernel_pi_psi_300
#print axioms coefficient_exact
#print axioms strict_moment_coefficient
end
end SynergyVector300
