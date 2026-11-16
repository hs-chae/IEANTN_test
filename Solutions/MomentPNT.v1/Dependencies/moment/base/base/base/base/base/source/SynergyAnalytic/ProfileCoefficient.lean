import SynergyAnalytic.SourceOrdinate
import SynergyAnalytic.PairedLinear
namespace SynergyAnalytic
open Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def profileCoefficient (a c D:ℕ→ℝ) (n:ℕ) (L:ℝ) : ℝ :=
  2*(∑i∈Finset.range n,((1/a i-1/a (i+1))*c i)*pairedFactor (D i) (1/8) L)+
    (1/250000:ℝ)*pairedFactor 160 (1/8) L+1/50000000+
    (1/1000000000000:ℝ)*pairedFactor (880/3) (1/8) L+1/1000000000000

/-- No real-part quadrature remains in the numerical contract: the entire
paired spectral integral is exactly this finite positive coefficient sum. -/
theorem ordinate_paired_coefficient (a c D:ℕ→ℝ) (n:ℕ) (L:ℝ) :
    pairedFunctional (7/8) (1/8) L (ordinateProfile a c D n)=profileCoefficient a c D n L := by
  unfold ordinateProfile reciprocalProfile
  rw [pairedFunctional_add (by fun_prop) continuous_const]
  rw [pairedFunctional_add (by fun_prop) (by fun_prop)]
  rw [pairedFunctional_smul]
  rw [pairedFunctional_add (by fun_prop) continuous_const]
  rw [pairedFunctional_add (by fun_prop) (by fun_prop)]
  rw [pairedFunctional_sum_exponentials,pairedFunctional_exponential,
    pairedFunctional_const,pairedFunctional_exponential,pairedFunctional_const]
  unfold profileCoefficient
  ring

#print axioms ordinate_paired_coefficient
end SynergyAnalytic
