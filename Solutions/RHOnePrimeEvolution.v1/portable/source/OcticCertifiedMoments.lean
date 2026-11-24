import OcticEndpointAssembly
import OcticFiniteCaps
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0

theorem actual_M0 : FourierMoments.M0 ≤ (143/25:ℝ) :=
  actual_M0_of_checked all_checked

theorem actual_M1 : FourierMoments.M1 ≤ (23/5:ℝ) :=
  actual_M1_of_checked all_checked

theorem certified_moments : FourierMoments.M0 ≤ (143/25:ℝ) ∧
    FourierMoments.M1 ≤ (23/5:ℝ) := ⟨actual_M0,actual_M1⟩

#print axioms actual_M0
#print axioms actual_M1
#print axioms certified_moments
end RHOcticPush.Moments.Endpoint
