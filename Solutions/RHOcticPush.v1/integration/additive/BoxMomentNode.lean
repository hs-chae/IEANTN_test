import BoxFirstMoment
import BoxSecondMoment
import StieltjesTrapezoid
import IEANTN.Nodes.BoxMellinInputs.v2.Conclusions

namespace BoxMellinInputs.v2
theorem challenge_first_moment : first_moment := RHOcticPush.BoxGamma.first_moment
theorem challenge_second_moment_identity : second_moment_identity :=
  RHOcticPush.BoxGamma.second_moment_identity
theorem challenge_stieltjes_trapezoid : stieltjes_trapezoid :=
  RHLimit.Stieltjes.stieltjes_trapezoid
end BoxMellinInputs.v2
#print axioms BoxMellinInputs.v2.challenge_first_moment
#print axioms BoxMellinInputs.v2.challenge_second_moment_identity
#print axioms BoxMellinInputs.v2.challenge_stieltjes_trapezoid
