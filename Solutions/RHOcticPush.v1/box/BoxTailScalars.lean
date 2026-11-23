import BoxTail
namespace RHOcticPush.BoxTail
open CLogMoment
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma scalar_improved : improvedUpper < 70871/100000 ∧ 0 < tailCorrection := by
  decide +kernel

#print axioms scalar_improved
end RHOcticPush.BoxTail
