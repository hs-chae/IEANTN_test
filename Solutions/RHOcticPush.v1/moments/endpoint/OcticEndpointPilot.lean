import OcticEndpointData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma pilot64 : tree row 0 6=true := by decide +kernel
lemma pilot1001 : row 1001=true := by decide +kernel
lemma pilot2000 : row 2000=true := by decide +kernel
lemma pilot2801 : row 2801=true := by decide +kernel
lemma pilot4000 : row 4000=true := by decide +kernel
lemma pilot7300 : row 7300=true := by decide +kernel
#print axioms pilot64
#print axioms pilot7300
end RHOcticPush.Moments.Endpoint
