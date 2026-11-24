import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked070 : tree allRow 4480 6=true := by decide +kernel
#print axioms checked070
end RHOcticPush.Moments.Endpoint
