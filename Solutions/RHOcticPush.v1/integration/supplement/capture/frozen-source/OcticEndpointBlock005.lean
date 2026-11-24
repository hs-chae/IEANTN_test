import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked005 : tree allRow 320 6=true := by decide +kernel
#print axioms checked005
end RHOcticPush.Moments.Endpoint
