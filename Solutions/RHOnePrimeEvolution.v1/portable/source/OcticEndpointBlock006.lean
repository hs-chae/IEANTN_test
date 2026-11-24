import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked006 : tree allRow 384 6=true := by decide +kernel
#print axioms checked006
end RHOcticPush.Moments.Endpoint
