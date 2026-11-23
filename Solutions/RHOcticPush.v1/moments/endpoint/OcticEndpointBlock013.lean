import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked013 : tree allRow 832 6=true := by decide +kernel
#print axioms checked013
end RHOcticPush.Moments.Endpoint
