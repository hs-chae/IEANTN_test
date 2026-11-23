import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked035 : tree allRow 2240 6=true := by decide +kernel
#print axioms checked035
end RHOcticPush.Moments.Endpoint
