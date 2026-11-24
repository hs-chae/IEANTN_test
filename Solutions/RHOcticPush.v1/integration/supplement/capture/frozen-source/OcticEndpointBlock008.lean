import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked008 : tree allRow 512 6=true := by decide +kernel
#print axioms checked008
end RHOcticPush.Moments.Endpoint
