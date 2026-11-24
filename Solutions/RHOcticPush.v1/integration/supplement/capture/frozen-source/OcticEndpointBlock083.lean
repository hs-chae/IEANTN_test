import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked083 : tree allRow 5312 6=true := by decide +kernel
#print axioms checked083
end RHOcticPush.Moments.Endpoint
