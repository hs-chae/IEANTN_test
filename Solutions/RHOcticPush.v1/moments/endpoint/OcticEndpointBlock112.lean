import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked112 : tree allRow 7168 6=true := by decide +kernel
#print axioms checked112
end RHOcticPush.Moments.Endpoint
