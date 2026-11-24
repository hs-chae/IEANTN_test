import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked093 : tree allRow 5952 6=true := by decide +kernel
#print axioms checked093
end RHOcticPush.Moments.Endpoint
