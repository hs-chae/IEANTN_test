import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked030 : tree allRow 1920 6=true := by decide +kernel
#print axioms checked030
end RHOcticPush.Moments.Endpoint
