import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked096 : tree allRow 6144 6=true := by decide +kernel
#print axioms checked096
end RHOcticPush.Moments.Endpoint
