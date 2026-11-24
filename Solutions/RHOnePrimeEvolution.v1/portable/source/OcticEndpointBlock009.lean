import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked009 : tree allRow 576 6=true := by decide +kernel
#print axioms checked009
end RHOcticPush.Moments.Endpoint
