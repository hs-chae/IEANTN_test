import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked001 : tree allRow 64 6=true := by decide +kernel
#print axioms checked001
end RHOcticPush.Moments.Endpoint
