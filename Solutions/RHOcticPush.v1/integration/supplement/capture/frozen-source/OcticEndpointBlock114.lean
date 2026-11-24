import OcticCellData
namespace RHOcticPush.Moments.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
lemma checked114 : tree allRow 7296 2=true := by decide +kernel
lemma checked_last : allRow 7300=true := by decide +kernel
#print axioms checked_last
#print axioms checked114
end RHOcticPush.Moments.Endpoint
