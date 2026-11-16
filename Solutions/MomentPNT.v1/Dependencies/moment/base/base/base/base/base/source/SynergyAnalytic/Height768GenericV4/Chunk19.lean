import SynergyAnalytic.HeightPointChecks
import SynergyAnalytic.PointCheckDecode
namespace SynergyAnalytic.HeightPoint
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem kernel_height_generic_v4_chunk19 : (List.range 8).all (fun j => genericPointCheck (logCell (j+152+1)) (point constantValues) (cWords[j+152]?) (DWords[j+152]?) mainIndex slopeIndex)=true := by decide +kernel
#print axioms kernel_height_generic_v4_chunk19
end SynergyAnalytic.HeightPoint
