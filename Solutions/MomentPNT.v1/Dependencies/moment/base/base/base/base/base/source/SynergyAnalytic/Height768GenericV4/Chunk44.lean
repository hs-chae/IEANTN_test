import SynergyAnalytic.HeightPointChecks
import SynergyAnalytic.PointCheckDecode
namespace SynergyAnalytic.HeightPoint
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem kernel_height_generic_v4_chunk44 : (List.range 8).all (fun j => genericPointCheck (logCell (j+352+1)) (point constantValues) (cWords[j+352]?) (DWords[j+352]?) mainIndex slopeIndex)=true := by decide +kernel
#print axioms kernel_height_generic_v4_chunk44
end SynergyAnalytic.HeightPoint
