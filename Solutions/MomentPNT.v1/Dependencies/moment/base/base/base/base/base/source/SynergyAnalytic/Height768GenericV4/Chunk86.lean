import SynergyAnalytic.HeightPointChecks
import SynergyAnalytic.PointCheckDecode
namespace SynergyAnalytic.HeightPoint
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem kernel_height_generic_v4_chunk86 : (List.range 8).all (fun j => genericPointCheck (logCell (j+688+1)) (point constantValues) (cWords[j+688]?) (DWords[j+688]?) mainIndex slopeIndex)=true := by decide +kernel
#print axioms kernel_height_generic_v4_chunk86
end SynergyAnalytic.HeightPoint
