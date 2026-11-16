import SynergyAnalytic.HeightPointChecks
import SynergyAnalytic.PointCheckDecode
namespace SynergyAnalytic.HeightPoint
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem kernel_height_generic_v4_chunk18 : (List.range 8).all (fun j => genericPointCheck (logCell (j+144+1)) (point constantValues) (cWords[j+144]?) (DWords[j+144]?) mainIndex slopeIndex)=true := by decide +kernel
#print axioms kernel_height_generic_v4_chunk18
end SynergyAnalytic.HeightPoint
