import SynergyAnalytic.HeightPointChecks
import SynergyAnalytic.PointCheckDecode
namespace SynergyAnalytic.HeightPoint
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem kernel_height_generic_v4_chunk49 : (List.range 8).all (fun j => genericPointCheck (logCell (j+392+1)) (point constantValues) (cWords[j+392]?) (DWords[j+392]?) mainIndex slopeIndex)=true := by decide +kernel
#print axioms kernel_height_generic_v4_chunk49
end SynergyAnalytic.HeightPoint
