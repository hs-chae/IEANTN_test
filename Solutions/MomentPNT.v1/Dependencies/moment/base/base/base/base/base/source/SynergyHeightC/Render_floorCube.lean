import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_floorCube : renderFunction f_floorCube = some "static U floorCube(U n){U lo=0;\nU hi=(4*S);\nwhile((lo<hi)){U m=((lo+((hi-lo)/2))+1);\nif((mulU(mulU(m,m),m)<=n))(lo=m);else (hi=(m-1));}\nreturn lo;}\n" := by decide +kernel
#print axioms render_floorCube
end SynergyHeightC.Generated
