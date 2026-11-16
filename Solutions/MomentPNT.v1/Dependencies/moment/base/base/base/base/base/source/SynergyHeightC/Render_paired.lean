import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_paired : renderFunction f_paired = some "static I paired(I D,unsigned int L){I Lbox=rat(L,1);\nif(((D.hi)>=(Lbox.lo)))fail();else ;\nI difference=positiveSub(Lbox,D);\nI e=expNegAny(divN(difference,8));\nreturn add(e,divI(mul(Lbox,positiveSub(unit(),e)),difference));}\n" := by decide +kernel
#print axioms render_paired
end SynergyHeightC.Generated
