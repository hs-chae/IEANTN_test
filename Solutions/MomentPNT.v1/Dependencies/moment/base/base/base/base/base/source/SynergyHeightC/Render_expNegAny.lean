import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_expNegAny : renderFunction f_expNegAny = some "static I expNegAny(I x){if(((x.lo)>(x.hi)))fail();else ;\nunsigned int shifts=0;\nwhile(((x.hi)>(64*S))){(x=divN(x,2));\n(shifts=(shifts+1));\nif((shifts>64))fail();else ;}\nI value=expNeg(x);\nwhile((shifts>0)){(value=mul(value,value));\n(shifts=(shifts-1));}\nreturn value;}\n" := by decide +kernel
#print axioms render_expNegAny
end SynergyHeightC.Generated
