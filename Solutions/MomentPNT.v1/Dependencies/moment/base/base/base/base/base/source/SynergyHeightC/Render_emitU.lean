import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_emitU : renderFunction f_emitU = some "static void emitU(U x){uint64_t words[8];\nunsigned int i=0;\nwhile((i<8)){((words[i])=((uint64_t)(x>>(64*i))));\n(i=(i+1));}\nif((fwrite(words,8,8,stdout)!=8))fail();else ;}\n" := by decide +kernel
#print axioms render_emitU
end SynergyHeightC.Generated
