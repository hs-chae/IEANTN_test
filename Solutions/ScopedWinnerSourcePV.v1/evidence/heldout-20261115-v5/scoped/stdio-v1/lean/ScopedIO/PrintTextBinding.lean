/- Actual original print helper files, bound individually to structured ASTs.
This is source correspondence only, not their execution/correctness theorem. -/
import ScopedC.Generated
import ScopedC.Restricted

namespace ScopedIO.PrintTextBinding
open ScopedC ScopedC.Syntax ScopedC.RestrictedC
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def printSSource : String := include_str "../../../source-bundle/source/function_64_printS.inc"
def printISource : String := include_str "../../../source-bundle/source/function_65_printI.inc"

theorem printS_render : renderFunction Generated.f_printS = some printSSource :=
  Generated.render_printS

theorem printI_render : renderFunction Generated.f_printI = some printISource :=
  Generated.render_printI

theorem printS_source : SourceCorresponds renderFunction printSSource Generated.f_printS :=
  source_corresponds_of_exact _ _ _ printS_render (by decide +kernel)

theorem printI_source : SourceCorresponds renderFunction printISource Generated.f_printI :=
  source_corresponds_of_exact _ _ _ printI_render (by decide +kernel)

end ScopedIO.PrintTextBinding
