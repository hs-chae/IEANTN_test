import SourceHeightEdgesV1.Block00
import SourceHeightEdgesV1.Block01
import SourceHeightEdgesV1.Block02
import SourceHeightEdgesV1.Block03
import SourceHeightEdgesV1.Block04
import SourceHeightEdgesV1.Block05
import SourceHeightEdgesV1.Block06
import SourceHeightEdgesV1.Block07
import SourceHeightEdgesV1.Block08
import SourceHeightEdgesV1.Block09
import SourceHeightEdgesV1.Block10
import SourceHeightEdgesV1.Block11
import SourceHeightEdgesV1.Block12
import SourceHeightEdgesV1.Block13
import SourceHeightEdgesV1.Block14
import SourceHeightEdgesV1.Block15
import SourceHeightEdgesV1.Block16
import SourceHeightEdgesV1.Block17
import SourceHeightEdgesV1.Block18
import SourceHeightEdgesV1.Block19
import SourceHeightEdgesV1.Block20
import SourceHeightEdgesV1.Block21
import SourceHeightEdgesV1.Block22
import SourceHeightEdgesV1.Block23
import Lean.Elab.Tactic.Omega
namespace SourceHeightEdgesV1.All
open ScopedNumerical SynergyHeightC
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem edges (i : Nat) (hi : i<SynergyAnalytic.HeightPoint.logCellCount) :
 FullMainEdges.ExactEdges i := by
 change i<768 at hi
 let b:=i/32
 let r:=i%32
 have hb : b<24 := by dsimp [b];omega
 have hr : r<32 := by dsimp [r];omega
 have eq : 32*b+r=i := by dsimp [b,r];omega
 have chosen : FullMainEdges.ExactEdges (32*b+r) := by
  interval_cases b
  · exact SourceHeightEdgesV1.Block00.all r hr
  · exact SourceHeightEdgesV1.Block01.all r hr
  · exact SourceHeightEdgesV1.Block02.all r hr
  · exact SourceHeightEdgesV1.Block03.all r hr
  · exact SourceHeightEdgesV1.Block04.all r hr
  · exact SourceHeightEdgesV1.Block05.all r hr
  · exact SourceHeightEdgesV1.Block06.all r hr
  · exact SourceHeightEdgesV1.Block07.all r hr
  · exact SourceHeightEdgesV1.Block08.all r hr
  · exact SourceHeightEdgesV1.Block09.all r hr
  · exact SourceHeightEdgesV1.Block10.all r hr
  · exact SourceHeightEdgesV1.Block11.all r hr
  · exact SourceHeightEdgesV1.Block12.all r hr
  · exact SourceHeightEdgesV1.Block13.all r hr
  · exact SourceHeightEdgesV1.Block14.all r hr
  · exact SourceHeightEdgesV1.Block15.all r hr
  · exact SourceHeightEdgesV1.Block16.all r hr
  · exact SourceHeightEdgesV1.Block17.all r hr
  · exact SourceHeightEdgesV1.Block18.all r hr
  · exact SourceHeightEdgesV1.Block19.all r hr
  · exact SourceHeightEdgesV1.Block20.all r hr
  · exact SourceHeightEdgesV1.Block21.all r hr
  · exact SourceHeightEdgesV1.Block22.all r hr
  · exact SourceHeightEdgesV1.Block23.all r hr
 rw [eq] at chosen
 exact chosen
end SourceHeightEdgesV1.All
#print axioms SourceHeightEdgesV1.All.edges
