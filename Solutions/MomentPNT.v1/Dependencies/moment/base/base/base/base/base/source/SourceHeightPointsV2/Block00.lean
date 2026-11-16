import SourceHeightPointsV2.Point0000
import SourceHeightPointsV2.Point0001
import SourceHeightPointsV2.Point0002
import SourceHeightPointsV2.Point0003
import SourceHeightPointsV2.Point0004
import SourceHeightPointsV2.Point0005
import SourceHeightPointsV2.Point0006
import SourceHeightPointsV2.Point0007
import SourceHeightPointsV2.Point0008
import SourceHeightPointsV2.Point0009
import SourceHeightPointsV2.Point0010
import SourceHeightPointsV2.Point0011
import SourceHeightPointsV2.Point0012
import SourceHeightPointsV2.Point0013
import SourceHeightPointsV2.Point0014
import SourceHeightPointsV2.Point0015
import SourceHeightPointsV2.Point0016
import SourceHeightPointsV2.Point0017
import SourceHeightPointsV2.Point0018
import SourceHeightPointsV2.Point0019
import SourceHeightPointsV2.Point0020
import SourceHeightPointsV2.Point0021
import SourceHeightPointsV2.Point0022
import SourceHeightPointsV2.Point0023
import SourceHeightPointsV2.Point0024
import SourceHeightPointsV2.Point0025
import SourceHeightPointsV2.Point0026
import SourceHeightPointsV2.Point0027
import SourceHeightPointsV2.Point0028
import SourceHeightPointsV2.Point0029
import SourceHeightPointsV2.Point0030
import SourceHeightPointsV2.Point0031
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block00
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 0 ≤ i) (upper : i < 32) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0000.source_outputs
   exact ⟨SourceHeightPointsV2.Point0000.input,c,d,SourceHeightPointsV2.Point0000.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0001.source_outputs
   exact ⟨SourceHeightPointsV2.Point0001.input,c,d,SourceHeightPointsV2.Point0001.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0002.source_outputs
   exact ⟨SourceHeightPointsV2.Point0002.input,c,d,SourceHeightPointsV2.Point0002.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0003.source_outputs
   exact ⟨SourceHeightPointsV2.Point0003.input,c,d,SourceHeightPointsV2.Point0003.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0004.source_outputs
   exact ⟨SourceHeightPointsV2.Point0004.input,c,d,SourceHeightPointsV2.Point0004.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0005.source_outputs
   exact ⟨SourceHeightPointsV2.Point0005.input,c,d,SourceHeightPointsV2.Point0005.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0006.source_outputs
   exact ⟨SourceHeightPointsV2.Point0006.input,c,d,SourceHeightPointsV2.Point0006.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0007.source_outputs
   exact ⟨SourceHeightPointsV2.Point0007.input,c,d,SourceHeightPointsV2.Point0007.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0008.source_outputs
   exact ⟨SourceHeightPointsV2.Point0008.input,c,d,SourceHeightPointsV2.Point0008.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0009.source_outputs
   exact ⟨SourceHeightPointsV2.Point0009.input,c,d,SourceHeightPointsV2.Point0009.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0010.source_outputs
   exact ⟨SourceHeightPointsV2.Point0010.input,c,d,SourceHeightPointsV2.Point0010.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0011.source_outputs
   exact ⟨SourceHeightPointsV2.Point0011.input,c,d,SourceHeightPointsV2.Point0011.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0012.source_outputs
   exact ⟨SourceHeightPointsV2.Point0012.input,c,d,SourceHeightPointsV2.Point0012.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0013.source_outputs
   exact ⟨SourceHeightPointsV2.Point0013.input,c,d,SourceHeightPointsV2.Point0013.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0014.source_outputs
   exact ⟨SourceHeightPointsV2.Point0014.input,c,d,SourceHeightPointsV2.Point0014.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0015.source_outputs
   exact ⟨SourceHeightPointsV2.Point0015.input,c,d,SourceHeightPointsV2.Point0015.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0016.source_outputs
   exact ⟨SourceHeightPointsV2.Point0016.input,c,d,SourceHeightPointsV2.Point0016.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0017.source_outputs
   exact ⟨SourceHeightPointsV2.Point0017.input,c,d,SourceHeightPointsV2.Point0017.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0018.source_outputs
   exact ⟨SourceHeightPointsV2.Point0018.input,c,d,SourceHeightPointsV2.Point0018.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0019.source_outputs
   exact ⟨SourceHeightPointsV2.Point0019.input,c,d,SourceHeightPointsV2.Point0019.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0020.source_outputs
   exact ⟨SourceHeightPointsV2.Point0020.input,c,d,SourceHeightPointsV2.Point0020.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0021.source_outputs
   exact ⟨SourceHeightPointsV2.Point0021.input,c,d,SourceHeightPointsV2.Point0021.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0022.source_outputs
   exact ⟨SourceHeightPointsV2.Point0022.input,c,d,SourceHeightPointsV2.Point0022.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0023.source_outputs
   exact ⟨SourceHeightPointsV2.Point0023.input,c,d,SourceHeightPointsV2.Point0023.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0024.source_outputs
   exact ⟨SourceHeightPointsV2.Point0024.input,c,d,SourceHeightPointsV2.Point0024.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0025.source_outputs
   exact ⟨SourceHeightPointsV2.Point0025.input,c,d,SourceHeightPointsV2.Point0025.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0026.source_outputs
   exact ⟨SourceHeightPointsV2.Point0026.input,c,d,SourceHeightPointsV2.Point0026.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0027.source_outputs
   exact ⟨SourceHeightPointsV2.Point0027.input,c,d,SourceHeightPointsV2.Point0027.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0028.source_outputs
   exact ⟨SourceHeightPointsV2.Point0028.input,c,d,SourceHeightPointsV2.Point0028.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0029.source_outputs
   exact ⟨SourceHeightPointsV2.Point0029.input,c,d,SourceHeightPointsV2.Point0029.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0030.source_outputs
   exact ⟨SourceHeightPointsV2.Point0030.input,c,d,SourceHeightPointsV2.Point0030.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0031.source_outputs
   exact ⟨SourceHeightPointsV2.Point0031.input,c,d,SourceHeightPointsV2.Point0031.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block00
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block00.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
