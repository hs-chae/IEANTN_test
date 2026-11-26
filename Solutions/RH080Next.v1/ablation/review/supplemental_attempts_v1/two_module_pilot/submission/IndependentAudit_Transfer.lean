import Transfer
import Lean
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option pp.fullNames true
open Lean Elab Command Meta
run_cmd do
  let env←getEnv
  let moduleName : Name:=`Transfer
  let constants:=env.constants.toList.filter (fun pair=>match env.getModuleIdxFor? pair.1 with
    | some i=>env.header.moduleNames[i]! == moduleName
    | none=>false)
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let mut rows : Array Json:=#[]
  let mut problems : Array Json:=#[]
  let mut theoremCount:=0
  for (name,info) in constants do
    let axioms←collectAxioms name
    let rendered←liftTermElabM <| Meta.ppExpr info.type
    let kind:=match info with
      | .thmInfo _=>"theorem" | .defnInfo _=>"definition" | .axiomInfo _=>"axiom"
      | .opaqueInfo _=>"opaque" | .inductInfo _=>"inductive" | .ctorInfo _=>"constructor"
      | .recInfo _=>"recursor" | .quotInfo _=>"quotient"
    let deps:=match info with
      | .thmInfo t=>t.value.getUsedConstants.toList.map toString
      | .defnInfo t=>t.value.getUsedConstants.toList.map toString
      | _=>[]
    if kind=="theorem" then theoremCount:=theoremCount+1
    let row:=Json.mkObj [("declaration",toJson name.toString),("kind",toJson kind),
      ("type",toJson rendered.pretty),("axioms",toJson (axioms.map toString)),("direct_dependencies",toJson deps)]
    rows:=rows.push row
    if kind=="axiom" || !(axioms.all allowed.contains) then problems:=problems.push row
  liftIO <| IO.FS.writeFile "/work/submission/EXPORT.Transfer.json" (Json.compress (Json.mkObj
    [("module",toJson moduleName.toString),("declarations",toJson rows),("problems",toJson problems),("theorems",toJson theoremCount)]))
  unless theoremCount>0 do throwError "No submitted theorem declarations"
  unless problems.isEmpty do throwError "Submitted axioms or nonstandard proof axioms: {problems.size}"
  logInfo m!"SUPPLEMENTAL_FULL_Transfer_TYPE_STD3_EXPORT_PASS module={moduleName} declarations={rows.size} theorems={theoremCount} CLAIM_INTERPRETATION_PENDING PRIMARY_INADMISSIBLE_UNCHANGED"
