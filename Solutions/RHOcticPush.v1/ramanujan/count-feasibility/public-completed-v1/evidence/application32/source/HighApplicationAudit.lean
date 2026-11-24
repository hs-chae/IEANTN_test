import HighDriverContract
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #["LCMSourcePV.RestrictedC","WitnessCGrammar","LCMSourcePV.ASTLoops","RamanujanPV.QuotientCSourceV2","RamanujanPV.QuotientDriverSource","HighDriverSource","RamanujanPV.CSource","RamanujanPV.CArithmetic","RamanujanPV.QuotientCMachine","RamanujanPV.PrimeCount","RamanujanPV.QuotientSieve","RamanujanPV.QuotientTables","RamanujanPV.QuotientCInit","RamanujanPV.QuotientCSource","RamanujanPV.QuotientSqrtExecute","RamanujanPV.QuotientWordBounds","RamanujanPV.QuotientCExecute","RamanujanPV.QuotientCFunctionPrefix","RamanujanPV.QuotientCLarge","RamanujanPV.QuotientCSmallLoop","RamanujanPV.QuotientCRound","RamanujanPV.QuotientCWhole","LCMSourcePV.ASTDeterminism","RamanujanPV.QuotientCDeterminism","RamanujanPV.QuotientCFunction","RamanujanPV.QuotientCHeapShape","RamanujanPV.QuotientDriverInit","RamanujanPV.QuotientDriverExecution","RamanujanPV.QuotientDriverSuccess","HighDriverRuntime","HighDriverContract"]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, idx) in env.const2ModIdx.toList do
    let modName := (env.header.moduleNames[idx.toNat]?).getD .anonymous
    if !mods.contains modName.toString then continue
    let some (.thmInfo _) := env.find? name | continue
    let axs ← collectAxioms name
    unless axs.all allowed.contains do throwError "Nonstandard application proof {name}: {axs}"
    let row := Json.mkObj [("name",toJson name.toString),("module",toJson modName.toString),("axioms",toJson (axs.map Name.toString))]
    logInfo m!"HIGH_MAIN_PROOF {row.compress}"
    count := count + 1
  unless count > 0 do throwError "Empty application proof audit"
  logInfo m!"HIGH_MAIN_AUDIT_PASS {count}"
