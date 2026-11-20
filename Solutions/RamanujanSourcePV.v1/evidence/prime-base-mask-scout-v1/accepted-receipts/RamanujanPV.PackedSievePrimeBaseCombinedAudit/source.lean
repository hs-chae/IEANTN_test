/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PrimeBaseMaskScout.CombinedP
import Lean.Util.FoldConsts
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let forbiddenModules := ["RamanujanPV.PackedSievePrimitiveMaskMillion",
    "RamanujanPV.PackedSievePrimitiveQWindow",
    "RamanujanPV.PrimeBaseMaskScout.MainP","RamanujanPV.PrimeBaseMaskScout.OldControlP",
    "RamanujanPV.PackedMaskDataEncoding.BaselineData",
    "RamanujanPV.LocalLucas","RamanujanPV.LocalPrimeTree","RamanujanPV.LocalWindowMillion"]
  for name in env.header.moduleNames do
    for pre in forbiddenModules do
      if name.toString.startsWith pre then throwError "Forbidden baseline/Lucas module imported {name}"
    if name.toString.endsWith ".Equality" || name.toString.endsWith ".ProviderCheck" then
      throwError "Prior calibration/provider module imported {name}"
  logInfo m!"COMBINED_ACTUAL_IMPORT_COUNT {env.header.moduleNames.size}"
  for (root,required) in [
    (`RamanujanPV.PrimeBaseMaskScout.CombinedP.original_mask_equality,
     [`RamanujanPV.PrimeBaseMaskScout.CombinedP.primitive_evaluated,
      `RamanujanPV.PackedSievePrimeBase.primitive_eq_original,
      `RamanujanPV.PackedSievePrimeBase.certified_membership,
      `RamanujanPV.PackedSievePrimeBase.list_composite_iff,
      `RamanujanPV.PrimeBaseMaskScout.BaseP.full_P_certificate,
      `RamanujanPV.PrimeBaseMaskScout.BaseP.range_checked,
      `RamanujanPV.PrimeBaseMaskScout.BaseP.canonical_base_evaluated,
      `RamanujanPV.PackedSieveCorrect.primeBits_prime,
      `RamanujanPV.PackedMaskEncodingCodec.assemble,
      `RamanujanPV.PackedMaskDataEncoding.W4096DataOnly.value,
      `Nat.minFac_prime,`Nat.minFac_sq_le_self]),
    (`RamanujanPV.PrimeBaseMaskScout.CombinedP.primitive_evaluated,([] : List Name))] do
    let mut seen : NameSet := ({} : NameSet).insert root
    let mut pending := [root]
    let mut axioms : NameSet := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      let some info := env.find? name | throwError "Missing actual combined proof path {name}"
      if name == `sorryAx || name.toString.startsWith "Lean.ofReduceBool" then
        throwError "Native/admitted numerical leaf {name}"
      if name.toString.endsWith ".data_equal" || name.toString.contains "primitive_program_matches_data" ||
          name.toString.contains "original_program_matches_data" then
        throwError "Calibration/old provider proof reused {name}"
      for pre in forbiddenModules do
        if name.toString.startsWith pre then throwError "Old-data/proof/primality path {name}"
      match info with
      | .axiomInfo _ =>
        unless name == `propext || name == `Classical.choice || name == `Quot.sound do
          throwError "Nonstandard combined-provider axiom {name}"
        axioms := axioms.insert name
      | _ => pure ()
      for dependency in info.getUsedConstantsAsSet.toList do
        if !seen.contains dependency then
          seen := seen.insert dependency
          pending := dependency :: pending
    for name in required do
      unless seen.contains name do throwError "Missing certified-list/math/computed-DATA path {name}"
      logInfo m!"COMBINED_REQUIRED {root} {name}"
    unless !(env.find? root).get!.type.isForall do
      throwError "Combined ground equality retains external premise {root}"
    logInfo m!"COMBINED_COMPLETE_CLOSURE {root} {seen.size}"
    logInfo m!"COMBINED_COMPLETE_AXIOMS {root} {axioms.toList}"
namespace RamanujanPV.PackedSievePrimeBaseCombinedAudit
example : PackedSieveKernel.primeBits 38358837684 1000000=
    PackedMaskDataEncoding.W4096DataOnly.value := PrimeBaseMaskScout.CombinedP.original_mask_equality
#print axioms PrimeBaseMaskScout.CombinedP.original_mask_equality
end RamanujanPV.PackedSievePrimeBaseCombinedAudit
