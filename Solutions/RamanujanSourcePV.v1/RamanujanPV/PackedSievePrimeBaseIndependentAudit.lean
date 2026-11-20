/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PrimeBaseMaskScout.MainP
import RamanujanPV.PrimeBaseMaskScout.OldControlP
import Lean.Util.FoldConsts
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  for (root,required) in [
    (`RamanujanPV.PrimeBaseMaskScout.MainP.original_mask_equality,
     [`RamanujanPV.PrimeBaseMaskScout.MainP.primitive_evaluated,
      `RamanujanPV.PackedSievePrimeBase.primitive_eq_original,
      `RamanujanPV.PackedSievePrimeBase.certified_membership,
      `RamanujanPV.PackedSievePrimeBase.list_composite_iff,
      `RamanujanPV.PrimeBaseMaskScout.BaseP.full_P_certificate,
      `RamanujanPV.PrimeBaseMaskScout.BaseP.range_checked,
      `RamanujanPV.PrimeBaseMaskScout.BaseP.canonical_base_evaluated,
      `RamanujanPV.PackedSieveCorrect.primeBits_prime,
      `Nat.minFac_prime,`Nat.minFac_sq_le_self]),
    (`RamanujanPV.PrimeBaseMaskScout.MainP.primitive_evaluated,([] : List Name)),
    (`RamanujanPV.PrimeBaseMaskScout.OldControlP.primitive_evaluated,([] : List Name))] do
    let mut seen : NameSet := ({} : NameSet).insert root
    let mut pending := [root]
    let mut axioms : NameSet := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      let some info := env.find? name | throwError "Missing actual proof path {name}"
      if name == `sorryAx || name.toString.startsWith "Lean.ofReduceBool" then
        throwError "Native/admitted numerical leaf {name}"
      if name == `RamanujanPV.PackedSievePrimitiveMaskMillion.primitive_bits ||
          name == `RamanujanPV.PackedSievePrimitiveMaskMillion.packed_bits then
        throwError "Old P correctness theorem reused {name}"
      if name.toString.startsWith "RamanujanPV.LocalLucas." ||
          name.toString.startsWith "RamanujanPV.LocalPrimeTree." ||
          name.toString.startsWith "RamanujanPV.LocalWindowMillion.Prime" then
        throwError "Unrequested Lucas/old-primality path {name}"
      match info with
      | .axiomInfo _ =>
        unless name == `propext || name == `Classical.choice || name == `Quot.sound do
          throwError "Nonstandard axiom {name}"
        axioms := axioms.insert name
      | _ => pure ()
      for dependency in info.getUsedConstantsAsSet.toList do
        if !seen.contains dependency then
          seen := seen.insert dependency
          pending := dependency :: pending
    for name in required do
      unless seen.contains name do throwError "Missing certified-base/math/numeric path {name}"
      logInfo m!"PRIME_BASE_REQUIRED {root} {name}"
    unless !(env.find? root).get!.type.isForall do
      throwError "Ground identity still has an unclosed premise {root}"
    logInfo m!"PRIME_BASE_COMPLETE_CLOSURE {root} {seen.size}"
    logInfo m!"PRIME_BASE_COMPLETE_AXIOMS {root} {axioms.toList}"
namespace RamanujanPV.PackedSievePrimeBaseIndependentAudit
example : PackedSieveKernel.primeBits 38358837684 1000000=
    PackedSievePrimitiveMaskMillion.bits := PrimeBaseMaskScout.MainP.original_mask_equality
#print axioms PrimeBaseMaskScout.MainP.original_mask_equality
#print axioms PrimeBaseMaskScout.BaseP.full_P_certificate
end RamanujanPV.PackedSievePrimeBaseIndependentAudit
