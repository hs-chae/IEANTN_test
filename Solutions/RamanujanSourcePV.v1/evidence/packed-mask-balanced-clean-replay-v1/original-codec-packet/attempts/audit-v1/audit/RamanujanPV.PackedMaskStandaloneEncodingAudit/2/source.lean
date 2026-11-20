import RamanujanPV.PackedMaskDataEncoding.W4096DataOnly.ProviderCheck
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for mod in env.header.moduleNames do
    let name := mod.toString
    if name.startsWith "RamanujanPV.PackedMaskDataEncoding.BaselineData" ||
        name.startsWith "RamanujanPV.PackedSievePrimitiveMaskMillion" ||
        name.startsWith "RamanujanPV.PackedSievePrimitiveMillion" then
      throwError "Forbidden baseline data/proof dependency: {name}"
    if name.startsWith "RamanujanPV.PackedMaskDataEncoding" then
      logInfo m!"STANDALONE_ENCODING_IMPORT {name}"
    count := count+1
  logInfo m!"STANDALONE_ENCODING_IMPORT_COUNT {count}"
namespace RamanujanPV.PackedMaskStandaloneEncodingAudit
example : PackedSievePrimitiveBits.primitiveBits 38358837684 1000000=PackedMaskDataEncoding.W4096DataOnly.value :=
  PackedMaskDataEncoding.W4096DataOnly.primitive_program_matches_data
example : PackedSieveKernel.primeBits 38358837684 1000000=PackedMaskDataEncoding.W4096DataOnly.value :=
  PackedMaskDataEncoding.W4096DataOnly.original_program_matches_data
#print axioms PackedMaskDataEncoding.W4096DataOnly.primitive_program_matches_data
#print axioms PackedMaskDataEncoding.W4096DataOnly.original_program_matches_data
end RamanujanPV.PackedMaskStandaloneEncodingAudit
