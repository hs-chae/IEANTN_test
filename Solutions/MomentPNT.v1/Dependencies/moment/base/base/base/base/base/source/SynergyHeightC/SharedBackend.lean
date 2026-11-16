import SynergyHeightC.Definitions
import SynergyC.Generated
import SynergyC.Header
import ScopedC.SourceCallExecute
namespace SynergyHeightC
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem shared_fail : Generated.f_fail=SynergyC.Generated.f_fail := by rfl
theorem shared_addU : Generated.f_addU=SynergyC.Generated.f_addU := by rfl
theorem shared_mulU : Generated.f_mulU=SynergyC.Generated.f_mulU := by rfl
theorem shared_ceilDiv : Generated.f_ceilDiv=SynergyC.Generated.f_ceilDiv := by rfl
theorem shared_rat : Generated.f_rat=SynergyC.Generated.f_rat := by rfl
theorem shared_unit : Generated.f_unit=SynergyC.Generated.f_unit := by rfl
theorem shared_zero : Generated.f_zero=SynergyC.Generated.f_zero := by rfl
theorem shared_add : Generated.f_add=SynergyC.Generated.f_add := by rfl
theorem shared_mul : Generated.f_mul=SynergyC.Generated.f_mul := by rfl
theorem shared_divI : Generated.f_divI=SynergyC.Generated.f_divI := by rfl
theorem shared_divN : Generated.f_divN=SynergyC.Generated.f_divN := by rfl
theorem shared_positiveSub : Generated.f_positiveSub=SynergyC.Generated.f_positiveSub := by rfl
theorem shared_expNeg : Generated.f_expNeg=SynergyC.Generated.f_expNeg := by rfl
theorem shared_atanh2 : Generated.f_atanh2=SynergyC.Generated.f_atanh2 := by rfl
theorem shared_floorCube : Generated.f_floorCube=SynergyC.Generated.f_floorCube := by rfl
theorem shared_cubeRoot : Generated.f_cubeRoot=SynergyC.Generated.f_cubeRoot := by rfl
theorem shared_gaussianCell : Generated.f_gaussianCell=SynergyC.Generated.f_gaussianCell := by rfl
theorem core_header_prefix : Generated.globals.take 3=SynergyC.Header.globals := by rfl
theorem find_fail : ScopedC.SourceCallExecute.find Generated.functions "fail"=some Generated.f_fail := by rfl
theorem find_addU : ScopedC.SourceCallExecute.find Generated.functions "addU"=some Generated.f_addU := by rfl
theorem find_mulU : ScopedC.SourceCallExecute.find Generated.functions "mulU"=some Generated.f_mulU := by rfl
theorem find_ceilDiv : ScopedC.SourceCallExecute.find Generated.functions "ceilDiv"=some Generated.f_ceilDiv := by rfl
theorem find_rat : ScopedC.SourceCallExecute.find Generated.functions "rat"=some Generated.f_rat := by rfl
theorem find_unit : ScopedC.SourceCallExecute.find Generated.functions "unit"=some Generated.f_unit := by rfl
theorem find_zero : ScopedC.SourceCallExecute.find Generated.functions "zero"=some Generated.f_zero := by rfl
theorem find_add : ScopedC.SourceCallExecute.find Generated.functions "add"=some Generated.f_add := by rfl
theorem find_mul : ScopedC.SourceCallExecute.find Generated.functions "mul"=some Generated.f_mul := by rfl
theorem find_divI : ScopedC.SourceCallExecute.find Generated.functions "divI"=some Generated.f_divI := by rfl
theorem find_divN : ScopedC.SourceCallExecute.find Generated.functions "divN"=some Generated.f_divN := by rfl
theorem find_positiveSub : ScopedC.SourceCallExecute.find Generated.functions "positiveSub"=some Generated.f_positiveSub := by rfl
theorem find_expNeg : ScopedC.SourceCallExecute.find Generated.functions "expNeg"=some Generated.f_expNeg := by rfl
theorem find_atanh2 : ScopedC.SourceCallExecute.find Generated.functions "atanh2"=some Generated.f_atanh2 := by rfl
theorem find_logPos : ScopedC.SourceCallExecute.find Generated.functions "logPos"=some Generated.f_logPos := by rfl
theorem find_floorCube : ScopedC.SourceCallExecute.find Generated.functions "floorCube"=some Generated.f_floorCube := by rfl
theorem find_cubeRoot : ScopedC.SourceCallExecute.find Generated.functions "cubeRoot"=some Generated.f_cubeRoot := by rfl
theorem find_gaussianCell : ScopedC.SourceCallExecute.find Generated.functions "gaussianCell"=some Generated.f_gaussianCell := by rfl
theorem find_archived_basis_main : ScopedC.SourceCallExecute.find Generated.functions "archived_basis_main"=some Generated.f_archived_basis_main := by rfl
theorem find_expPositiveRaw : ScopedC.SourceCallExecute.find Generated.functions "expPositiveRaw"=some Generated.f_expPositiveRaw := by rfl
theorem find_expPositive : ScopedC.SourceCallExecute.find Generated.functions "expPositive"=some Generated.f_expPositive := by rfl
theorem find_logTight : ScopedC.SourceCallExecute.find Generated.functions "logTight"=some Generated.f_logTight := by rfl
theorem find_squareI : ScopedC.SourceCallExecute.find Generated.functions "squareI"=some Generated.f_squareI := by rfl
theorem find_inverseI : ScopedC.SourceCallExecute.find Generated.functions "inverseI"=some Generated.f_inverseI := by rfl
theorem find_sqrtInterval : ScopedC.SourceCallExecute.find Generated.functions "sqrtInterval"=some Generated.f_sqrtInterval := by rfl
theorem find_emitU : ScopedC.SourceCallExecute.find Generated.functions "emitU"=some Generated.f_emitU := by rfl
theorem find_emitI : ScopedC.SourceCallExecute.find Generated.functions "emitI"=some Generated.f_emitI := by rfl
theorem find_initializeConstants : ScopedC.SourceCallExecute.find Generated.functions "initializeConstants"=some Generated.f_initializeConstants := by rfl
theorem find_rightRawCap : ScopedC.SourceCallExecute.find Generated.functions "rightRawCap"=some Generated.f_rightRawCap := by rfl
theorem find_leftRawCap : ScopedC.SourceCallExecute.find Generated.functions "leftRawCap"=some Generated.f_leftRawCap := by rfl
theorem find_heightPair : ScopedC.SourceCallExecute.find Generated.functions "heightPair"=some Generated.f_heightPair := by rfl
theorem find_expNegAny : ScopedC.SourceCallExecute.find Generated.functions "expNegAny"=some Generated.f_expNegAny := by rfl
theorem find_paired : ScopedC.SourceCallExecute.find Generated.functions "paired"=some Generated.f_paired := by rfl
theorem find_subExact : ScopedC.SourceCallExecute.find Generated.functions "subExact"=some Generated.f_subExact := by rfl
theorem find_sqrtMatch : ScopedC.SourceCallExecute.find Generated.functions "sqrtMatch"=some Generated.f_sqrtMatch := by rfl
theorem find_initializePointConstants : ScopedC.SourceCallExecute.find Generated.functions "initializePointConstants"=some Generated.f_initializePointConstants := by rfl
theorem find_pointHeight : ScopedC.SourceCallExecute.find Generated.functions "pointHeight"=some Generated.f_pointHeight := by rfl
theorem find_pointEdge : ScopedC.SourceCallExecute.find Generated.functions "pointEdge"=some Generated.f_pointEdge := by rfl
theorem find_main : ScopedC.SourceCallExecute.find Generated.functions "main"=some Generated.f_main := by rfl
#print axioms shared_expNeg
#print axioms core_header_prefix
#print axioms find_initializePointConstants
#print axioms find_pointHeight
end SynergyHeightC
