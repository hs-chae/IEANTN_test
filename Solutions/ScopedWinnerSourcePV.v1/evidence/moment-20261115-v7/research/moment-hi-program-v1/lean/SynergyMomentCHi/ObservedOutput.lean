/- Actual selected C-output final128bytes, compared to the independently proved
source computation. The observations are not mathematical premises or certificates
replacing execution of the actual C numerical algorithms. -/
import SynergyMomentCHi.CompleteProgram
namespace SynergyMomentCHi.ObservedOutput
open ScopedNumerical SynergyMomentC SynergyHeightC
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
def total : Kind→ProofBox
 | .mass=>⟨2154135236826731182547168213720778134,2154135236826731182574914692470792332⟩
 | .firstMoment=>⟨177084373774472127963244658386711985347,177084373774472127967469350544969916761⟩
def bytes : Kind→List Nat
 | .mass=>[150,69,46,49,222,237,69,60,151,101,144,42,17,223,158,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,140,224,215,178,36,129,168,60,151,101,144,42,17,223,158,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 | .firstMoment=>[195,188,213,77,103,188,136,155,13,42,241,86,182,53,57,133,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,89,97,45,192,137,219,41,214,13,42,241,86,182,53,57,133,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem total_exact (kind : Kind) : FamilyAPI.total kind 768=total kind := by
 cases kind with
 | mass=>exact SourceMomentSumsV1.Data.mass_final
 | firstMoment=>exact SourceMomentSumsV1.Data.first_moment_final
theorem bytes_exact (kind : Kind) :
 bytes kind=EmitUBuffer.bytes (total kind).lo++EmitUBuffer.bytes (total kind).hi := by
 cases kind <;> decide +kernel
theorem source_bytes (kind : Kind) : bytes kind=
 EmitUBuffer.bytes (FamilyAPI.total kind 768).lo++EmitUBuffer.bytes (FamilyAPI.total kind 768).hi :=
 (bytes_exact kind).trans (congrArg
   (fun box : ProofBox=>EmitUBuffer.bytes box.lo++EmitUBuffer.bytes box.hi) (total_exact kind).symm)
#print axioms total_exact
#print axioms bytes_exact
#print axioms source_bytes
end SynergyMomentCHi.ObservedOutput
